#!/usr/bin/env python3
"""Compare the Lean checker and the reference C++ viprchk on benchmarks/new.

Every certificate in the corpus is a gzipped, already-complete VIPR v1.0 file.
For each certificate, in order of increasing compressed size, the runner

1. decompresses it to a scratch directory (untimed) and reads its header,
2. runs ``viprchk`` (C++) on the plain file,
3. runs ``viprcheck --native-mode full`` (Lean) on the same file,
4. runs ``viprcheck --native-mode slice`` for ``RTP infeas`` certificates,
5. deletes the plain file.

All runs are strictly sequential. Each run is wrapped in ``/usr/bin/time -l -p``
(macOS rusage: max RSS, peak footprint, instructions, cycles, ...) and guarded by
a wall-clock timeout and a resident-memory watchdog. One CSV row is appended and
flushed per run, so an interrupted run can be resumed with ``--resume``.
"""

from __future__ import annotations

import argparse
import csv
import ctypes
import datetime as dt
import gzip
import hashlib
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent

LEAN_REPORT_RE = re.compile(
    r"vars (?P<vars>\d+)\s+int (?P<int_vars>\d+)\s+"
    r"con (?P<constraints>\d+)\s+steps (?P<steps>\d+)"
)
LEAN_RTP_RE = re.compile(r"VER (?P<ver>\S+)\s+RTP (?P<rtp>\S+)")
LEAN_REASONS_RE = re.compile(
    r"asm×(?P<asm>\d+)\s+lin×(?P<lin>\d+)\s+rnd×(?P<rnd>\d+)\s+"
    r"uns×(?P<uns>\d+)\s+sol×(?P<sol>\d+)"
)
LEAN_SLICE_RE = re.compile(
    r"slice: (?P<constraints>\d+) → (?P<sliced_constraints>\d+) constraints,\s+"
    r"(?P<steps>\d+) → (?P<sliced_steps>\d+) steps"
)
CPP_CPU_RE = re.compile(r"Completed in (?P<cpu>[0-9.eE+-]+) seconds \(CPU\)")
CPP_TERMINATED_RE = re.compile(r"Terminated after (?P<n>\d+) derivations")
CPP_NDER_RE = re.compile(r"numberOfDerivations = (?P<n>\d+)")

# Fields of macOS `/usr/bin/time -l` that are reported per run.
RUSAGE_FIELDS = {
    "maximum resident set size": "max_rss_bytes",
    "peak memory footprint": "peak_footprint_bytes",
    "page reclaims": "page_reclaims",
    "page faults": "page_faults",
    "swaps": "swaps",
    "block input operations": "block_in",
    "block output operations": "block_out",
    "voluntary context switches": "vol_ctx_switches",
    "involuntary context switches": "invol_ctx_switches",
    "instructions retired": "instructions",
    "cycles elapsed": "cycles",
}

COMMON_HEAD = [
    # identity
    "instance", "set", "tool", "mode",
    # outcome
    "status", "returncode", "verdict",
    # timing
    "wall_s", "time_real_s", "user_s", "sys_s", "cpu_s",
    # resources
    *RUSAGE_FIELDS.values(), "watchdog_peak_rss_bytes", "watchdog_peak_footprint_bytes",
    # certificate (from the file itself)
    "gz_bytes", "bytes", "lines", "gz_sha256",
    "ver", "rtp", "rtp_lower", "rtp_upper", "obj_sense",
    "hdr_vars", "hdr_int_vars", "hdr_constraints", "hdr_bound_constraints",
    "hdr_sol", "hdr_steps",
]
COMMON_TAIL = [
    "throughput_mb_s", "timeout_s", "mem_limit_bytes", "footprint_limit_bytes",
    "decompress_s",
    "started_at", "log",
]
LEAN_FIELDS = [
    "lean_vars", "lean_int_vars", "lean_constraints", "lean_steps",
    "asm", "lin", "rnd", "uns", "sol",
    "checked_constraints", "checked_steps",
]
CPP_FIELDS = ["cpp_internal_cpu_s", "cpp_derivations_used"]

# One CSV per method: <prefix>_<method>.csv
METHODS = {
    ("cpp", "check"): ("cpp", COMMON_HEAD + CPP_FIELDS + COMMON_TAIL),
    ("lean", "full"): ("lean_full", COMMON_HEAD + LEAN_FIELDS + COMMON_TAIL),
    ("lean", "slice"): ("lean_slice", COMMON_HEAD + LEAN_FIELDS + COMMON_TAIL),
}


def method_path(prefix: Path, tool: str, mode: str) -> Path:
    return prefix.parent / f"{prefix.name}_{METHODS[(tool, mode)][0]}.csv"

FINAL_STATUSES = {"pass", "reject", "timeout", "memout", "crash", "error"}
ABNORMAL = "time: command terminated abnormally"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--lean", type=Path, default=ROOT / ".lake/build/bin/viprcheck")
    p.add_argument("--cpp", type=Path, default=ROOT / "viprcheck/code/build/viprchk")
    p.add_argument("--root", type=Path, default=ROOT / "benchmarks/new")
    p.add_argument("--sets", nargs="+", default=["easy", "hard"])
    p.add_argument("--only", nargs="+", help="restrict to these instance names")
    p.add_argument("--output-prefix", type=Path, default=ROOT / "benchmarks/results/new",
                   help="writes <prefix>_cpp.csv, <prefix>_lean_full.csv, "
                        "<prefix>_lean_slice.csv")
    p.add_argument("--env-output", type=Path,
                   default=ROOT / "benchmarks/results/new_env.csv")
    p.add_argument("--logs", type=Path, default=ROOT / "benchmarks/results/new_logs")
    p.add_argument("--workdir", type=Path, required=True,
                   help="scratch directory for decompressed certificates")
    p.add_argument("--timeout", type=float, default=3600.0,
                   help="wall-clock limit per run in seconds")
    p.add_argument("--mem-limit-gb", type=float, default=18.0,
                   help="kill a run whose resident set exceeds this many GiB")
    p.add_argument("--footprint-limit-gb", type=float, default=32.0,
                   help="kill a run whose macOS phys_footprint (resident + "
                        "compressed + swapped) exceeds this many GiB")
    p.add_argument("--tools", nargs="+", default=["cpp", "lean"],
                   choices=["cpp", "lean"])
    p.add_argument("--resume", action="store_true",
                   help="skip runs that already have a final row in --output")
    p.add_argument("--slice-all", action="store_true",
                   help="also run slice mode on non-infeas certificates (Lean falls back "
                        "to the full check there)")
    p.add_argument("--lean-tasks", type=int, default=1,
                   help="VIPRCHECK_TASKS for the Lean checker. Defaults to 1 so that the "
                        "table compares like with like against sequential viprchk; set it "
                        "to the core count to measure the parallel replay, and then "
                        "compare against viprchk_parallel rather than viprchk.")
    p.add_argument("--no-warmup", action="store_true")
    p.add_argument("--keep", action="store_true", help="keep decompressed files")
    p.add_argument("--stop-file", type=Path,
                   default=ROOT / "benchmarks/results/new_STOP",
                   help="if this file exists, stop cleanly before the next run")
    return p.parse_args()


# --------------------------------------------------------------------------- #
# certificate preparation


def decompress(src: Path, dst: Path) -> Tuple[float, str]:
    """Decompress `src` to `dst`; return (seconds, sha256 of the gz bytes)."""
    h = hashlib.sha256()
    start = time.perf_counter()
    with src.open("rb") as raw:
        gz_proc = subprocess.Popen(["gzip", "-dc"], stdin=subprocess.PIPE,
                                   stdout=dst.open("wb"))
        assert gz_proc.stdin is not None
        while True:
            chunk = raw.read(1 << 22)
            if not chunk:
                break
            h.update(chunk)
            gz_proc.stdin.write(chunk)
        gz_proc.stdin.close()
        if gz_proc.wait() != 0:
            raise RuntimeError(f"gzip failed on {src}")
    return time.perf_counter() - start, h.hexdigest()


def read_header(path: Path) -> Dict[str, str]:
    """Section header counts of a VIPR file, scanning only up to `DER`."""
    info: Dict[str, str] = {}
    out = subprocess.run(
        ["grep", "-m", "8", "-E", r"^(VER|VAR|INT|OBJ|CON|RTP|SOL|DER)\b", str(path)],
        capture_output=True, text=True, check=False).stdout
    for line in out.splitlines():
        parts = line.split()
        key = parts[0]
        if key == "VER":
            info["ver"] = parts[1]
        elif key == "VAR":
            info["hdr_vars"] = parts[1]
        elif key == "INT":
            info["hdr_int_vars"] = parts[1]
        elif key == "OBJ":
            info["obj_sense"] = parts[1]
        elif key == "CON":
            info["hdr_constraints"] = parts[1]
            info["hdr_bound_constraints"] = parts[2] if len(parts) > 2 else ""
        elif key == "RTP":
            info["rtp"] = parts[1]
            if parts[1] == "range" and len(parts) >= 4:
                info["rtp_lower"], info["rtp_upper"] = parts[2], parts[3]
        elif key == "SOL":
            info["hdr_sol"] = parts[1]
        elif key == "DER":
            info["hdr_steps"] = parts[1]
    wc = subprocess.run(["wc", "-l", str(path)], capture_output=True, text=True)
    info["lines"] = wc.stdout.split()[0]
    return info


# --------------------------------------------------------------------------- #
# measurement


_LIBSYSTEM = ctypes.CDLL("/usr/lib/libSystem.B.dylib", use_errno=True)
_LIBSYSTEM.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]


def phys_footprint_bytes(pid: int) -> int:
    """macOS phys_footprint of `pid` (resident + compressed + swapped), or 0.

    Uses proc_pid_rusage(RUSAGE_INFO_V2). After the 16-byte UUID the struct is a
    sequence of uint64s, of which ri_phys_footprint is the eighth.
    """
    buf = (ctypes.c_uint64 * 64)()
    if _LIBSYSTEM.proc_pid_rusage(pid, 2, ctypes.byref(buf)) != 0:
        return 0
    return int(buf[2 + 7])


def tree_memory(root_pid: int) -> Tuple[int, int]:
    """(RSS, phys_footprint) summed over `root_pid` and all of its descendants."""
    out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,rss="],
                         capture_output=True, text=True).stdout
    children: Dict[int, List[int]] = {}
    rss: Dict[int, int] = {}
    for line in out.splitlines():
        try:
            pid, ppid, kb = (int(x) for x in line.split())
        except ValueError:
            continue
        children.setdefault(ppid, []).append(pid)
        rss[pid] = kb * 1024
    total, footprint, stack = 0, 0, [root_pid]
    while stack:
        pid = stack.pop()
        total += rss.get(pid, 0)
        footprint += phys_footprint_bytes(pid)
        stack.extend(children.get(pid, []))
    return total, footprint


def parse_rusage(path: Path) -> Dict[str, str]:
    values: Dict[str, str] = {}
    if not path.exists():
        return values
    for line in path.read_text().splitlines():
        line = line.strip()
        for key in ("real", "user", "sys"):
            if line.startswith(key + " "):
                values[{"real": "time_real_s", "user": "user_s", "sys": "sys_s"}[key]] = \
                    line.split()[1]
        m = re.match(r"(\d+)\s+(.*)$", line)
        if m and m.group(2) in RUSAGE_FIELDS:
            values[RUSAGE_FIELDS[m.group(2)]] = m.group(1)
    return values


def measure(command: List[str], log: Path, timeout: float,
            mem_limit: int, footprint_limit: int,
            env: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    """Run `command` under /usr/bin/time with timeout and memory watchdog."""
    time_path = log.with_suffix(".time")
    time_path.unlink(missing_ok=True)
    full = ["/usr/bin/time", "-l", "-p", "-o", str(time_path), *command]
    child_env = None
    if env:
        child_env = dict(os.environ)
        child_env.update(env)
    with log.open("w") as out:
        out.write("$ " + " ".join(command) + "\n")
        if env:
            out.write("# env " + " ".join(f"{k}={v}" for k, v in env.items()) + "\n")
        out.flush()
        start = time.perf_counter()
        proc = subprocess.Popen(full, stdout=out, stderr=subprocess.STDOUT,
                                start_new_session=True, env=child_env)
        peak, peak_fp, killed = 0, 0, ""
        while True:
            try:
                proc.wait(timeout=0.5)
                break
            except subprocess.TimeoutExpired:
                pass
            rss, fp = tree_memory(proc.pid)
            peak, peak_fp = max(peak, rss), max(peak_fp, fp)
            elapsed = time.perf_counter() - start
            if elapsed > timeout:
                killed = "timeout"
            elif rss > mem_limit or fp > footprint_limit:
                killed = "memout"
            if killed:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                break
        wall = time.perf_counter() - start
    result = parse_rusage(time_path)
    time_path.unlink(missing_ok=True)
    result.update({
        "wall_s": f"{wall:.3f}",
        "returncode": str(proc.returncode),
        "watchdog_peak_rss_bytes": str(peak),
        "watchdog_peak_footprint_bytes": str(peak_fp),
        "killed": killed,
    })
    if "user_s" in result and "sys_s" in result:
        result["cpu_s"] = f"{float(result['user_s']) + float(result['sys_s']):.2f}"
    return result


def run_cpp(cpp: Path, cert: Path, log: Path, args: argparse.Namespace,
            mem_limit: int) -> Dict[str, str]:
    r = measure([str(cpp), str(cert)], log, args.timeout, mem_limit,
                args.footprint_limit)
    text = log.read_text(errors="replace")
    row: Dict[str, str] = {k: v for k, v in r.items() if k != "killed"}
    if r["killed"]:
        row["status"] = r["killed"]
    elif r["returncode"] == "0":
        row["status"] = "pass"
    elif ABNORMAL in text:
        row["status"] = "crash"
    else:
        row["status"] = "reject"
    m = CPP_CPU_RE.search(text)
    row["cpp_internal_cpu_s"] = m.group("cpu") if m else ""
    m = CPP_TERMINATED_RE.search(text)
    if m:
        row["cpp_derivations_used"] = m.group("n")
    else:
        m = CPP_NDER_RE.search(text)
        row["cpp_derivations_used"] = m.group("n") if (m and row["status"] == "pass") else ""
    verdict = [l for l in text.splitlines()
               if l.startswith(("Successfully verified", "Verification failed",
                                "Failed", "Comment or VER", "time: "))]
    row["verdict"] = verdict[-1][:200] if verdict else ""
    return row


def run_lean(lean: Path, cert: Path, mode: str, log: Path,
             args: argparse.Namespace, mem_limit: int) -> Dict[str, str]:
    r = measure([str(lean), "--native-mode", mode, str(cert)], log, args.timeout,
                mem_limit, args.footprint_limit,
                env={"VIPRCHECK_TASKS": str(args.lean_tasks)})
    text = log.read_text(errors="replace")
    row: Dict[str, str] = {k: v for k, v in r.items() if k != "killed"}
    if r["killed"]:
        row["status"] = r["killed"]
    elif r["returncode"] == "0" and "NATIVE ACCEPT" in text:
        row["status"] = "pass"
    elif "NATIVE REJECT" in text or "parse error" in text:
        row["status"] = "reject"
    elif ABNORMAL in text:
        row["status"] = "crash"
    else:
        row["status"] = "error"
    if (m := LEAN_REPORT_RE.search(text)):
        row.update(lean_vars=m["vars"], lean_int_vars=m["int_vars"],
                   lean_constraints=m["constraints"], lean_steps=m["steps"])
    if (m := LEAN_REASONS_RE.search(text)):
        row.update(asm=m["asm"], lin=m["lin"], rnd=m["rnd"], uns=m["uns"], sol=m["sol"])
    if (m := LEAN_SLICE_RE.search(text)):
        row.update(checked_constraints=m["sliced_constraints"],
                   checked_steps=m["sliced_steps"])
    elif "lean_steps" in row:
        row.update(checked_constraints=row["lean_constraints"],
                   checked_steps=row["lean_steps"])
    verdict = [l for l in text.splitlines()
               if l.startswith(("NATIVE ACCEPT", "NATIVE REJECT", "parse error", "INTERNAL PANIC",
                                "uncaught exception", "time: "))]
    row["verdict"] = verdict[-1][:200] if verdict else ""
    return row


# --------------------------------------------------------------------------- #
# bookkeeping


def capture(cmd: List[str], cwd: Optional[Path] = None) -> str:
    try:
        return subprocess.run(cmd, capture_output=True, text=True, cwd=cwd,
                              check=False).stdout.strip()
    except OSError:
        return ""


def write_env(path: Path, args: argparse.Namespace) -> None:
    sysctl = lambda key: capture(["sysctl", "-n", key])
    env = {
        "date": dt.datetime.now().isoformat(timespec="seconds"),
        "host_cpu": sysctl("machdep.cpu.brand_string"),
        "host_ncpu": sysctl("hw.ncpu"),
        "host_perf_cores": sysctl("hw.perflevel0.physicalcpu"),
        "host_mem_bytes": sysctl("hw.memsize"),
        "os": f"{platform.system()} {platform.mac_ver()[0]} ({platform.release()})",
        "python": platform.python_version(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lean_version": capture(["lean", "--version"], cwd=ROOT),
        "leanvipr_commit": capture(["git", "rev-parse", "HEAD"], cwd=ROOT),
        "leanvipr_dirty": capture(["git", "status", "--porcelain", "--", "LeanVIPR",
                                   "LeanVIPRMain.lean"], cwd=ROOT) or "clean",
        "lean_binary": str(args.lean),
        "lean_binary_sha256": capture(["shasum", "-a", "256", str(args.lean)]).split(" ")[0],
        "viprchk_commit": capture(["git", "rev-parse", "HEAD"], cwd=args.cpp.parent.parent),
        "viprchk_binary": str(args.cpp),
        "viprchk_build": "CMake Release (-O3 -DNDEBUG), target viprchk, VIPRCOMP=OFF",
        "cxx_compiler": capture(["c++", "--version"]).splitlines()[0],
        "gmp": capture(["brew", "list", "--versions", "gmp"]),
        "timeout_s": str(args.timeout),
        "mem_limit_gib": str(args.mem_limit_gb),
        "footprint_limit_gib": str(args.footprint_limit_gb),
        "watchdog": "kill if tree RSS > mem_limit or tree phys_footprint > footprint_limit (footprint check added after vpm1; rows before it used RSS only)",
        "corpus": str(args.root),
        "sets": " ".join(args.sets),
        "lean_modes": ("full (all); slice (all; for non-infeas RTP viprcheck falls back to the full check, LeanVIPRMain.lean:300)"
                       if args.slice_all else
                       "full (all); slice (RTP infeas only, as in run_compiled.py)"),
        "cpp_mode": "viprchk on the complete certificate (no viprcomp; no lin weak present)",
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        w = csv.writer(handle)
        w.writerow(["key", "value"])
        w.writerows(env.items())


def load_done(path: Path) -> Dict[Tuple[str, str, str, str], str]:
    """Map each finished (instance, set, tool, mode) to the certificate's RTP."""
    done: Dict[Tuple[str, str, str, str], str] = {}
    if path.exists():
        with path.open() as handle:
            for row in csv.DictReader(handle):
                if row.get("status") in FINAL_STATUSES:
                    done[(row["instance"], row["set"], row["tool"], row["mode"])] = row["rtp"]
    return done


def main() -> int:
    args = parse_args()
    args.lean, args.cpp = args.lean.resolve(), args.cpp.resolve()
    for exe in (args.lean, args.cpp):
        if not exe.exists():
            raise SystemExit(f"missing executable {exe}")
    mem_limit = int(args.mem_limit_gb * (1 << 30))
    args.footprint_limit = int(args.footprint_limit_gb * (1 << 30))
    args.workdir.mkdir(parents=True, exist_ok=True)
    args.logs.mkdir(parents=True, exist_ok=True)

    certs = [p for s in args.sets for p in (args.root / s).glob("*.vipr.gz")]
    if args.only:
        certs = [p for p in certs if p.name[: -len(".vipr.gz")] in args.only]
    certs.sort(key=lambda p: (p.stat().st_size, p.name))
    if not certs:
        raise SystemExit(f"no certificates below {args.root}")

    paths = {key: method_path(args.output_prefix, *key) for key in METHODS}
    done: Dict[Tuple[str, str, str, str], str] = {}
    if args.resume:
        for path in paths.values():
            done.update(load_done(path))
    else:
        existing = [str(path) for path in paths.values() if path.exists()]
        if existing:
            raise SystemExit("refusing to overwrite " + ", ".join(existing)
                             + " (pass --resume to append)")
    write_env(args.env_output, args)

    if not args.no_warmup:
        warm_src = certs[0]
        warm = args.workdir / "warmup.vipr"
        decompress(warm_src, warm)
        for cmd in ([str(args.cpp), str(warm)],
                    [str(args.lean), "--native-mode", "full", str(warm)]):
            subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        warm.unlink()

    # One CSV per method, opened lazily, appended to on resume.
    handles: Dict[Tuple[str, str], object] = {}
    writers: Dict[Tuple[str, str], csv.DictWriter] = {}

    def writer_for(key: Tuple[str, str]) -> Tuple[csv.DictWriter, object]:
        if key not in writers:
            path = paths[key]
            fresh = not path.exists() or path.stat().st_size == 0
            path.parent.mkdir(parents=True, exist_ok=True)
            handle = path.open("a", newline="")
            writer = csv.DictWriter(handle, fieldnames=METHODS[key][1],
                                    extrasaction="ignore")
            if fresh:
                writer.writeheader()
            handles[key], writers[key] = handle, writer
        return writers[key], handles[key]

    counts: Dict[str, int] = {}
    for idx, src in enumerate(certs, 1):
        name, cset = src.name[: -len(".vipr.gz")], src.parent.name
        planned = []
        if "cpp" in args.tools:
            planned.append(("cpp", "check"))
        if "lean" in args.tools:
            planned.append(("lean", "full"))
            planned.append(("lean", "slice"))  # dropped below for range certificates
        known_rtp = {done[k] for k in done if k[0] == name and k[1] == cset}
        todo = [(t, m) for t, m in planned if (name, cset, t, m) not in done
                and not (m == "slice" and not args.slice_all
                         and known_rtp and "infeas" not in known_rtp)]
        if not todo:
            print(f"[{idx}/{len(certs)}] {cset}/{name}: done, skipping", flush=True)
            continue

        plain = args.workdir / f"{name}.vipr"
        print(f"[{idx}/{len(certs)}] {cset}/{name}: decompressing "
              f"{src.stat().st_size / 1e6:.1f} MB gz", flush=True)
        dsec, sha = decompress(src, plain)
        hdr = read_header(plain)
        base = {
            "instance": name, "set": cset,
            "gz_bytes": str(src.stat().st_size), "bytes": str(plain.stat().st_size),
            "gz_sha256": sha, "decompress_s": f"{dsec:.2f}",
            "timeout_s": str(args.timeout), "mem_limit_bytes": str(mem_limit),
            "footprint_limit_bytes": str(args.footprint_limit),
            **hdr,
        }
        print(f"    {int(base['bytes']) / 1e6:.1f} MB plain, RTP {hdr.get('rtp')}, "
              f"{hdr.get('hdr_steps')} steps", flush=True)

        for tool, mode in planned:
            if args.stop_file and args.stop_file.exists():
                break
            if mode == "slice" and not args.slice_all and hdr.get("rtp") != "infeas":
                continue
            if (name, cset, tool, mode) in done:
                continue
            log = args.logs / f"{cset}__{name}__{tool}_{mode}.log"
            started = dt.datetime.now().isoformat(timespec="seconds")
            print(f"    {tool:4s} {mode:5s} ... ", end="", flush=True)
            if tool == "cpp":
                row = run_cpp(args.cpp, plain, log, args, mem_limit)
            else:
                row = run_lean(args.lean, plain, mode, log, args, mem_limit)
            row.update(base)
            row.update(tool=tool, mode=mode, started_at=started,
                       log=str(log.relative_to(ROOT)) if log.is_relative_to(ROOT)
                       else str(log))
            if row["status"] == "pass" and float(row["wall_s"]) > 0:
                row["throughput_mb_s"] = f"{int(base['bytes']) / 1e6 / float(row['wall_s']):.2f}"
            writer, handle = writer_for((tool, mode))
            writer.writerow(row)
            handle.flush()
            counts[f"{tool}_{mode}_{row['status']}"] = \
                counts.get(f"{tool}_{mode}_{row['status']}", 0) + 1
            print(f"{row['status']:7s} wall {row['wall_s']}s  "
                  f"rss {int(row.get('max_rss_bytes') or row['watchdog_peak_rss_bytes']) / 2**20:.0f} MiB",
                  flush=True)

        if not args.keep:
            plain.unlink(missing_ok=True)
        if args.stop_file and args.stop_file.exists():
            print(f"stop file {args.stop_file} found; stopping", flush=True)
            break

    for handle in handles.values():
        handle.close()
    for key in writers:
        print(f"wrote {paths[key]}")
    for key in sorted(counts):
        print(f"  {key}: {counts[key]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
