#!/usr/bin/env python3
"""How often does exact SCIP write a range certificate whose only defect is that
rows follow the objective-bound row (no closing `DualBound ... OBJ` row)?

Each model is solved by exact SCIP under default settings and with presolving
off. Every certificate written is checked by LeanVIPR and by upstream viprchk.
A rejected range certificate is then truncated after its last k rows, k = 1, 2,
..., and re-checked; if some truncation is accepted, its only defect is the
trailing rows.

Models: SCIP's own exact-mode test instances, the 26 problems behind
benchmarks/{infeas,range}, and seeded random families.
"""

from __future__ import annotations

import argparse
import csv
import random
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SCIP = Path.home() / "scip-exact/scipoptsuite-10.0.1/build/bin/scip"
SCIP_ZPL = Path("/opt/homebrew/bin/scip")          # 10.0.1 build has ZIMPL=off
SCIP_CHECK = Path.home() / "scip-exact/scipoptsuite-10.0.1/scip/check"
LEAN = REPO / ".lake/build/bin/viprcheck"
VIPRCHK = HERE / "bin/viprchk"

PRESOLVE = {"default": [], "presolve-off": ["set presolving maxrounds 0"]}


# --------------------------------------------------------------------------- #
# models

def fmt(q: Q) -> str:
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def write_mps(path: Path, m: dict) -> None:
    """Free MPS. Every variable gets explicit bounds; MPS defaults differ by reader."""
    out = ["NAME model"]
    if m["sense"] == "max":
        out += ["OBJSENSE", "    MAX"]
    out.append("ROWS")
    out.append(" N obj")
    for i, (sense, _, _) in enumerate(m["cons"]):
        out.append(f" {sense} c{i}")
    out.append("COLUMNS")
    cols: dict[int, list[tuple[str, Q]]] = {j: [] for j in range(len(m["vars"]))}
    for j, a in m["obj"].items():
        cols[j].append(("obj", a))
    for i, (_, coefs, _) in enumerate(m["cons"]):
        for j, a in coefs.items():
            cols[j].append((f"c{i}", a))
    in_int = False
    for j, (vtype, _, _) in enumerate(m["vars"]):
        if (vtype == "I") != in_int:
            out.append("    MARKER 'MARKER' " + ("'INTORG'" if not in_int else "'INTEND'"))
            in_int = not in_int
        entries = cols[j] or [("obj", Q(0))]
        for row, a in entries:
            out.append(f"    x{j} {row} {fmt(a)}")
    if in_int:
        out.append("    MARKER 'MARKER' 'INTEND'")
    out.append("RHS")
    for i, (_, _, rhs) in enumerate(m["cons"]):
        if rhs != 0:
            out.append(f"    RHS c{i} {fmt(rhs)}")
    out.append("BOUNDS")
    for j, (_, lb, ub) in enumerate(m["vars"]):
        if lb is None and ub is None:
            out.append(f" FR BND x{j}")
            continue
        out.append(f" LO BND x{j} {fmt(lb)}" if lb is not None else f" MI BND x{j}")
        out.append(f" UP BND x{j} {fmt(ub)}" if ub is not None else f" PL BND x{j}")
    out.append("ENDATA")
    path.write_text("\n".join(out) + "\n")


def vipr_problem(path: Path) -> dict:
    """The problem section of a VIPR file. VIPR variables are free reals."""
    toks = path.read_text(errors="replace").split()
    pos = 0

    def take() -> str:
        nonlocal pos
        pos += 1
        return toks[pos - 1]

    def coefs() -> dict[int, Q]:
        k = take()
        if k == "OBJ":
            raise ValueError("OBJ shorthand in problem section")
        return {int(take()): Q(take()) for _ in range(int(k))}

    m = {"vars": [], "cons": [], "obj": {}, "sense": "min"}
    while pos < len(toks):
        t = take()
        if t == "VAR":
            n = int(take())
            pos += n
            m["vars"] = [["C", None, None] for _ in range(n)]
        elif t == "INT":
            for _ in range(int(take())):
                m["vars"][int(take())][0] = "I"
        elif t == "OBJ":
            m["sense"] = take()
            m["obj"] = coefs()
        elif t == "CON":
            ncon = int(take())
            take()
            for _ in range(ncon):
                take()
                sense = take()
                rhs = Q(take())
                m["cons"].append((sense, coefs(), rhs))
        elif t == "RTP":
            break
    m["vars"] = [tuple(v) for v in m["vars"]]
    return m


def random_model(rng: random.Random, family: str) -> dict:
    if family == "knap":
        n = rng.randint(3, 9)
        w = [Q(rng.randint(1, 9)) for _ in range(n)]
        cons = [("L", dict(enumerate(w)), Q(rng.randint(1, int(sum(w)))))]
        if rng.random() < 0.5:
            cons.append(("G", {j: Q(1) for j in rng.sample(range(n), rng.randint(1, n))}, Q(1)))
        return {"vars": [("I", Q(0), Q(1))] * n, "cons": cons,
                "obj": {j: Q(rng.randint(1, 9)) for j in range(n)}, "sense": "max"}
    if family == "bigm":
        # k indicators z_i = 1 -> a_i . x <= b_i, written as big-M with the tight M
        nx, k = rng.randint(1, 4), rng.randint(1, 3)
        xs = [(rng.choice("IC"), Q(0), Q(rng.randint(1, 8))) for _ in range(nx)]
        vars_ = xs + [("I", Q(0), Q(1))] * k
        cons = []
        for i in range(k):
            a = {j: Q(rng.randint(1, 4)) for j in rng.sample(range(nx), rng.randint(1, nx))}
            top = sum(c * xs[j][2] for j, c in a.items())
            b = Q(rng.randint(0, int(top)))
            big_m = top - b
            cons.append(("L", {**a, nx + i: big_m}, b + big_m))
        cons.append(("G", {nx + i: Q(1) for i in range(k)}, Q(rng.randint(1, k))))
        obj = {j: Q(-rng.randint(1, 5)) for j in range(nx)}
        obj.update({nx + i: Q(rng.randint(0, 3)) for i in range(k)})
        return {"vars": vars_, "cons": cons, "obj": obj, "sense": "min"}
    # "rand" (feasible by construction) and "rand-any" (may be infeasible)
    n = rng.randint(2, 8)
    vars_ = []
    for _ in range(n):
        vtype = "I" if rng.random() < 0.6 else "C"
        vars_.append((vtype, Q(0), Q(rng.randint(1, 6))))
    point = [Q(rng.randint(0, int(ub))) for _, _, ub in vars_]
    cons = []
    for _ in range(rng.randint(1, 6)):
        a = {j: Q(rng.choice([-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]))
             for j in rng.sample(range(n), rng.randint(1, n))}
        sense = rng.choice("LLGGE")
        act = sum(c * point[j] for j, c in a.items())
        if family == "rand-any":
            rhs = act + rng.randint(-4, 4)
        else:
            slack = rng.randint(0, 4)
            rhs = act + (slack if sense == "L" else -slack if sense == "G" else 0)
        cons.append((sense, a, rhs))
    obj = {j: Q(rng.randint(-5, 5)) for j in range(n)}
    return {"vars": vars_, "cons": cons, "obj": obj, "sense": rng.choice(["min", "max"])}


# --------------------------------------------------------------------------- #
# running

def run(cmd: list[str], timeout: float, cwd: Path | None = None) -> str:
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, errors="replace",
                           cwd=cwd)
        return p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return "__TIMEOUT__"


def lean_verdict(path: Path) -> str:
    out = run([str(LEAN), str(path)], 300)
    if out == "__TIMEOUT__":
        return "timeout"
    if "NATIVE ACCEPT" in out:
        return "accept"
    if "parse error" in out:
        return "parse-error"
    return "reject" if "NATIVE REJECT" in out else "error"


VIPRCOMP = HERE / "bin/viprcomp"


def viprchk_verdict(path: Path) -> str:
    out = run([str(VIPRCHK), str(path)], 300)
    if out == "__TIMEOUT__":
        return "timeout"
    if "Successfully verified" in out:
        return "accept"
    if "Failed to derive lower bound" in out or "Failed to derive upper bound" in out:
        return "reject-bound"
    return "reject" if "Verification failed" in out else "error"


def upstream_verdict(path: Path) -> str:
    """The upstream pipeline: viprcomp first if the certificate has weak or incomplete
    derivations (viprchk is VIPR 1.0 only), then viprchk."""
    text = path.read_text(errors="replace")
    if "weak" not in text and "incomplete" not in text:
        return viprchk_verdict(path)
    out = run([str(VIPRCOMP), "--verbosity=0", "--debugmode=off", "--soplex=on", path.name],
              300, cwd=path.parent)
    done = path.with_name(path.stem + "_complete.vipr")
    if out == "__TIMEOUT__":
        return "comp-timeout"
    if "Failed to complete" in out or not done.exists():
        done.unlink(missing_ok=True)
        return "comp-fail"
    verdict = viprchk_verdict(done)
    done.unlink(missing_ok=True)
    return "comp+" + verdict


def lean_diagnosis(path: Path) -> str:
    """Where LeanVIPR's check fails: `final` if every step passes, else the reason
    kind of the first invalid step."""
    out = run([str(LEAN), "--debug-first-invalid", str(path)], 300)
    if "all derivation steps pass" in out:
        return "final"
    m = re.search(r"^reason: (\w+)", out, re.M)
    if m:
        return "step-" + m.group(1) + ("-weak" if "weak base references" in out else "")
    return "undiagnosed"


def split_der(text: str) -> tuple[list[str], list[str]] | None:
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("DER "):
            n = int(line.split()[1])
            rows = lines[i + 1:i + 1 + n]
            return (lines[:i], rows) if len(rows) == n else None
    return None


def truncation_accepts(path: Path, work: Path, max_drop: int = 40) -> int:
    """Smallest k such that dropping the last k DER rows makes LeanVIPR accept, else 0.
    Final-use hints are reset to -1, which always conforms."""
    parts = split_der(path.read_text(errors="replace"))
    if parts is None:
        return 0
    head, rows = parts

    def reset_hint(row: str) -> str:
        cut = row.rfind("}")
        tail = row[cut + 1:].split()
        return row[:cut + 1] + " " + " ".join(["-1"] + tail[1:]) if tail else row

    for k in range(1, min(max_drop, len(rows)) + 1):
        kept = [reset_hint(r) for r in rows[:len(rows) - k]]
        trial = work / (path.stem + f".drop{k}.vipr")
        trial.write_text("\n".join(head + [f"DER {len(kept)}"] + kept) + "\n")
        verdict = lean_verdict(trial)
        trial.unlink()
        if verdict == "accept":
            return k
    return 0


def job(spec: dict) -> dict:
    name, mode, work = spec["name"], spec["mode"], spec["work"]
    cert = work / f"{name}.{mode}.vipr"
    for p in (cert, Path(str(cert) + "_ori")):
        p.unlink(missing_ok=True)
    cmds = ["set exact enable TRUE", "set limits time 60"]
    if spec.get("settings"):
        cmds.append(f"set load {spec['settings']}")
    cmds += PRESOLVE[mode] + [f"set certificate filename {cert}", f"read {spec['model']}",
                              "optimize", "quit"]
    args = [str(spec.get("scip") or SCIP)]
    for c in cmds:
        args += ["-c", c]
    log = run(args, 180)
    status = "timeout" if log == "__TIMEOUT__" else (
        re.search(r"SCIP Status\s*:\s*(.*)", log).group(1).strip()
        if re.search(r"SCIP Status\s*:\s*(.*)", log) else "no-status")
    if "ERROR" in log and "problem is solved" not in status:
        status = "scip-error: " + (re.search(r"ERROR: (.*)", log).group(1)[:60]
                                   if re.search(r"ERROR: (.*)", log) else "?")
    row = {"source": spec["source"], "name": name, "mode": mode, "scip_status": status,
           "cert": "no", "rtp": "", "rows": "", "dualbound_rows": "", "last_row": "",
           "lean": "", "upstream": "", "lean_diag": "", "trailing_drop": "", "class": ""}
    ori = Path(str(cert) + "_ori")
    row["ori_rtp"] = next((l.strip() for l in ori.read_text(errors="replace").splitlines()
                           if l.startswith("RTP")), "") if ori.exists() else ""
    if not cert.exists() or cert.stat().st_size == 0:
        row["class"] = "no-cert" if "solved" in status else "solver-" + status.split(" ")[0]
        return row
    text = cert.read_text(errors="replace")
    row["cert"] = "yes"
    row["rtp"] = next((l.strip() for l in text.splitlines() if l.startswith("RTP")), "")
    parts = split_der(text)
    if parts:
        row["rows"] = str(len(parts[1]))
        row["dualbound_rows"] = str(sum(r.startswith("DualBound") for r in parts[1]))
        row["last_row"] = re.sub(r"_\d+$", "", parts[1][-1].split()[0]) if parts[1] else ""
    row["lean"] = lean_verdict(cert)
    row["upstream"] = upstream_verdict(cert)
    row["lean_diag"] = lean_diagnosis(cert) if row["lean"] != "accept" else ""
    if row["lean"] == "accept" and row["upstream"].endswith("accept"):
        row["class"] = "both-accept"
    else:
        row["class"] = f"lean:{row['lean']}/{row['lean_diag'] or '-'} | upstream:{row['upstream']}"
        if row["lean_diag"] == "final" and row["rtp"].startswith("RTP range"):
            row["trailing_drop"] = str(truncation_accepts(cert, work))
    if row["class"] == "both-accept":
        cert.unlink()
        ori.unlink(missing_ok=True)
    return row


def main() -> int:
    global SCIP
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=200, help="models per random family")
    ap.add_argument("--seed", type=int, default=20261119)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--scip", type=Path, default=SCIP)
    ap.add_argument("--label", default="10.0.1")
    args = ap.parse_args()

    SCIP = args.scip
    args.out = HERE / f"results-{args.label}.csv"
    work = HERE / f"work-{args.label}"
    models = HERE / "models"
    work.mkdir(exist_ok=True)
    models.mkdir(exist_ok=True)
    specs = []

    # 0. known-positive control: the original reproducer must come out trailing-rows
    for mode in PRESOLVE:
        specs.append({"source": "control", "name": "ind_bigM", "mode": mode,
                      "model": HERE.parent / "ind_bigM.lp", "work": work})

    # 1. SCIP's own exact-mode test instances, with their own settings files
    mipex = {"egout.cip": None, "flugpl_rational.mps": None, "Side-coef.cip": None,
             "Side-coeftest.lp": None, "misc03p1.zpl": None, "rgn.zpl": None,
             "stein27.zpl": None}
    for inst, scip in mipex.items():
        for setting in ("exact-default", "exact-exactlp", "exact-projshift"):
            for mode in PRESOLVE:
                spec = {"source": "scip-mipex", "name": f"{inst}.{setting}", "mode": mode,
                        "model": SCIP_CHECK / "instances/MIPEX" / inst, "work": work,
                        "settings": SCIP_CHECK / "coverage/settings" / f"{setting}.set"}
                if scip:
                    spec["scip"] = scip
                specs.append(spec)

    # 2. the problems behind the checked-in certificates
    for vipr in sorted((REPO / "benchmarks").glob("[ir][na][fn]*/*.vipr")):
        mps = models / f"bench-{vipr.stem}.mps"
        write_mps(mps, vipr_problem(vipr))
        for mode in PRESOLVE:
            specs.append({"source": "bench-" + vipr.parent.name, "name": vipr.stem,
                          "mode": mode, "model": mps, "work": work})

    # 3. seeded random families
    rng = random.Random(args.seed)
    for family in ("rand", "rand-any", "bigm", "knap"):
        for i in range(args.random):
            mps = models / f"{family}-{i:04d}.mps"
            write_mps(mps, random_model(rng, family))
            for mode in PRESOLVE:
                specs.append({"source": family, "name": f"{family}-{i:04d}", "mode": mode,
                              "model": mps, "work": work})

    print(f"{len(specs)} runs", file=sys.stderr)
    with ThreadPoolExecutor(args.jobs) as pool:
        rows = list(pool.map(job, specs))
    with args.out.open("w", newline="") as handle:
        w = csv.DictWriter(handle, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    print(f"wrote {args.out}")
    summary: dict[tuple[str, str], dict[str, int]] = {}
    for r in rows:
        key = (r["source"] if not r["source"].startswith("bench") else "bench", r["mode"])
        summary.setdefault(key, {})
        summary[key][r["class"]] = summary[key].get(r["class"], 0) + 1
    for (src, mode), counts in sorted(summary.items()):
        print(f"{src:12s} {mode:13s} " + "  ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    return 0


if __name__ == "__main__":
    sys.exit(main())
