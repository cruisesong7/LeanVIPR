#!/usr/bin/env python3
"""Download the ``benchmarks/new`` VIPR v1.0 certificates.

The certificates total about 18 GB, so they are not committed. Every file is
listed in ``benchmarks/new/manifest.csv`` with its source URL, SHA-256 and size.
This script fetches each file into ``benchmarks/new/<set>/<instance>.vipr.gz``
and checks it against the manifest.

Manifest ``store`` column:

* ``as-is``: the upstream file is already ``.vipr.gz`` and is saved unchanged.
  ``sha256``/``bytes`` describe that gzip file.
* ``gzip``: the upstream file is a plain ``.vipr``. It is verified, then
  gzip-compressed for the runner. ``sha256``/``bytes`` describe the plain file,
  because gzip output can differ between gzip implementations.

Sets: ``easy`` (56) and ``hard`` (50) come from the scipopt/vipr experiments
(viprcheck/experiments/README.md). ``chvatal`` and ``negative`` are documented
in their folders' SOURCE.md.

Examples::

    python3 benchmarks/download_new.py                    # everything missing
    python3 benchmarks/download_new.py --sets negative chvatal
    python3 benchmarks/download_new.py --only acc-0 bell5
    python3 benchmarks/download_new.py --verify           # rehash existing files
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import shutil
import sys
import time
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHUNK = 1 << 20


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--manifest", type=Path, default=ROOT / "benchmarks/new/manifest.csv")
    p.add_argument("--dest", type=Path, default=ROOT / "benchmarks/new",
                   help="root directory; files go to <dest>/<set>/<instance>.vipr.gz")
    p.add_argument("--sets", nargs="+", help="only these sets (easy hard chvatal negative)")
    p.add_argument("--only", nargs="+", help="only these instance names")
    p.add_argument("--verify", action="store_true",
                   help="hash files that already exist instead of trusting their size")
    p.add_argument("--force", action="store_true", help="download even if present")
    p.add_argument("--retries", type=int, default=3)
    p.add_argument("--list", action="store_true", help="print the selection and exit")
    return p.parse_args()


def sha256_of(path: Path, decompress: bool = False) -> tuple[str, int]:
    h, n = hashlib.sha256(), 0
    opener = gzip.open if decompress else open
    with opener(path, "rb") as f:
        while chunk := f.read(CHUNK):
            h.update(chunk)
            n += len(chunk)
    return h.hexdigest(), n


def is_good(path: Path, row: dict, verify: bool) -> bool:
    if not path.exists():
        return False
    if row["store"] == "as-is" and not verify:
        return path.stat().st_size == int(row["bytes"])
    try:
        digest, size = sha256_of(path, decompress=row["store"] == "gzip")
    except (OSError, EOFError):
        return False
    return digest == row["sha256"] and size == int(row["bytes"])


class _Redirects(urllib.request.HTTPRedirectHandler):
    """Follow 307/308 for GET too (Python < 3.11 does not; zib.de answers 308)."""

    def http_error_308(self, req, fp, code, msg, headers):
        return self.http_error_302(req, fp, code, msg, headers)

    http_error_307 = http_error_308

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if code in (307, 308) and req.get_method() == "GET":
            code = 302
        return super().redirect_request(req, fp, code, msg, headers, newurl)


_OPENER = urllib.request.build_opener(_Redirects)


def fetch(url: str, part: Path, expected: int) -> tuple[str, int]:
    """Stream ``url`` into ``part`` and return (sha256, size)."""
    req = urllib.request.Request(url, headers={"User-Agent": "LeanVIPR-benchmarks/1.0"})
    h, n = hashlib.sha256(), 0
    start = last = time.monotonic()
    with _OPENER.open(req, timeout=60) as resp, part.open("wb") as out:
        while chunk := resp.read(CHUNK):
            out.write(chunk)
            h.update(chunk)
            n += len(chunk)
            now = time.monotonic()
            if sys.stderr.isatty() and now - last > 0.5:
                rate = n / max(now - start, 1e-9) / 1e6
                print(f"\r    {n / 1e6:9.1f} / {expected / 1e6:.1f} MB  {rate:6.1f} MB/s",
                      end="", file=sys.stderr, flush=True)
                last = now
    if sys.stderr.isatty():
        print("\r" + " " * 60 + "\r", end="", file=sys.stderr, flush=True)
    return h.hexdigest(), n


def download(row: dict, target: Path, retries: int) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    part = target.with_name(target.name + ".part")
    for attempt in range(1, retries + 1):
        try:
            digest, size = fetch(row["url"], part, int(row["bytes"]))
            if digest != row["sha256"] or size != int(row["bytes"]):
                raise ValueError(f"checksum mismatch: got {size} bytes sha256 {digest}, "
                                 f"expected {row['bytes']} bytes sha256 {row['sha256']}")
            if row["store"] == "gzip":
                gz = target.with_name(target.name + ".gzpart")
                with part.open("rb") as src, gzip.GzipFile(gz, "wb", mtime=0) as dst:
                    shutil.copyfileobj(src, dst, CHUNK)
                part.unlink()
                gz.replace(target)
            else:
                part.replace(target)
            return
        except Exception as exc:  # network errors, HTTP errors, checksum mismatch
            part.unlink(missing_ok=True)
            if attempt == retries:
                raise
            print(f"    attempt {attempt} failed ({exc}); retrying", flush=True)
            time.sleep(5 * attempt)


def main() -> int:
    args = parse_args()
    with args.manifest.open(newline="") as f:
        rows = list(csv.DictReader(f))
    if args.sets:
        rows = [r for r in rows if r["set"] in args.sets]
    if args.only:
        rows = [r for r in rows if r["instance"] in args.only]
    if not rows:
        raise SystemExit("nothing selected")
    total = sum(int(r["bytes"]) for r in rows)
    print(f"{len(rows)} certificates, {total / 1e9:.2f} GB listed, into {args.dest}")
    if args.list:
        for r in rows:
            print(f"  {r['set']:8s} {r['instance']:28s} {int(r['bytes']) / 1e6:10.1f} MB  {r['url']}")
        return 0

    failed, fetched, present = [], 0, 0
    for i, r in enumerate(rows, 1):
        target = args.dest / r["set"] / f"{r['instance']}.vipr.gz"
        label = f"[{i}/{len(rows)}] {r['set']}/{r['instance']}"
        if not args.force and is_good(target, r, args.verify):
            present += 1
            print(f"{label}: present", flush=True)
            continue
        print(f"{label}: downloading {int(r['bytes']) / 1e6:.1f} MB", flush=True)
        try:
            download(r, target, args.retries)
            fetched += 1
        except Exception as exc:
            failed.append(f"{r['set']}/{r['instance']}: {exc}")
            print(f"    FAILED: {exc}", flush=True)

    print(f"done: {fetched} downloaded, {present} already present, {len(failed)} failed")
    for line in failed:
        print("  " + line)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
