# LeanVIPR (`viprcheck`)

LeanVIPR is a formally verified Lean 4 checker for **VIPR v1.0 infeasibility
and objective-range certificates**, using exact rational arithmetic.

The solver (exact SCIP) is **untrusted**. `viprcheck` re-reads the certificate,
emits its parsed AST as Lean data, and asks Lean's kernel to prove
the relevant Boolean acceptance theorem by reduction. `RTP infeas` uses the
refutation checker; `RTP range` additionally checks every `SOL` vector, `{ sol }`
steps, the primal witness bound, and the final closed dual-bound row. It prints
`ACCEPT` only after deriving `Vipr.ClaimValid cert`.

## Setup

Install [`elan`](https://github.com/leanprover/elan), then build from this
directory. Lean 4.35.0 and Mathlib v4.35.0 are pinned by `lean-toolchain` and
`lakefile.toml`.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"

lake exe cache get
lake build
```

That produces `viprcheck`. SCIP is **not** required to check an existing `.vipr`.

## Run the paper example (knapsack)

The running example is the integer-infeasible knapsack
`6x+10y+15z = 23`, `x+y+z ≥ 1`, `0 ≤ x ≤ 3`, `0 ≤ y ≤ 2`, `0 ≤ z ≤ 1`, with
`x,y,z ∈ ℤ`. Its linear relaxation is feasible, so the certificate must branch.
Official exact SCIP 10.0.3 produced
[`examples/uns_knapsack.vipr`](examples/uns_knapsack.vipr) from
[`examples/uns_knapsack.mps`](examples/uns_knapsack.mps) (32 steps:
`asm`×2, `lin`×21, `rnd`×8, `uns`×1). Re-check that file:

```bash
lake exe viprcheck examples/uns_knapsack.vipr
```

Expected: `ACCEPT`, with `vars 3  int 3  con 8  steps 32`, those reason counts,
and a generated proof under `/tmp/viprcheck_proof/LeanVIPRGenerated/`.
Exit code `0` on accept, `1` on usage/parse error, `2` on reject.

Any other VIPR v1.0 `RTP infeas` file is the same command with a different path.
Use `--proof-dir DIR` to retain a separate generated artifact:

```bash
lake exe viprcheck examples/uns_knapsack.vipr --proof-dir /tmp/vipr-knapsack
```

Two small range examples exercise minimization and maximization, including
`{ sol }`:

```bash
lake exe viprcheck examples/valid_min_range.vipr
lake exe viprcheck examples/valid_max_range.vipr
```

For performance comparison only, the explicitly untrusted compiled path is:

```bash
lake exe viprcheck --native-precheck examples/uns_knapsack.vipr
```

It never claims kernel certification.

The two kernel modes are:

```bash
lake exe viprcheck --kernel-mode full CERT.vipr --proof-dir /tmp/vipr-full
lake exe viprcheck --kernel-mode reconstruct CERT.vipr --proof-dir /tmp/vipr-reconstruct
```

`full` kernel-checks the complete certificate with the array-backed checker.
`reconstruct`, which is the default, backward-slices the certificate and runs
the same checker on the slice for `RTP infeas`. The kernel checks both
the sliced replay and a row-subset theorem
transporting infeasibility back to the original certificate. If slicing fails,
the command falls back to complete replay, so it does not lose acceptance
completeness. Range certificates currently use complete replay.

## Optional: regenerate the certificate

Only needed if you want SCIP to emit a fresh `.vipr` from the MPS. Requires official
SCIP **10.0.3** built with exact solving (not 9.x). Full recipe:
[`docs/SCIP-SETUP.md`](docs/SCIP-SETUP.md).

Run the SCIP block from the repository root:

```bash
scip -c "set exact enable TRUE" \
     -c "set presolving maxrounds 0" \
     -c "set separating maxrounds 0" -c "set separating maxroundsroot 0" \
     -c "set certificate filename examples/uns_knapsack.vipr" \
     -c "read examples/uns_knapsack.mps" \
     -c "optimize" -c "quit"
```

Then run `lake exe viprcheck` on the file SCIP wrote. A different SCIP build may
emit a different (still valid) derivation; the result checker accepts any
well-formed supported VIPR derivation, not only the checked-in examples.

## Format coverage

LeanVIPR checks the five VIPR v1.0 derivation rules — `asm`, `lin`, `rnd`, `uns`,
and `{ sol }` — over rows of either sense, and both `RTP infeas` and `RTP range`.

It also accepts the `lin weak` derivations of v1.1: the missing variable-bound rows
are supplied by an untrusted completer, and the resulting ordinary combination is
rechecked by the verified `lin` rule, so the completer is not trusted. The reference
checker `viprchk` has no `lin weak` support and rejects such files outright.

The other v1.1 form, `lin incomplete`, supplies no multipliers at all; recovering
them requires solving an exact linear program, which is the job of a completer such
as the reference `viprcomp`. LeanVIPR reports it as unsupported and names the row,
rather than treating the file as malformed. The reference checker does not support
this form either.

## What is trusted

Relative to the emitted certificate AST, trusted: the Lean kernel and the small
definitions of “satisfies” and “infeasible”. Not trusted: SCIP, certificate replay
in the compiled CLI, and proof generation. The generated theorem is checked with
`decide +kernel`, not `native_decide`, and `ACCEPT` additionally requires its
reported axioms to be among `propext`, `Classical.choice`, and `Quot.sound`.

For `RTP range`, `Vipr.ClaimValid` states that every listed solution is feasible,
the primal witness bound holds, and the derived objective bound holds at every
feasible point (minimization: `lb ≤ obj(x)` for all feasible `x`). The classical
statement that every optimal value lies in `[lb, ub]` is the corollary
`Vipr.ClaimValid.optimal_within`.

## Parser verification

The reader is verified against an independent grammar rather than trusted. Two
specifications are stated without reference to any parser function — the number grammar
in [`LeanVIPR/Thm/Number/Grammar.lean`](LeanVIPR/Thm/Number/Grammar.lean) and the
certificate grammar in
[`LeanVIPR/Thm/Vipr/Grammar.lean`](LeanVIPR/Thm/Vipr/Grammar.lean) — and the reader is
proved to agree with both in each direction:

```lean
theorem parseNum_eq_some_iff  : parseNumChars? cs = some q ↔ IsNumValue cs q
theorem parseVipr_eq_ok_iff   : parseVipr content = .ok v ↔
                                  IsVipr (wsTokens content.toList) v ∧
                                  validateVipr v = .ok ()
```

Soundness is the direction that closes a gap: `checkVipr_sound` proves a claim about the
AST it is handed, so a token read as the wrong rational would let it establish a true
claim about a *different* mixed-integer problem. Completeness is what makes a rejection
meaningful, rather than possibly an artefact of a narrow reader. `isNumValue_unique` and
`isVipr_unique` record that neither grammar is ambiguous.

Two things are deliberately still outside this result. `validateVipr` appears in the
statement as a function, not as a declarative predicate: it is a semantic check on
indices (in range, each variable at most once per sparse vector, no derivation used
after its own final-use index), and stating it declaratively needs a sort with a
specification, which `Array.qsort` does not have. And the artifact does not
*kernel-check*, on each run, that the AST emitted into the generated proof is the parse
of the exact source bytes; the compiled CLI and the AST printer remain a frontend trust
boundary for that per-run binding. Neither is included in the benchmark below.

## VIPR-only benchmark

The artifact includes 20 infeasibility certificates from the published ALU
suite and 6 objective-range certificates from ALU/MIPLIB 3.0. All are genuine
official exact-SCIP 10.0.3 output.

Measured as one warmed sequential run on an Apple M3 Pro (12 cores, 36 GB),
Lean 4.35.0, macOS 26.7.1. These are compiled CLI timings and are not kernel
certification.

| Infeasibility family | Files | C++ pipeline | Lean full | Lean sliced |
|---|---:|---:|---:|---:|
| `alu4` | 6 | 0.83 s | 2.68 s | 0.74 s |
| `alu5` | 5 | 0.14 s | 0.44 s | 0.21 s |
| `alu6` | 5 | 0.52 s | 1.61 s | 0.51 s |
| `alu7` | 4 | 0.26 s | 0.84 s | 0.51 s |
| **Total** | **20** | **1.75 s** | **5.57 s** | **1.97 s** |

Range certificates currently use complete replay:

| Certificate | Steps | C++ pipeline | Lean full |
|---|---:|---:|---:|
| `alu4_9` | 40,648 | 0.51 s | 2.14 s |
| `egout` | 372 | 0.04 s | 0.07 s |
| `enigma` | 36,872 | 0.27 s | 3.15 s |
| `flugpl` | 7,553 | 0.09 s | 0.17 s |
| `gt2` | 3,284 | 0.20 s | 1.10 s |
| `vpm1` | 6,416 | 0.59 s | 2.87 s |
| **Total** | **95,145** | **1.70 s** | **9.50 s** |

The C++ column is the official `viprcomp --soplex=off --threads=1` followed by
`viprchk`, both built from scipopt/vipr `master` (`99eec19`), because every
selected solver certificate contains `lin weak`. Both pipelines accept all 26
certificates.

The exact per-certificate measurements and structural counts are in
[`benchmarks/results/checker.csv`](benchmarks/results/checker.csv);
official
C++ pipeline measurements are in
[`benchmarks/results/cpp.csv`](benchmarks/results/cpp.csv). Reproduce the Lean
measurements with:

```bash
python3 benchmarks/run_compiled.py \
  --modes full slice \
  --output benchmarks/results/checker.csv
```

## Benchmark setup

The 26 certificates above are checked in under `benchmarks/infeas/` and
`benchmarks/range/`, so they need no download.

A larger corpus of 112 published VIPR v1.0 certificates (about 18 GB gzipped) is
not stored in git. It contains:

- the 56 numerically easy and 50 numerically difficult MIPs from the
  [scipopt/vipr experiments](https://github.com/scipopt/vipr/tree/master/experiments)
- 3 Chvátal's-conjecture proofs
- 3 forged or manipulated certificates

Download it into `benchmarks/new/`. Each file is checked against the SHA-256
in [`benchmarks/new/manifest.csv`](benchmarks/new/manifest.csv):

```bash
python3 benchmarks/download_new.py                          # all 112; skips files already present
python3 benchmarks/download_new.py --sets negative chvatal  # or a subset
python3 benchmarks/download_new.py --verify                 # re-hash what is on disk
```

The reference C++ checker `viprchk` is built from
[scipopt/vipr](https://github.com/scipopt/vipr) at `99eec19` into the ignored
directory `viprcheck/`. It needs a C++ compiler, CMake, GMP and Boost (on macOS:
`brew install cmake gmp boost`):

```bash
git clone https://github.com/scipopt/vipr.git viprcheck
git -C viprcheck checkout 99eec19
cmake -S viprcheck/code -B viprcheck/code/build -DCMAKE_BUILD_TYPE=Release -DVIPRCOMP=OFF
cmake --build viprcheck/code/build --target viprchk
```

The 26 checked-in certificates contain `lin weak`, so their C++ pipeline
([`benchmarks/run_cpp.py`](benchmarks/run_cpp.py)) also needs `viprcomp`. To
build it, configure with `-DVIPRCOMP=ON`, which requires SoPlex. The 112
downloaded certificates are complete, so they need only `viprchk`.

Run `viprchk` and both Lean modes on every downloaded certificate, one process
at a time. Run this inside `tmux` or `screen`, because the whole corpus takes
many hours:

```bash
lake build viprcheck
python3 benchmarks/run_new.py --sets easy hard chvatal negative \
  --workdir /tmp/vipr-work --slice-all
```

The runner writes one CSV per method to `benchmarks/results/`: `new_cpp.csv`,
`new_lean_full.csv` and `new_lean_slice.csv`. It records the environment in
`new_env.csv` and writes per-run logs to `benchmarks/results/new_logs/`. Pass
`--resume` to continue an interrupted run, or create
`benchmarks/results/new_STOP` to stop after the current certificate. Without
`--slice-all`, slice mode runs only on `RTP infeas` certificates; for the other
certificates `viprcheck` falls back to complete replay anyway. The defaults are
a 1-hour timeout and an 18 GiB RSS / 32 GiB memory-footprint limit per check.

## License

Copyright 2026 the LeanVIPR contributors.

Licensed under the Apache License, Version 2.0; see [`LICENSE`](LICENSE).
