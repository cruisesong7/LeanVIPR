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

Expected: `NATIVE ACCEPT`, with `vars 3  int 3  con 8  steps 32` and those
reason counts. Exit code `0` on accept, `1` on usage/parse error, `2` on reject.

That is the compiled checker, which trusts the Lean compiler and runtime. For
the kernel-checked theorem on the same file:

```bash
lake exe viprcheck --kernel-mode reconstruct examples/uns_knapsack.vipr \
  --proof-dir /tmp/vipr-knapsack
```

That writes a Lean module under `/tmp/vipr-knapsack/LeanVIPRGenerated/`, has the
kernel reduce the checker over it, and prints the theorem together with the
axioms it rests on. It takes far longer; see
[Modes and parameters](#modes-and-parameters).

Any other VIPR v1.0 `RTP infeas` file is the same command with a different path.

Two small range examples exercise minimization and maximization, including
`{ sol }`:

```bash
lake exe viprcheck examples/valid_min_range.vipr
lake exe viprcheck examples/valid_max_range.vipr
```

## Modes and parameters

The default is the compiled checker on a backward slice. Everything else is an
option on top of it: more tasks, complete replay instead of slicing, or the
kernel.

| Invocation | What runs | What it claims |
|---|---|---|
| `viprcheck CERT.vipr` | **default** — compiled checker on a backward slice | Checker returned `true` on a slice, and `checkViprSlice_sound` carries that to the original. Trusts the Lean compiler and runtime. |
| `viprcheck --native-mode slice CERT.vipr` | same as the default | same |
| `viprcheck --native-mode full CERT.vipr` | compiled checker, every step | Checker returned `true`. Same trust, strictly more work. |
| `viprcheck --kernel-mode reconstruct CERT.vipr` | slices, then the kernel reduces the checker on the slice and the subset theorem | Machine-checked theorem; prints the axioms it rests on |
| `viprcheck --kernel-mode full CERT.vipr` | kernel reduces the checker on the whole certificate | same |

Both native modes print `NATIVE ACCEPT` or `NATIVE REJECT`. Kernel modes print
`ACCEPT (kernel-checked ...)` with the theorem name and `#print axioms`. Exit
codes: `0` accept, `1` usage or parse error, `2` reject.

### Why slicing is the default

Slicing concludes the same thing about the same certificate. `checkViprSlice_sound`
turns acceptance of a slice into a statement about the original, and the three side
conditions it needs — same `RTP`, same integer variables, rows a sublist of the
original's — are re-established at run time, so the untrusted slicer buys no trust
and costs none. It is simply less work: on `alu4_1`, 2.33s complete against 0.54s
sliced.

`--native-mode full` therefore proves nothing extra. It is kept for measuring
against the slice and for debugging, not because it is safer.

Slicing applies to `RTP infeas` only; range certificates are replayed completely
either way. If the slicer emits a slice the checker rejects, both the native and
kernel paths fall back to complete replay and say so, so slicing cannot cost an
acceptance.

### Parallelism

| Parameter | Default | Meaning |
|---|---|---|
| `VIPRCHECK_TASKS=N` | `8` | Tasks the replay is split into. `1` is sequential. Native modes only. |
| `--proof-dir DIR` | `/tmp/viprcheck_<mode>` | Where kernel mode writes the generated Lean module. Kernel modes only. |

`VIPRCHECK_TASKS` is a tuning knob and nothing else: `checkViprPar_eq` proves the
parallel checker returns what the sequential one returns for *every* task count,
so no value of `N` can change a verdict. One task per core measures best — more
chunks lose more to contention over the shared pool than they recover. Lean
exposes no core count, hence the conservative default.

It buys wall clock, not work: on step-heavy certificates the replay runs about 2.8x
faster while using roughly 4x the total CPU, because the tasks share the pool and
its reference counts have to be updated atomically.

Two diagnostics, neither of which claims anything: `--debug-first-invalid`
reports the first step the checker rejects, and `--dump-materialized` prints the
certificate after `lin weak` completion.

### Kernel mode is slow on purpose

Kernel mode asks Lean's kernel to reduce the checker by term rewriting, with no
compiled code involved. That costs minutes per certificate, and only small ones
finish. On `alu4_2` the budget is roughly 16s elaborating the certificate as a
Lean literal, 13s reducing `checkVipr`, and 7s importing Mathlib. It is a
proof-of-concept for the trusted path, not the way to check a certificate from a
solver run — use the default for that.

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

## Repository layout

```
LeanVIPR/
  Spec.lean       Spec/Syntax.lean      Syntax/     Ast  Grammar
                  Spec/Semantics.lean   Semantics/  LinCon  LinForm  Row  Lower
                                                    System  Claim  Completeness
  Impl.lean       Impl/Parser.lean      Parser/     Utils
                  Impl/Checker.lean     Checker/    Form  Rules  Solution
  Thm.lean        Thm/Parser.lean       Parser/     Grammar-agreement + lemmas
                  Thm/System.lean       System/     Sound  RuleSound  RuleComplete
                                                    LinForm  Row  Claim  Completeness
                  Thm/Checker.lean      Checker/    Sound  Complete
LeanVIPRMain.lean  -- the `viprcheck` command line
```

Three parts, and the division is the point of the development:

* **`Spec/`** — what a certificate is (`Syntax/`) and what it means (`Semantics/`).
  Nothing here refers to an executable function: no reader, no checker, no `Bool`, no
  `Except`. Accept these definitions and you know what `ACCEPT` means without reading
  the implementation.
* **`Impl/`** — the reader (`Parser/`) and the checker (`Checker/`). The only artifacts
  whose correctness is in question, and nothing here is trusted.
* **`Thm/`** — the proofs that `Impl` meets `Spec`, with one results file per layer
  (`Thm/Parser.lean`, `Thm/System.lean`, `Thm/Checker.lean`) beside the directory that
  proves it.

The dependency order is enforced, not just intended: `Spec/` imports nothing from
`Impl/` or `Thm/`, and `Impl/` imports only `Spec/`. So no correctness statement can be
satisfied by an implementation that merely agrees with itself.

Every directory has a header file beside it saying what is in it and what to read first,
so `Spec.lean`, `Spec/Syntax.lean` and `Spec/Semantics.lean` are each an index to the
directory of the same name.

## What is trusted

Relative to the emitted certificate AST, trusted: the Lean kernel and the small
definitions of “satisfies” and “infeasible”. Not trusted: SCIP, certificate replay
in the compiled CLI, and proof generation. The generated theorem is checked with
`decide +kernel`, not `native_decide`, and `ACCEPT` additionally requires its
reported axioms to be among `propext`, `Classical.choice`, and `Quot.sound`.

Two pieces of machinery in the default path are deliberately outside the trusted
set, because a theorem covers each of them:

- **The slicer.** `sliceVipr` is an untrusted heuristic. Nothing is taken on its
  word: `checkViprSlice_sound` requires the slice to carry the same `RTP` and the
  same integer variables and to have rows that are a sublist of the original's,
  and all three are re-tested at run time. A slice the checker rejects falls back
  to complete replay rather than becoming a rejection.
- **The task count.** `checkViprPar_eq` proves the parallel replay returns what
  the sequential one returns for every value of `VIPRCHECK_TASKS`, so the split
  cannot change a verdict. The proof needs no reasoning about concurrency:
  `Task.spawn fn` is `{ get := fn () }` in Lean's logic, so the parallelism is an
  evaluation strategy the logic cannot observe. Kernel mode reduces it
  sequentially.

Neither is a soundness boundary, and neither adds an axiom.

For `RTP range`, `Vipr.ClaimValid` states that every listed solution is feasible,
the primal witness bound holds, and the derived objective bound holds at every
feasible point (minimization: `lb ≤ obj(x)` for all feasible `x`). The classical
statement that every optimal value lies in `[lb, ub]` is the corollary
`Vipr.ClaimValid.optimal_within`.

## Parser verification

The reader is verified against an independent specification rather than trusted. That
specification is one file — [`Spec/Grammar.lean`](LeanVIPR/Spec/Grammar.lean),
about 450 lines — stated without reference to any parser function:

| section of `Spec/Grammar.lean` | covers |
|---|---|
| `IsNumValue` | a numeric token to an exact rational |
| `IsTokenization` | characters to tokens |
| `IsVipr`, `IsViprText` | tokens to a certificate |
| `IsValid` | when a certificate denotes a usable problem |

and the reader is proved to agree with it in both directions:

```lean
theorem parseVipr_eq_ok_iff : parseVipr content = .ok v ↔
                                (IsViprText content.toList v ∧ IsValid v)
```

Both sides of that `↔` matter. **Soundness** closes a gap replay cannot:
`checkVipr_sound` proves a claim about the AST it is handed, so a token read as the
wrong rational would let it establish a true claim about a *different* mixed-integer
problem. **Completeness** is what makes a rejection a statement about the file rather
than possibly an artefact of a narrow reader. `isVipr_unique`, `isTokenization_unique`
and `isNumValue_unique` record that no part of the grammar is ambiguous.

The specification contains no implementation function. Nothing on the right-hand side
of that `↔` reduces to `wsTokens`, `parseViprToks` or `validateVipr`; it mentions only
that one grammar file and the AST type definitions, which is checked mechanically. That is the property that makes
the theorem worth proving — a correctness statement phrased in terms of `wsTokens`
would take the tokenizer's own output as the definition of tokenization and so could
not detect a tokenizer that dropped, merged or truncated tokens.

One limit is worth naming because the grammar states it rather than hiding it. VIPR
v1.1 leaves the `DER` scope keyword `global`/`local` optional *and* unbracketed, so the
format is only unambiguous under maximal munch: a derivation *named* `global` or
`local` directly after a flagless row would have its name read as that row's flag.
`IsDers` carries that side condition. Such a file is rejected rather than misread, so
this limits completeness only, and it is a property of the format — `viprchk` has the
same exposure.

What remains trusted is the per-run binding, not the reader. The theorems are about the
Lean functions; the artifact does not *kernel-check*, on each run, that the AST emitted
into the generated proof is the parse of the exact source bytes. The compiled CLI, the
AST printer, and the OS/file plumbing sit outside this result and are not included in
the benchmark below.

## VIPR-only benchmark

The artifact includes 20 infeasibility certificates from the published ALU
suite and 6 objective-range certificates from ALU/MIPLIB 3.0. All are genuine
official exact-SCIP 10.0.3 output.

Measured as one warmed run on an Apple M3 Pro (12 cores, 36 GB), Lean 4.35.0,
macOS 26.7.1. These are compiled CLI timings and are not kernel certification.

**The runners pin `VIPRCHECK_TASKS=1`.** Upstream `viprchk` is single-threaded,
so a parallel LeanVIPR against a sequential `viprchk` would not be a comparison
of checkers but of core counts. Every number in this section is therefore one
core against one core. To measure the parallel replay instead, pass
`--lean-tasks N` to `benchmarks/run_new.py`, and compare against
`viprchk_parallel` rather than `viprchk` — upstream ships both.

Note also that the parallel replay trades CPU for wall clock: it costs roughly
4x the total CPU on step-heavy certificates, from atomic reference counting on
the pool the tasks share. Wall-clock tables will flatter it and CPU-time tables
will not, so say which is being reported.

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
