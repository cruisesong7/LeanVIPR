# LeanVIPR (`viprcheck`)

LeanVIPR is a formally verified Lean 4 checker for **VIPR v1.0 infeasibility and
objective-range certificates**, using exact rational arithmetic throughout. The
solver that produced the certificate (exact SCIP) is **untrusted**: `viprcheck`
re-reads the file and re-derives the claim itself.

It has two modes. By default it runs a compiled checker that is proved sound and
complete against a declarative rendering of the VIPR proof system, which trusts
the Lean compiler and runtime. With `--kernel-mode` it instead emits the parsed
certificate as Lean data and asks Lean's kernel to reduce the checker, which
yields a machine-checked theorem together with the axioms it rests on.

`RTP infeas` uses the refutation checker; `RTP range` additionally checks every
`SOL` vector, `{ sol }` steps, the primal witness bound, and the final closed
dual-bound row. Acceptance means `Vipr.ClaimValid cert` has been derived.

What each mode claims is in [Modes and parameters](#modes-and-parameters); the
trust boundary, the measured results, and the SCIP recipe each have their own
document, listed under [Further reading](#further-reading).

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
axioms it rests on, and takes considerably longer than the default. Every mode is
listed under [Modes and parameters](#modes-and-parameters).

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

Slicing applies to `RTP infeas` only; range certificates are replayed completely
either way. If the slicer emits a slice the checker rejects, both the native and
kernel paths fall back to complete replay and say so, so slicing cannot cost an
acceptance.

### Complete replay, as an option

```bash
lake exe viprcheck --native-mode full CERT.vipr
```

This replays every step instead of slicing first. **It does not add any trust.**
Both modes run the same proved checker and both conclude about the same original
certificate — `checkViprSlice_sound` is what carries acceptance of a slice back,
and its side conditions are re-tested on every run. Complete replay is simply more
work for the identical claim.

It is worth having for two things: comparing against `viprchk`, which has no
slicing and always replays completely, and debugging, where seeing every step
checked is easier to reason about. Neither is a safety argument.

### Parallelism

| Parameter | Default | Meaning |
|---|---|---|
| `VIPRCHECK_TASKS=N` | `8` | Tasks the replay is split into. `1` spawns no task at all. Native modes only. |
| `--proof-dir DIR` | `/tmp/viprcheck_<mode>` | Where kernel mode writes the generated Lean module. Kernel modes only. |

`VIPRCHECK_TASKS` cannot change a verdict: `checkViprPar_eq` proves the parallel
checker returns what the sequential one returns for *every* task count. It is not
free of consequence, though — see [What is trusted](docs/VERIFICATION.md#what-is-trusted) for the
runtime machinery it brings in, and `N=1` for the setting that leaves it out.

One task per core measures best — more chunks lose more to contention over the
shared pool than they recover. Lean exposes no core count, hence the conservative
default.

It buys wall clock, not work: on step-heavy certificates the replay runs about 2.8x
faster while using roughly 4x the total CPU, because the tasks share the pool and
its reference counts have to be updated atomically.

Two diagnostics, neither of which claims anything: `--debug-first-invalid`
reports the first step the checker rejects, and `--dump-materialized` prints the
certificate after `lin weak` completion.

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
  Impl.lean       Impl/Parser.lean      Parser/     Utils  Printer
                  Impl/Checker.lean     Checker/    Form  Rules  Solution
  Thm.lean        Thm/Parser.lean       Parser/     Tokens  Number  NumberLemmas
                                                    Certificate  CertificateLemmas
                                                    Valid  Printer
                  Thm/System.lean       System/     Sound  RuleSound  RuleComplete
                                                    LinForm  Row  Claim  Completeness
                  Thm/Checker.lean      Checker/    Sound  Complete  Parallel
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

## Further reading

| Document | Contents |
|---|---|
| [`docs/VERIFICATION.md`](docs/VERIFICATION.md) | The trust boundary, and the parser's correctness theorems |
| [`benchmarks/README.md`](benchmarks/README.md) | The certificate corpus, measured results, and the runners |
| [`docs/SCIP-SETUP.md`](docs/SCIP-SETUP.md) | Building exact SCIP, and regenerating a `.vipr` from an `.mps` |
| [`examples/audit/README.md`](examples/audit/README.md) | Adversarial and edge-case certificates, with expected verdicts |

## License

Copyright 2026 the LeanVIPR contributors.

Licensed under the Apache License, Version 2.0; see [`LICENSE`](LICENSE).
