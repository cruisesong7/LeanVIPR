# `viprcheck`

`viprcheck` checks VIPR v1.0 infeasibility and objective-range certificates, using exact
rational arithmetic throughout. `RTP infeas` uses the refutation checker; `RTP range`
additionally checks every `SOL` vector, `{ sol }` steps, the primal witness bound, and the
final closed dual-bound row. Acceptance means `Vipr.ClaimValid cert` has been derived.

## The paper example (knapsack)

The running example is the integer-infeasible knapsack
`6x+10y+15z = 23`, `x+y+z ≥ 1`, `0 ≤ x ≤ 3`, `0 ≤ y ≤ 2`, `0 ≤ z ≤ 1`, with
`x,y,z ∈ ℤ`. Its linear relaxation is feasible, so the certificate must branch.
Official exact SCIP 10.0.3 produced
[`examples/uns_knapsack.vipr`](../examples/uns_knapsack.vipr) from
[`examples/uns_knapsack.mps`](../examples/uns_knapsack.mps) (32 steps:
`asm`×2, `lin`×21, `rnd`×8, `uns`×1).

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
axioms it rests on. It takes considerably longer than the default.

Two small range examples exercise minimization and maximization, including
`{ sol }`, and a third uses the one-unit cutoff that exact SCIP writes for integral
objectives. In the fourth, the row that proves the claim is not the last. The VIPR
specification requires it to be, but exact SCIP writes such certificates, so `viprcheck`
accepts any closed row that proves the claim and warns when it is not the last:

```bash
lake exe viprcheck examples/valid_min_range.vipr
lake exe viprcheck examples/valid_max_range.vipr
lake exe viprcheck examples/sol_integral_cutoff.vipr
lake exe viprcheck examples/proving_row_not_last.vipr
```

A certificate that is not UTF-8 is read as ISO-8859-1, with a warning; see
[`VERIFICATION.md`](VERIFICATION.md) for what that means for the trust boundary.

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
free of consequence, though — see [What is trusted](VERIFICATION.md#what-is-trusted) for the
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
