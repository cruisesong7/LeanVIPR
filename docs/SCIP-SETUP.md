# Exact SCIP setup + real-certificate findings

## Which SCIP

Exact **rational** solving with **VIPR certificate output** was upstreamed into
**official SCIP 10** (files `certificate.cpp`, `lpexact.c`, `cons_exactlinear.c`, …).
It is *not* in the 9.2.0 release, nor in older mainline. Use the official
`scipoptsuite-10.0.1` (from scipopt.org). (A separate unofficial fork,
`leoneifler/exact-SCIP`, also exists but we do not use it.)

## Build recipe (arm64 macOS, verified working)

```
brew install boost mpfr gmp           # gmp usually already present
curl -sLO https://www.scipopt.org/download/release/scipoptsuite-10.0.1.tgz
tar xzf scipoptsuite-10.0.1.tgz && cd scipoptsuite-10.0.1
mkdir build && cd build
cmake .. \
  -DCMAKE_PREFIX_PATH=/opt/homebrew \
  -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
  -DEXACTSOLVE=ON -DGMP=on -DMPFR=on -DBOOST=on \
  -DZIMPL=off -DPAPILO=off -DGCG=off -DUG=off -DIPOPT=off -DSYM=none \
  -DREADLINE=off -DZLIB=off -DAMPL=off -DCMAKE_BUILD_TYPE=Release
make -j8 scip
# binary: build/bin/scip   (reports: "support for exact solving mode using exact LP solver SoPlex")
```

ZIMPL/PaPILO are disabled (system Bison is too old for ZIMPL; PaPILO pulls a
FetchContent sub-build that fails). Neither is needed: we feed MPS and disable
presolving (presolving is not certified anyway).

## Invocation (exact solve + complete certificate)

```
scip -c "set exact enable TRUE" \
     -c "set presolving maxrounds 0" \
     -c "set separating maxrounds 0" -c "set separating maxroundsroot 0" \
     -c "set certificate filename OUT.vipr" \
     -c "read PROBLEM.mps" -c "optimize" -c "quit"
```

The exact MPS reader parses coefficients via `RatSetString`, which accepts exact
`num/den` fractions — so we can emit our exact-ℚ encoding losslessly (dyadic or not).

### The float reader truncates fractions, silently

Measured on homebrew `scip` 10.0.3 `[precision: 8 byte]` **without** `set exact enable
TRUE`. See "What actually distinguishes the builds" below: the truncation tracks the
*mode*, not the build, so this is what a run with exact mode off looks like, whichever
binary does it. Given

```
ROWS
 N obj
 L r0
COLUMNS
    x obj 1/1
    x r0 1/1
RHS
    rhs r0 1/2
```

maximizing `x` reports a primal bound of **1.0**, not `0.5`: the reader takes `1/2` to be
`1`. There is no syntax error and no warning — the digits after the `/` are simply
dropped.

Consequences, all of which matter to `Impl.Encoder.Mps`:

* **A run with exact mode off cannot sanity-check the encoder**, except on problems whose
  every coefficient, right-hand side and bound is an integer. Those come out as `n/1`,
  which truncates to `n` and is right by luck.
* Such a run given an exact-ℚ file will **answer a different problem and report success**.
  `examples/uns_knapsack.mps` happens to be all-integer, so this is invisible on the one
  example in the repo.
* This is not an argument against MPS — the *exact* MPS reader is fine — but it means
  "SCIP read our file" is only meaningful once exact mode is confirmed on. Always pass
  `set exact enable TRUE`, and confirm the certificate afterwards.

For the record, the exact **LP** and **cip** readers are lossless too: `max (1/3)x + y`
s.t. `(2/5)x + y ≤ 7/4`, `y ≤ 1/6` yields `Exact Primal Bound : 107/72` from an `.lp`
file as readily as from the equivalent `.mps`. MPS is chosen for being cheaper to
formalize, not for rational fidelity — see `docs/SCIP-ENCODER.md`.

### What actually distinguishes the builds

**Not the `1/2` probe, and this document said otherwise until 2026-11-10.** Measured that
day on both binaries:

| | `scip` 10.0.3 (homebrew) | 10.0.1, `-DEXACTSOLVE=ON` |
|---|---|---|
| `min -x` s.t. `x ≤ 1/2`, no `exact enable` | `-1` | `-1` |
| the same with `set exact enable TRUE` | `-1/2` | `-1/2` |
| `x ≥ 1/2 ∧ x ≤ 1/2`, `x` integer, exact on | `RTP infeas`, accepted | `RTP infeas`, accepted |

So the truncation tracks whether exact mode is **on**, not which binary is running, and
the `1/2` answer is evidence about the flag only. Homebrew's 10.0.3 produced a certificate
this checker accepts; on that evidence it is not disqualified, though nothing harder than
the probe has been tried on it.

What a build without `-DEXACTSOLVE=ON` does is still worth stating: it cannot write a
certificate at all. And its log is no help — `storing certificate information in file
<out.vipr>` is printed before the solve, so it appears either way.

**Detect by capability.** `LeanVIPRTactic.Tactic.probeBinary` asks for exactly what a
caller needs: solve `x ≥ 1/2 ∧ x ≤ 1/2` over the integers — infeasible only if `1/2`
survives the round trip — and require a certificate that appears, parses, agrees with the
Lean problem, and satisfies `checkVipr`. Also note **SCIP resets the working directory
mid-run**, so a relative `certificate filename` does not land where the caller expects;
pass absolute paths.

## Real certificate observed (infeasible `2x≤1 ∧ 2x≥1`, x integer)

Official SCIP 10 emits (abridged): CON C0/C1 + variable bounds B2/B3; then DER with
signed-multiplier `lin` steps and `rnd` cuts, ending in `ActivityConflict11 L -1 0
{ lin 2 1 -1 6 2 }` — i.e. `-1·(2x≥1) + 2·(x≤0) ⇒ 0 ≤ -1`. (No case-split needed here;
SCIP used Gomory rounding.)

## Checker support

The checker implements the VIPR v1.0 rules used by official exact SCIP:

- signed suitable combinations over mixed `L`, `G`, and `E` senses;
- domination of the stated row;
- integer rounding;
- assumption introduction and branch discharge with `uns`;
- `RTP infeas` and finite `RTP range` results, including `SOL` and `{ sol }`.

The checked-in knapsack certificate was emitted by official exact SCIP 10.0.1
and exercises `asm`, `lin`, `rnd`, and `uns`.

## Maximization comes back as minimization

Exact SCIP normalizes a maximization by **negating the objective**, so the certificate
says `OBJ min` over `-obj` with its bounds negated. On `max (1/3)a + b` subject to
`(2/5)a + b ≤ 7/4`, `b ≤ 1/6` (optimum `107/72`) it emits

```
OBJ min
 2  0 -1/3 1 -1
RTP range -107/72 -107/72
```

Every certificate real exact SCIP has produced in this repository says `OBJ min`,
whatever the problem said; the only `OBJ max` anywhere is the hand-written
`examples/valid_max_range.vipr`.

Consequence for `Impl/Encoder/Agree.lean`: an agreement check that compares the
certificate's objective to ours for *equality* fails on every maximization. That is what
`Mip.ObjAgreesNeg` / `objAgreesNegWith` are for, and why `pipeline_upper_bound_of_min`
rather than `pipeline_upper_bound` is the theorem that fires on real output — a minimizing
certificate's lower bound `l` on `-obj` is an upper bound `-l` on ours.
