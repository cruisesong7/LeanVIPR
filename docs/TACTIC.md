# Proving your own problem (`LeanVIPRTactic`)

`viprcheck` re-checks a certificate someone else produced. This target does the other
direction: you write a mixed-integer program *in Lean*, exact SCIP is asked about it, and
what comes back becomes a theorem about the problem you wrote — not about whatever problem
the certificate says it is about.

```
your Mip  ──encodeMps──▶  .mps  ──exact SCIP──▶  .vipr  ──parse──▶  v : Vipr
   │                                                                  │
   └───────────── agreesWith m v  (verified) ─────────────────────────┘
                              │  checkVipr v  (verified)
                              ▼
                          m.Infeasible
```

`Mip.pipeline_infeasible` depends on two `Bool`s only — `agreesWith m v` and
`checkVipr v` — and both are decided against the `Mip` and the certificate *as data*. The
emitter, the file, the solver, the parser and the renaming guess are all outside that, so
each of them can make the pipeline **fail**, and none can make it prove something false.

**State of play.** `mip` closes linear goals over `ℕ`, `ℤ`, `ℚ` and `ℝ`, mixed freely:

```lean
example (x y : ℤ) (h1 : 27 ≤ 11*x + 13*y) (h2 : 11*x + 13*y ≤ 45)
    (h3 : -10 ≤ 7*x - 9*y) (h4 : 7*x - 9*y ≤ 4) : False := by mip
```

Goals may be a comparison, `False`, `¬ ∃ …` or `a ≠ b`; `∨` and `≠` hypotheses are split
into cases; coefficients may be rational. Strict comparisons are exact over `ℕ` and `ℤ`
and relaxed (soundly) over `ℚ` and `ℝ`. When SCIP finds the problem feasible, the error
shows its solution and which hypotheses were read. The proof uses the three standard
axioms. `mip` also closes `m.Infeasible` for a `Mip` you wrote, and `#mip_scip m` reports
without proving.

`mip_maximize e` adds `hbound : e ≤ N`, and `mip_minimize e` adds `hbound : N ≤ e`, with `N`
the optimum SCIP certifies; `mip_maximize h : e` names it `h`. This is the analogue of
`lp`'s `maximize`, with integer variables allowed:

```lean
example (x y : ℤ) (h1 : x + y ≤ 4) (h2 : x - y ≤ 1) (h3 : 0 ≤ y) : 2*x + y ≤ 6 := by
  mip_maximize 2*x + y   -- the LP optimum is 6.5
  exact hbound
```

Cases are in [`examples/mip_optimize_tests.lean`](../examples/mip_optimize_tests.lean).

Beyond linear hypotheses, `mip` reads two more shapes, and treats anything non-linear as
a variable of its own:

* **Opaque terms** — `x * y`, `f x`, `n - m` over `ℕ`, `x / 2` over `ℤ` — become variables
  of the problem, integral and nonnegative when their type says so. Sound, as a
  relaxation.
* **Indicators** `δ = 1 → a ≤ b` (or `δ = 0 → …`) with `0 ≤ δ ≤ 1` an integer, and
  **products with a binary** `δ * x` with `x` bounded, become big-M and McCormick
  inequalities. Each is proved for the case at hand by splitting `δ = 0 ∨ δ = 1`, so no
  encoding is trusted. Cases are in
  [`examples/mip_encoding_tests.lean`](../examples/mip_encoding_tests.lean).

**Is this the right tool for your goal?** Prefer `omega` for small integer goals and
`linarith` or [`lp`](https://github.com/leanprover/lp) for rational ones: no solver
needed. `mip` is for what they cannot prove, each case in
[`examples/mip_tactic_tests.lean`](../examples/mip_tactic_tests.lean):

| goal | `omega` | `linarith`, `lp` | `mip` |
|---|---|---|---|
| integer, needs the omega test's dark shadow (Pugh) | fails | fails: LP relaxation feasible | ✓ |
| mixed integer and rational, infeasible by integrality | cannot state it | fails | ✓ |
| an indicator, with a binary on/off variable | cannot state it | ignored; `lp`'s `maximize` gives 30, 150/7 with big-M by hand, where the optimum is 19 | ✓ `mip_maximize` gives 19 |
| large, search outside Lean | — | — | ✓ only the certificate is checked |

## The tactics

| tactic | closes, or adds | options |
|---|---|---|
| `mip` | a linear goal — a comparison, `False`, `¬ ∃ …`, `a ≠ b` — over `ℕ ℤ ℚ ℝ`; or `m.Infeasible`, for a `Mip` you wrote | `(dir := "…")` keeps the `.mps` and `.vipr`; `(timeout := n)` seconds; `(cert := "…")` reads saved certificates instead of running SCIP |
| `mip_maximize e` | adds `hbound : e ≤ N`, `N` the certified maximum; `mip_maximize h : e` names it `h` | as `mip` |
| `mip_minimize e` | adds `hbound : N ≤ e`, `N` the certified minimum | as `mip` |
| `mip?`, `mip_maximize?`, `mip_minimize?` | as without `?`, and save the certificates, suggesting the `(cert := "…")` call | as `mip`, less `cert` |
| `#mip_scip m` | nothing: runs SCIP on `m` and reports the certificate and its checks | as `mip` |

Options are Lean's configuration syntax, as for `omega` and `decide`, so they combine in
any order and a misspelled one is an error. Where a term follows them, only the
`(opt := v)` form is accepted, so `mip_maximize -x` maximizes `-x`.

All of them need a certifying SCIP (below), except to replay saved certificates, and every
proof uses the three standard axioms.

### Building without SCIP

`mip?` runs SCIP once, writes every certificate the call needed to
`File-decl-line-col.vipr` next to the Lean file, and suggests the call that reads them
back:

```lean
theorem pugh … : False := by
  mip (cert := "Pugh-pugh-5-2.vipr")   -- was `mip?`; now builds with no solver installed
```

This is what `bv_decide?` and `bv_check` do for LRAT proofs. The saved file is as
untrusted as SCIP's output: each certificate is still checked in the kernel against the
problem the call builds, so after an edit that changes the problem the proof fails with
"not about this problem" and a prompt to rerun `mip?`.
[`examples/mip_cert_tests.lean`](../examples/mip_cert_tests.lean) checks this way.

## Setup

A certifying SCIP build is required, and only for this target — `viprcheck` never needs
one. Build it as in [`docs/SCIP-SETUP.md`](SCIP-SETUP.md), then:

```bash
export LEANVIPR_SCIP=~/scip-exact/scipoptsuite-10.0.1/build/bin/scip
lake build LeanVIPRTactic
```

With `LEANVIPR_SCIP` unset, `scip` from `PATH` is tried instead. Either way the binary is
checked by *capability* before use: a one-variable problem is solved and the certificate
must appear, parse, agree and be accepted. A build that cannot certify is rejected with a
message saying so, rather than quietly answering a different question. (Why this is not a
`--version` check, and why the fraction probe the docs used to recommend does not work, is
in [`docs/SCIP-SETUP.md`](SCIP-SETUP.md#what-actually-distinguishes-the-builds).)

Nothing in the `LeanVIPR` library imports `LeanVIPRTactic`, so the checker stays free of
metaprogramming, `IO`, and any dependency on a solver being installed.

## 1. Write the problem as a `Mip`

```lean
import LeanVIPRTactic
open LeanVIPR LeanVIPR.Tactic

def knapsack : Mip where
  vars := #[{ name := "x", isInt := true, lo := some 0, hi := some 3 },
            { name := "y", isInt := true, lo := some 0, hi := some 2 },
            { name := "z", isInt := true, lo := some 0, hi := some 1 }]
  objSense := .min
  obj := []
  rows := #[{ name := "c0", sense := 'E', rhs := 23,
              form := [⟨0, 6⟩, ⟨1, 10⟩, ⟨2, 15⟩] },   -- 6x + 10y + 15z = 23
            { name := "c1", sense := 'G', rhs := 1,
              form := [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] }]      -- x + y + z ≥ 1
```

* **Variables are indices.** A `form` is a list of `⟨index into vars, coefficient⟩`
  pairs, and coefficients are exact `ℚ` — `1/3` means a third, not `0.333…`.
* **Bounds live on the variable, not in `rows`.** `lo`/`hi` are `Option ℚ` with `none`
  meaning infinite, and the defaults are MPS's own: continuous, `lo := some 0`,
  `hi := none`. `Mip.conSLes` is `rows` followed by one row per finite bound, lower before
  upper, in index order — that list is what the certificate gets compared against.
* **Senses** are `'L'`, `'G'`, `'E'`.
* Distinct variables need distinct names and so do distinct rows (`Mip.WellFormed`), since
  names are what the problem file refers to. Well-formedness is what the *emitter* needs;
  no soundness result assumes it.
* The objective may be empty, as here. An infeasibility question does not use it.

## 2. Ask the solver

```lean
#mip_scip knapsack
```

```
/Users/you/scip-exact/scipoptsuite-10.0.1/build/bin/scip
certificate: 3 vars, 8 cons, 32 ders, RTP infeas, OBJ min
agreesWith: yes   checkVipr: yes   relaxedByWith: yes
objAgreesWith: yes   objAgreesNegWith: yes
pipeline_infeasible applies: true
```

`#mip_scip (dir := "/tmp/run") knapsack` leaves the `.mps` and `.vipr` in `/tmp/run` to
look at. The command only logs — it proves nothing, and is the thing to reach for when a
run needs diagnosing.

Reading the report: each `yes` is a hypothesis some pipeline theorem wants, and together
they say which conclusions are available.

| certificate says | plus | gives you | theorem |
|---|---|---|---|
| `RTP infeas` | `agreesWith`, `checkVipr` | `m.Infeasible` | `pipeline_infeasible` |
| `RTP range l u`, `OBJ min` | `objAgreesWith` | `l ≤ obj` at every feasible point | `pipeline_lower_bound` |
| `RTP range l u`, `OBJ min`, your problem maximizes | `objAgreesNegWith` | `obj ≤ -l` | `pipeline_upper_bound_of_min` |
| `RTP range z z` | a feasible point attaining `z` | `m.IsOptimal a` | `pipeline_optimal_min` / `_max` |
| any, with a `SOL` entry | `relaxedByWith` | that entry is feasible for *your* problem | `feasible_of_solution` |

Two things worth knowing about what SCIP returns:

* **It renames and permutes your variables.** The knapsack comes back declaring
  `t_y t_x t_z`, so the certificate's `C0` lists `(0, 10)` before `(1, 6)` where yours
  lists `6x` first. `agreesWith` recovers the renaming itself and compares rows as linear
  functions, so none of this needs handling. A wrong guess can only cause a rejection.
* **A maximization comes back as a minimization.** Exact SCIP negates the objective, so
  the certificate says `OBJ min` whatever you asked, with its bounds negated. That is why
  `objAgreesNegWith` and the `_of_min` theorems exist, and why they are the ones that fire
  on real output.

## 3. Drive it from `IO`

`#mip_scip` is a thin wrapper over the driver, which is plain `IO` and `#eval`-able:

```lean
#eval show IO Unit from do
  match ← runScip knapsack with
  | .error e => IO.println e.message
  | .ok r =>
    IO.println r.summary
    if !r.provesInfeasible then throw (IO.userError "expected infeasibility")
```

`ScipRun` carries the certificate (`cert`), the emitted file (`mps`, for diagnostics
only), and the five decisions: `agrees`, `relaxedBy`, `accepted`, `objAgrees`,
`objAgreesNeg`. `provesInfeasible` is the conjunction `pipeline_infeasible` needs.

`runScip m cfg` takes a `ScipConfig`:

| field | default | meaning |
|---|---|---|
| `binary` | `none` | the solver to use; `none` means `LEANVIPR_SCIP` then `scip` |
| `timeLimit` | `none` | seconds, passed as `set limits time` |
| `verifyBinary` | `true` | run the capability probe (cached per binary per process) |
| `workDir` | `none` | keep the `.mps`/`.vipr` here instead of a temporary directory |
| `problemName` | `"leanvipr"` | the `NAME` field, and the file stem |

`findScip cfg` resolves a binary without solving anything, and `probeBinary` is the
capability check on its own.

## 4. Turn it into a theorem

`theorem knapsack_infeasible : knapsack.Infeasible := by mip` does all of this. By hand it
is short, and shows what `mip` builds.
[`examples/mip_prop_demo.lean`](../examples/mip_prop_demo.lean) is the whole thing,
compiling in a few seconds with `#print axioms` reporting the standard three.

Paste the certificate in as Lean data — `(repr r.cert).pretty` prints it in re-readable
form — and then:

```lean
theorem agreed   : agreesWith knapsack cert = true := by decide +kernel
theorem accepted : checkVipr cert = true           := by decide +kernel
theorem isInfeas : cert.rtp = .infeas              := by decide +kernel

theorem knapsack_infeasible : knapsack.Infeasible :=
  Mip.pipeline_infeasible agreed accepted isInfeas
```

`decide +kernel`, not `decide`: Lean's kernel performs the check, so the compiler is not
trusted for it. `native_decide` would add a per-theorem axiom and is used nowhere in this
development.

From there to the statement you wanted, `Mip.absurd_of_infeasible` is the bridge — and
integrality is free, because a valuation built by casting integers is integral at every
index:

```lean
theorem knapsack_unsolvable :
    ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                   6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by
  rintro ⟨x, y, z, hx0, hx3, hy0, hy2, hz0, hz1, heq, hge⟩
  refine Mip.absurd_of_infeasible knapsack_infeasible [x, y, z] ?_
  -- rows live over ℝ: move each hypothesis across the cast, then close them row by row
  …
```

What is left after `refine` is one real inequality per row of `conSLes`, which
`norm_num`/`linarith` close. `knapsack.conSLes = […] := by rfl` holds — the row list
computes — which is what makes that step mechanical rather than merely finite.

## When it fails

The pipeline is **not** a decision procedure, and will not become one: exact SCIP can time
out or return something that fails agreement, and then you get a refusal. Same status as
`bv_decide`, `polyrith` and Trestle. Every failure names which stage it came from, because
the remedies are unrelated:

| message | means | do |
|---|---|---|
| `no SCIP binary found` | nothing spawnable at `LEANVIPR_SCIP` or on `PATH` | build one ([SCIP-SETUP](SCIP-SETUP.md)) and export `LEANVIPR_SCIP` |
| `did not pass the certificate probe` | it runs but cannot certify, or does not read `1/2` exactly | use a `-DEXACTSOLVE=ON` build |
| `SCIP … exited with code N` | solver error, or the time limit | read the log tail in the message; raise `timeLimit` |
| `reported success but wrote no certificate` | no `.vipr` appeared | almost always a non-certifying build |
| `does not parse` | the file is not VIPR v1.0 as we read it | keep it with `(dir := …)` and open it; this is a bug report |
| `reports the objective unbounded` | `mip_maximize`/`mip_minimize` found no finite bound, which VIPR cannot certify | check which hypotheses were read; a bound may be missing |
| `agreesWith: NO` | the certificate is not about your problem | compare `conSLes` with the certificate's `CON` block; check for an emitter bug |
| `checkVipr: NO` | the certificate itself does not check out | a certificate this checker cannot verify — see the known shape in [TACTIC-TODO](TACTIC-TODO.md#open-items-this-roadmap-inherits-or-found) |

Two limits that are not errors: the kernel route caps out around 6–7k certificate lines
(measured in [`docs/SCIP-ENCODER.md`](SCIP-ENCODER.md)), and VIPR v1.0 cannot express
unboundedness — `RTP` is `infeas` or `range`, so there is nothing to transfer.

## Examples

| file | shows |
|---|---|
| [`examples/mip_prop_goals.lean`](../examples/mip_prop_goals.lean) | **the goals `mip` must take** — one problem in five phrasings, a rational-coefficient goal proved end to end, and what `omega` already does |
| [`examples/mip_prop_demo.lean`](../examples/mip_prop_demo.lean) | the whole path from a certificate to `¬ ∃ x y z : ℤ, …`, by hand |
| [`examples/mip_scip_smoke.lean`](../examples/mip_scip_smoke.lean) | `runScip` and `#mip_scip` on an infeasible problem, a feasible one, and the probe problem |
| [`examples/mip_cert_tests.lean`](../examples/mip_cert_tests.lean) | proofs from certificates `mip?` saved, including the indicator example; checks with no solver |

`mip_scip_smoke.lean` needs a solver, so it is not part of `lake build`:

```bash
LEANVIPR_SCIP=~/scip-exact/scipoptsuite-10.0.1/build/bin/scip \
  lake env lean examples/mip_scip_smoke.lean
```

`mip_prop_demo.lean` carries its certificate inline and needs no solver:

```bash
lake env lean examples/mip_prop_demo.lean
```

## Further reading

| Document | Contents |
|---|---|
| [`docs/TACTIC-TODO.md`](TACTIC-TODO.md) | the roadmap to the bundled tactic, stage by stage |
| [`docs/SCIP-ENCODER.md`](SCIP-ENCODER.md) | why a `Mip` type, the theorems, and what is and is not proved |
| [`docs/SCIP-SETUP.md`](SCIP-SETUP.md) | building exact SCIP, and how to tell a certifying build |
| [`docs/VERIFICATION.md`](VERIFICATION.md) | the trust boundary of the checker itself |
