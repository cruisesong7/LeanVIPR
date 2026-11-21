# The `mip` tactic: roadmap

How to use what already exists is [`docs/TACTIC.md`](TACTIC.md); this is the plan for the
rest.

The endpoint is one tactic. A user writes a `Prop` about integers, types `mip`, and gets
either a proof or a refusal with a reason:

```lean
example : ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                         6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by mip
```

Everything between the goal and that proof — the emitter, the solver, the file, the
parser, the renaming guess — is untrusted, because `Mip.pipeline_infeasible` mentions none
of it. The two `Bool`s it does mention are decided against the reified `Mip`, so a fault
anywhere in the transport can make `mip` *fail* and cannot make it lie.

```
goal : Prop
  │  reflect                     (metacode, untrusted — may fail, cannot lie)
  ▼
m : Mip  ──encodeMps──▶  .mps  ──exact SCIP──▶  .vipr  ──parse──▶  v : Vipr
  │                                                                  │
  └───────────── agreesWith m v  (verified) ─────────────────────────┘
                              │  checkVipr v  (verified)
                              ▼
                      Mip.Infeasible m  ⟹  the original goal
```

The stages below are ordered so that each one is usable and testable before the next
exists, and each is a separate file in the `LeanVIPRTactic` target. The bundled tactic is
the last stage, not the first: when it fails, the question is always *which half* failed,
and the staging is what makes that answerable.

| stage | artifact | buys | status |
|---|---|---|---|
| 1 | `Scip.lean` — `runScip : Mip → IO (Except ScipError ScipRun)` | a certificate, and the pipeline's `Bool`s | **done, run against real SCIP** |
| 2 | `Command.lean` — `#mip_scip m` | the same, reported from Lean source; diagnosis | **done** |
| 3 | `Certify.lean` — a goal `m.Infeasible`, taken by `mip` | the proof term | **done** |
| 4 | `Reflect.lean` — a `Prop` goal to a `Mip` | the front end | **done**: `ℕ ℤ ℚ ℝ` mixed, rational coefficients, `∨`/`≠` splits |
| 5 | `Reflect.lean` — `mip` | the one tactic | **done**: `examples/mip_tactic_tests.lean`, 24 cases |
| 6 | `Optimize.lean` — `mip_maximize`, `mip_minimize` | `RTP range` results | **done**: `examples/mip_optimize_tests.lean`, 11 cases |

After stage 6, in order of value:

* ~~**Verified modeling encodings**~~ **done** for indicators and products with a binary
  (`addEncodings`, `examples/mip_encoding_tests.lean`), checked per instance rather than
  proved once in general. Not yet: encoding a disjunction with a fresh binary instead of
  splitting it into cases, which would save the `2^k` solver calls.
* **`mip?` and `(cert := "…")`**, as `bv_decide?` and `bv_check` do for LRAT proofs: save
  the certificates next to the source and suggest the call that reads them back, so the
  file builds without SCIP. A stale file fails `agreesWith`, so nothing new is trusted. An
  option rather than a separate `mip_check`, so it serves all three tactics.
* *Optional:* **re-check with [con-leche](https://github.com/leanprover/con-leche)**, an
  external kernel proven consistent, so a `mip` proof does not rest on Lean's C++ kernel.
  The checker-side items are in `docs/VERIFICATION.md`.
* **A native option** (`decide +native`) for certificates too large to reduce in the
  kernel, at the cost of trusting the compiler, as `bv_decide` does.

## 1. Drive SCIP from `IO` — done

`LeanVIPRTactic/Scip.lean`. `runScip m` writes `encodeMps m`, runs the solver with
certificate output enabled, parses the `.vipr`, and returns a `ScipRun`: the certificate
together with `agreesWith`, `relaxedByWith`, `checkVipr`, `objAgreesWith` and
`objAgreesNegWith`. No metaprogramming, so it is exercisable with `#eval`.

Measured on this machine, with the `-DEXACTSOLVE=ON` build of SCIP 10.0.1:

* the knapsack — 3 variables, 2 rows — comes back as a 32-derivation `RTP infeas`
  certificate with `agreesWith` and `checkVipr` both true, so `pipeline_infeasible`
  applies;
* the same problem with `c0`'s right-hand side at 25 comes back `RTP range 0 0`, and the
  driver reports no infeasibility conclusion rather than failing;
* `examples/mip_scip_smoke.lean` is the runnable version of all of this.

### Finding the binary is a capability question, not a version question

A build without `-DEXACTSOLVE=ON` cannot produce a certificate, and nothing it says about
itself distinguishes it: `--version` is identical, and the log line `storing certificate
information in file <…>` is printed before the solve. The fraction probe earlier revisions
of `docs/SCIP-SETUP.md` recommended — `x ≤ 1/2`, expecting `0.5` rather than a truncated
`1` — turns out to test whether `exact/enable` is *on*, not whether the build supports it:
measured 2026-11-10, without `set exact enable TRUE` both homebrew's `scip` 10.0.3 and our
`-DEXACTSOLVE=ON` 10.0.1 answer `-1`, and with it both answer `-1/2`.

So `probeBinary` asks for the thing the tactic needs, end to end: `x ≥ 1/2 ∧ x ≤ 1/2` over
the integers, infeasible *only* if `1/2` survives the round trip. A certificate must
appear, parse, agree with the Lean problem, satisfy `checkVipr`, and claim `RTP infeas`.
Result is cached per binary per process. Homebrew's 10.0.3 passes it here, so that build is
not disqualified on this evidence alone — but it has not been tried on anything harder than
the probe.

## 2. Report from a command — done

`LeanVIPRTactic/Command.lean`. `#mip_scip m` elaborates `m` to a `Mip`, evaluates it with
`Meta.evalExpr`, runs the driver and logs the result; `#mip_scip (dir := "/tmp/run") m`
leaves the `.mps` and `.vipr` behind to look at. It proves nothing on purpose — it is the
diagnostic half, kept separate so that "no certificate" and "certificate, no proof" never
arrive as the same error.

## 3. Close a `Mip.Infeasible` goal — next

`mip`, on a goal that is already `m.Infeasible` for a closed `m`. This is the
stage where the proof term appears, and the one with the real engineering in it.

[`examples/mip_prop_demo.lean`](../examples/mip_prop_demo.lean) is the proof term written
out by hand — certificate pasted in as data, two `decide +kernel`s, `pipeline_infeasible`,
then `absurd_of_infeasible` to a `¬ ∃ x y z : ℤ, …`, axioms `[propext, Classical.choice,
Quot.sound]`. It compiles in a few seconds, which settles the question of whether the
kernel route is viable at this size, and it is the target output for stages 3 to 5.

- [ ] Run the compiled checker first as an untrusted precheck (free: `runScip` already
      returns it), so a bad certificate fails fast with a readable message instead of
      hanging the kernel.
- [ ] Slice the certificate in compiled code — untrusted, and `sliceVipr` already exists
      in `LeanVIPRMain.lean`.
- [ ] Elaborate the sliced `Vipr` as a **literal term** with `Qq`. Do not run the parser
      in the kernel: `Impl/Parser.lean` has well-founded recursion and `mergeSort`,
      `Impl/Checker` has neither, which is exactly what makes `decide +kernel` viable.
- [ ] `decide +kernel` the two `Bool`s and apply `pipeline_infeasible`.
- [ ] Guard on size: the kernel route caps out around 6–7k certificate lines (measured in
      `docs/SCIP-ENCODER.md`). Past that, **fail loudly** rather than hang.
- [ ] Decide what to do about `--kernel-mode reconstruct`'s four small facts
      (`slicedInfeas`, `sameIntVars`, `rowsSubset`, `acceptedSlice`): reproduce them in
      `MetaM`, or keep the whole-certificate route for the tactic and leave slicing to
      `viprcheck`.

Lifting `LeanVIPRMain.lean`'s generated-file machinery into `MetaM` is the work; the
theorems it needs are all proved already.

## 4. Reflect a goal into a `Mip` — after 3

The acceptance list is [`examples/mip_prop_goals.lean`](../examples/mip_prop_goals.lean):
one problem in five phrasings — negated existential, `∀ … → False`, a row moved into the
conclusion as `≠`, strict bounds, and rows written with the constant on the left — each
proved today by the recipe this stage has to emit, plus a rational-coefficient goal proved
end to end. Every statement in that file must become `by mip`.

- [ ] Recognize `¬ ∃ x … : ℤ, c₁ ∧ … ∧ cₙ` with each `cᵢ` a linear (in)equality over the
      bound variables, and the four variants above.
- [ ] Build the row list through `LeanVIPR.Mip.Build.VRows`, so the predicate the rows
      denote is carried in the type and needs no separate proof.
- [ ] Extend the builder to cover variable **bounds** as well as explicit rows — today
      `absurd_of_spec` still leaves `∀ c ∈ m.boundSLes, …` to the caller. Recognizing
      `0 ≤ x ∧ x ≤ 3` as a bound rather than as two rows is what keeps the emitted MPS the
      shape SCIP expects.
- [ ] Emit the `ℤ → ℝ` cast bridge the hand-written demo writes by hand
      (`exact_mod_cast` per hypothesis; the recipe is in `docs/SCIP-ENCODER.md`).
- [ ] Report unrecognized shapes with the subterm that failed, not "mip failed".

## 5. The bundled tactic — after 4

`mip` is stages 4 and 3 composed, with one error taxonomy across both: no binary / wrong
binary / solver error or timeout / no certificate / parse error / `agreesWith` rejected /
`checkVipr` rejected / certificate too large for the kernel / goal shape not recognized.
Each needs to name the stage it came from, because the remedies are unrelated.

Options: `mip (timeout := 60)`, and `mip (dir := "…")` to keep the artifacts, in Lean's
configuration syntax (`Config.lean`). `mip?` is in the list after stage 6.

## 6. Beyond infeasibility — after 5

- [ ] `RTP range`: an objective-bound goal via `pipeline_lower_bound` /
      `pipeline_upper_bound_of_min`. Exact SCIP always reports `OBJ min`, negating the
      objective for a maximization, so the `_of_min` variants are the ones that fire and
      `objAgreesNegWith` is the check that passes.
- [ ] An optimal-point goal via `pipeline_optimal_min` and `feasible_of_solution`.

## Open items this roadmap inherits or found

* **A certificate shape `checkVipr` rejects.** `min -x` subject to `x ≤ 1/2`, `x`
  continuous: exact SCIP returns `RTP range -1/2 -1/2` and three derivations, the last a
  `GlobalBound_4 L 1/2 … { lin 1 3 1 } -1 global` row stated over `x` rather than over the
  objective. `checkVipr` rejects it, and `agreesWith` has nothing to do with the failure.
  Whether the reference C++ `viprchk` accepts it is **unmeasured** and worth measuring: a
  yes is a disagreement to explain (or another false acceptance), a no is a SCIP bug. This
  is why the stage-1 probe is an infeasibility problem — it avoids the objective machinery
  altogether. Repro: `#mip_scip` on that `Mip`, four lines.
* **No unboundedness result.** VIPR v1.0's `RTP` is `infeas` or `range`, so unboundedness
  is not expressible in the certificate format.
* **SCIP writes `RTP range -inf -infinity` for an unbounded objective**, and a solution
  with a variable at `+infinity`. The spec allows only a number or `inf` as the upper
  bound, so the parser rejects the file, rightly; `runScip` recognizes the shape and
  reports the objective unbounded (`ScipError.unbounded`, case 9 of
  `examples/mip_optimize_tests.lean`).
* **`mpsRoundTrip` is unproved** (tokenization half only). This costs completeness, not
  soundness — a faulty emitter makes `agreesWith` reject.
* **No totality.** Exact SCIP can time out or return something that fails agreement, and
  then the tactic fails. Same status as `bv_decide`, `polyrith` and Trestle.
* **`omega` closes the headline example.** Measured: the knapsack goal, which this whole
  pipeline is demonstrated on, falls to `rintro` plus `omega` in under a second — it is
  bounded all-integer feasibility, squarely inside linear integer arithmetic. So the
  demonstration problem cannot also be the motivation. What has no `omega` answer is
  rational coefficients, continuous variables alongside integer ones, objective bounds and
  optimality, and certificates at benchmark scale; the paper and the docs should lead with
  those, and `examples/mip_prop_goals.lean` keeps an instance of each honest.
