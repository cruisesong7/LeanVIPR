> **Stale.** This roadmap was written from the `scip-encoder` branch. Stages 1–5 have
> since been built on the `mip-tactic` branch — `LeanVIPRTactic/{Scip,Reflect,Certify,
> Eval,Command}.lean` — where the driver spawns exact SCIP, `#mip_scip` reports a run, and
> `mip` closes a goal. Verified by running it: `examples/mip_prop_goals.lean` proves a goal
> with `by mip` at `[propext, Classical.choice, Quot.sound]`. Read this for the shape of
> the work, not for its status.

# The `mip` tactic: plan

Ordered so each step is testable on its own.

## 1. Drive SCIP from `IO`

- [ ] `runScip : Mip → IO (Except String Vipr)` — write `encodeMps m` to a temp file,
      invoke exact SCIP with `set exact enable TRUE` and `set certificate filename`,
      read back and parse the `.vipr`.
- [ ] Locate the binary: `LEANVIPR_SCIP` env var, else `scip` on `PATH`, and **verify it
      is the exact build by behaviour** — solve `max x s.t. x ≤ 1/2` and require `0.5`.
      `--version` is identical for both builds, so this check is not optional.
- [ ] Fail with a readable message, distinguishing: no binary, wrong binary, solver
      error, parse error, `agreesWith` rejected.

## 2. Reflect a goal into a `Mip`

- [ ] Recognize `¬ ∃ x … : ℤ, c₁ ∧ … ∧ cₙ` where each `cᵢ` is a linear (in)equality.
- [ ] Build the row list through `LeanVIPR.Mip.Build.VRows`, so the predicate the rows
      denote is carried in the type and needs no separate proof.
- [ ] Extend the builder to cover variable **bounds** as well as explicit rows — today
      `absurd_of_spec` still leaves bounds to the caller.
- [ ] Emit the `ℤ → ℝ` cast bridge that the demo currently writes by hand
      (`exact_mod_cast` per hypothesis).

## 3. Close the goal

- [ ] Elaborate the returned `Vipr` as a **literal term** with `Qq` — do not run the
      parser in the kernel. `Impl/Parser.lean` has well-founded recursion and `mergeSort`;
      `Impl/Checker` has neither, which is what makes `decide +kernel` viable.
- [ ] `decide +kernel` the two `Bool`s, then apply `pipeline_infeasible` and
      `Mip.Build.absurd_of_spec`.
- [ ] Run the compiled checker first as an untrusted precheck, so a bad certificate fails
      fast with a good message instead of hanging the kernel.
- [ ] Guard on certificate size: the kernel route caps out around 6–7k certificate lines
      (measured in LeanVIPR's `docs/SCIP-ENCODER.md`). Past that, **fail loudly** rather
      than hang.

## 4. Beyond infeasibility

- [ ] `RTP range`: discharge an objective-bound goal via `pipeline_lower_bound` /
      `pipeline_upper_bound_of_min`. Note exact SCIP always reports `OBJ min`, negating
      the objective for a maximization, so the `_of_min` variants are the ones that fire.
- [ ] An optimal-point goal via `pipeline_optimal_min` and `feasible_of_solution`.

## Known gaps inherited from LeanVIPR

- No unboundedness result: VIPR v1.0's `RTP` is `infeas` or `range`, so unboundedness is
  not expressible in the certificate format.
- `mpsRoundTrip` is unproved (tokenization half only). This costs completeness, not
  soundness — a faulty emitter makes `agreesWith` reject.
