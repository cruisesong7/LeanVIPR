module

public import LeanVIPR.Thm.Encoder.Agree
public import LeanVIPR.Thm.Checker.Sound

@[expose] public section

/-!
# The end-to-end result

**This is what the branch was for.** Everything else in `Thm` concludes something about
*the problem a certificate carries in its own sections*. This file concludes something
about the problem written in Lean.

The chain is

```
m : Mip  ──encodeMps──▶  .mps  ──exact SCIP (untrusted)──▶  .vipr  ──parse──▶  v : Vipr
   │                                                                            │
   └────────────── agreesWith m v = true  (verified here) ──────────────────────┘
```

and the hypotheses of `pipeline_infeasible` are exactly the two `Bool`s a run produces:
`agreesWith m v` and `checkVipr v`. Neither the encoder nor the solver nor the parser
appears in the statement, which is the point — a misencoding, a mis-solve or a misparse
can only make `agreesWith` fail. None of them can make it lie.

Composed with `Mip.absurd_of_infeasible` from `Thm/Reflect.lean`, this closes the gap all
the way to a user's `Prop` about integer tuples.
-/

namespace LeanVIPR.Mip

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Semantics.System
open LeanVIPR.Parser LeanVIPR.Checker LeanVIPR.Impl.Encoder

/-- **The pipeline result.** If the agreement check passes, the verified checker accepts,
and the certificate claims infeasibility, then the Lean problem is infeasible.

No hypothesis constrains the renaming, and `m` need not be `WellFormed`: well-formedness
is what the *encoder* needs in order to produce a file at all, not something soundness
rests on. -/
theorem pipeline_infeasible {m : Mip} {v : Vipr}
    (hagree : agreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .infeas) :
    m.Infeasible := by
  intro a ha
  have hrel : m.Relaxes (sigmaFn (recoverSigma m v.varNames))
      (Lower.conSLes v) v.intVars := relaxesB_sound hagree
  obtain ⟨hints, hrows⟩ := hrel.feasible ha
  have hclaim : Vipr.ClaimValid v := checkVipr_sound v haccept
  rw [Vipr.ClaimValid, hrtp] at hclaim
  exact hclaim _ ⟨hints, hrows⟩

/-! ## The objective-bound results

A `RTP range` certificate establishes a *dual* bound: a lower bound when minimizing, an
upper bound when maximizing, holding at every feasible point. That is stronger than the
usual "the optimum lies in `[lb, ub]`" phrasing, because it bounds the infimum even when
no optimum is attained — so it is what we transfer, and `OptimumWithin` is a corollary.

The objective *sense* appears as an explicit hypothesis rather than inside the agreement
check, since which end of the interval a certificate establishes is a property of the
claim, not of whether the two problems match. -/

/-- A minimizing certificate's lower bound holds at every feasible point of `m`. -/
theorem pipeline_lower_bound {m : Mip} {v : Vipr} {lb ub : Option ℚ} {lower : ℚ}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    (hsense : v.objSense = "min")
    (hlb : lb = some lower) :
    ∀ a, m.Feasible a → (lower : ℝ) ≤ m.objectiveReal a := by
  intro a ha
  have hrel : m.Relaxes (sigmaFn (recoverSigma m v.varNames))
      (Lower.conSLes v) v.intVars := relaxesB_sound hagree
  obtain ⟨hints, hrows⟩ := hrel.feasible ha
  have hclaim : Vipr.ClaimValid v := checkVipr_sound v haccept
  rw [Vipr.ClaimValid, hrtp] at hclaim
  have hbound := hclaim.2
  simp only [Vipr.RangeBoundValid, hsense, hlb, ite_true] at hbound
  have := hbound _ ⟨hints, hrows⟩
  rwa [Vipr.objectiveReal, objectiveReal_comp (objAgreesWith_sound hobj)] at this

/-- A maximizing certificate's upper bound holds at every feasible point of `m`. -/
theorem pipeline_upper_bound {m : Mip} {v : Vipr} {lb ub : Option ℚ} {upper : ℚ}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    (hsense : v.objSense = "max")
    (hub : ub = some upper) :
    ∀ a, m.Feasible a → m.objectiveReal a ≤ (upper : ℝ) := by
  intro a ha
  have hrel : m.Relaxes (sigmaFn (recoverSigma m v.varNames))
      (Lower.conSLes v) v.intVars := relaxesB_sound hagree
  obtain ⟨hints, hrows⟩ := hrel.feasible ha
  have hclaim : Vipr.ClaimValid v := checkVipr_sound v haccept
  rw [Vipr.ClaimValid, hrtp] at hclaim
  have hbound := hclaim.2
  simp only [Vipr.RangeBoundValid, hsense, hub, ite_true] at hbound
  have := hbound _ ⟨hints, hrows⟩
  rwa [Vipr.objectiveReal, objectiveReal_comp (objAgreesWith_sound hobj)] at this

/-- **The result a user recognises for the minimizing case.** The optimum is no better
than the certificate's dual bound. Immediate from `pipeline_lower_bound`, since an optimal
point is in particular feasible. -/
theorem pipeline_optimum_within_min {m : Mip} {v : Vipr} {lb ub : Option ℚ} {lower : ℚ}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    (hsense : v.objSense = "min")
    (hlb : lb = some lower) :
    m.OptimumWithin (some lower) none := by
  intro a ha
  exact ⟨pipeline_lower_bound hagree hobj haccept hrtp hsense hlb a ha.1, trivial⟩

/-- **The maximization result that real certificates can actually discharge.**

`pipeline_upper_bound` above requires `v.objSense = "max"`, which exact SCIP never emits:
it normalizes a maximization by negating the objective, so the certificate says `OBJ min`
over `-obj` with its bounds negated. This is the version that matches. A minimizing
certificate's lower bound `lower` on `-obj` gives `-obj ≥ lower`, hence
`obj ≤ -lower` — an upper bound on the maximization. -/
theorem pipeline_upper_bound_of_min {m : Mip} {v : Vipr} {lb ub : Option ℚ} {lower : ℚ}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesNegWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    (hsense : v.objSense = "min")
    (hlb : lb = some lower) :
    ∀ a, m.Feasible a → m.objectiveReal a ≤ ((-lower : ℚ) : ℝ) := by
  intro a ha
  have hrel : m.Relaxes (sigmaFn (recoverSigma m v.varNames))
      (Lower.conSLes v) v.intVars := relaxesB_sound hagree
  obtain ⟨hints, hrows⟩ := hrel.feasible ha
  have hclaim : Vipr.ClaimValid v := checkVipr_sound v haccept
  rw [Vipr.ClaimValid, hrtp] at hclaim
  have hbound := hclaim.2
  simp only [Vipr.RangeBoundValid, hsense, hlb, ite_true] at hbound
  have hb := hbound _ ⟨hints, hrows⟩
  rw [Vipr.objectiveReal, objectiveReal_comp_neg (objAgreesNegWith_sound hobj)] at hb
  push_cast
  linarith

/-- `Mip.OptimumWithin` for a maximization, from the minimizing certificate SCIP emits. -/
theorem pipeline_optimum_within_max_of_min {m : Mip} {v : Vipr} {lb ub : Option ℚ}
    {lower : ℚ}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesNegWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    (hsense : v.objSense = "min")
    (hlb : lb = some lower) :
    m.OptimumWithin none (some (-lower)) := by
  intro a ha
  exact ⟨trivial, by
    simpa using pipeline_upper_bound_of_min hagree hobj haccept hrtp hsense hlb a ha.1⟩

/-! ## A verified optimal point

What the converse direction buys. `Relaxes` alone cannot deliver this: a solution is a
*positive* answer, so feasibility has to travel from the certificate back to `m`, which is
`Relaxed`. -/

/-- A solution listed in the certificate, read back through `τ`, is a feasible point of
`m`. The certificate's own `SOL` section is what guarantees it is feasible *there*;
`relaxedByWith` is what carries that to here. -/
theorem feasible_of_solution {m : Mip} {v : Vipr} {lb ub : Option ℚ}
    (hrelaxed : relaxedByWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    {s : Vipr.NamedSolution} (hs : s ∈ v.sols.toList) :
    m.Feasible (Vipr.solutionValuation s ∘ sigmaFn (recoverTau m v.varNames)) := by
  have hclaim : Vipr.ClaimValid v := checkVipr_sound v haccept
  rw [Vipr.ClaimValid, hrtp] at hclaim
  have hsol := hclaim.1
  rw [Vipr.SolSectionValid, hrtp] at hsol
  have hvf := hsol.1 s hs
  exact (relaxedB_sound hrelaxed).feasible hvf.1 hvf.2

/-- **A verified optimal point, minimizing.** Given a tight certificate and a feasible
point of `m` attaining the bound, that point is optimal. The dual bound rules out anything
better; the point itself supplies the primal side.

`m.objSense` appears as its own hypothesis because the claim is about *our* problem's
sense, which the agreement check does not compare — `v.objSense` governs which end of the
interval the certificate establishes, and the two are checked separately on purpose. -/
theorem pipeline_optimal_min {m : Mip} {v : Vipr} {z : ℚ} {a : RealValuation}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range (some z) (some z))
    (hsense : v.objSense = "min")
    (hmsense : m.objSense = .min)
    (hfeas : m.Feasible a)
    (hval : m.objectiveReal a = (z : ℝ)) :
    m.IsOptimal a := by
  refine ⟨hfeas, ?_⟩
  rw [hmsense]
  intro b hb
  rw [hval]
  exact pipeline_lower_bound hagree hobj haccept hrtp hsense rfl b hb

/-- The maximizing companion of `pipeline_optimal_min`. -/
theorem pipeline_optimal_max {m : Mip} {v : Vipr} {z : ℚ} {a : RealValuation}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range (some z) (some z))
    (hsense : v.objSense = "max")
    (hmsense : m.objSense = .max)
    (hfeas : m.Feasible a)
    (hval : m.objectiveReal a = (z : ℝ)) :
    m.IsOptimal a := by
  refine ⟨hfeas, ?_⟩
  rw [hmsense]
  intro b hb
  rw [hval]
  exact pipeline_upper_bound hagree hobj haccept hrtp hsense rfl b hb

/-- The maximizing companion. -/
theorem pipeline_optimum_within_max {m : Mip} {v : Vipr} {lb ub : Option ℚ} {upper : ℚ}
    (hagree : agreesWith m v = true)
    (hobj : objAgreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .range lb ub)
    (hsense : v.objSense = "max")
    (hub : ub = some upper) :
    m.OptimumWithin none (some upper) := by
  intro a ha
  exact ⟨trivial, pipeline_upper_bound hagree hobj haccept hrtp hsense hub a ha.1⟩

end LeanVIPR.Mip
