module

public import LeanVIPR.Completeness.FiniteRankCriterion
public import LeanVIPR.Completeness.FinitePolyhedron

@[expose] public section

/-!
# Integer-hull invariance of semantic CG derivations

Every semantic Chvátal--Gomory cut is valid on all integral points of its
current relaxation.  Adding finitely many such cuts therefore preserves the
integer-point set exactly, and hence also preserves its rational convex hull.

This invariant is important for the finite-rank completeness proof:
affine-dimension induction must recurse on auxiliary exposed faces.  It cannot
claim that the integer hull of the replay state itself becomes lower
dimensional after a sound CG round.
-/

namespace LeanVIPR.Completeness.RankInvariance

open LeanVIPR.Cert
  LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.FiniteRankCriterion

/-- A semantic CG round preserves the integral feasible points exactly. -/
theorem integerPoints_finalRows
    {intVars : List Nat} {rows : List Le}
    (round : SemanticRound intVars rows) :
    integerPoints intVars.toFinset round.finalRows =
      integerPoints intVars.toFinset rows := by
  ext point
  constructor
  · intro hpoint
    refine ⟨?_, hpoint.2⟩
    intro row hrow
    exact
      hpoint.1 row
        (mem_prependTargets_right round.targets rows hrow)
  · intro hpoint
    refine ⟨?_, hpoint.2⟩
    intro row hrow
    rw [SemanticRound.finalRows, prependTargets_eq_reverse_append] at hrow
    rcases List.mem_append.mp hrow with htarget | hrow
    · have htarget' : row ∈ round.targets := by
        simpa using htarget
      exact
        (integerPoints_subset_cgClosure intVars rows hpoint).2
          row (round.valid row htarget')
    · exact hpoint.1 row hrow

/-- A semantic CG round preserves the rational integer hull exactly. -/
theorem integerHull_finalRows
    {intVars : List Nat} {rows : List Le}
    (round : SemanticRound intVars rows) :
    integerHull intVars.toFinset round.finalRows =
      integerHull intVars.toFinset rows := by
  unfold integerHull
  rw [integerPoints_finalRows round]

/-- Every finite semantic CG-rank derivation preserves the integral feasible
points exactly. -/
theorem semanticRankDerivation_integerPoints_eq
    {intVars : List Nat} {first final : List Le}
    (derivation : SemanticRankDerivation intVars first final) :
    integerPoints intVars.toFinset final =
      integerPoints intVars.toFinset first := by
  induction derivation with
  | done rows =>
      rfl
  | @round rows final head tail ih =>
      rw [ih, integerPoints_finalRows head]

/-- Every finite semantic CG-rank derivation preserves the rational integer
hull exactly. -/
theorem semanticRankDerivation_integerHull_eq
    {intVars : List Nat} {first final : List Le}
    (derivation : SemanticRankDerivation intVars first final) :
    integerHull intVars.toFinset final =
      integerHull intVars.toFinset first := by
  unfold integerHull
  rw [semanticRankDerivation_integerPoints_eq derivation]

end LeanVIPR.Completeness.RankInvariance
