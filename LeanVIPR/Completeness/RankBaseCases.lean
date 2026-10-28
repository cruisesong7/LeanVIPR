module

public import LeanVIPR.Completeness.RankAssembly

@[expose] public section

/-!
# Base cases for pointwise finite CG rank

Two cases in the classical finite-rank argument are independent of the
dimension-reduction and support-shrinking geometry.

* If an integral inequality is already valid on the current rational
  relaxation and has an integral right-hand side, one semantic CG round
  derives it.
* If the current relaxation implies a nonintegral equality for an
  integer-valued form, the two opposite rounded inequalities refute the
  relaxation in one round.

The pointwise rank outcome permits either result, since an empty earlier
closure correctly terminates replay instead of deriving arbitrary rows.
-/

namespace LeanVIPR.Completeness.RankBaseCases

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
  LeanVIPR.Completeness.AffineHyperplaneRank
  LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.RankAssembly

theorem cast_floor_eq_of_isIntVal
    {bound : ℚ} (hbound : IsIntVal bound) :
    ((⌊bound⌋ : ℤ) : ℚ) = bound := by
  obtain ⟨value, rfl⟩ := hbound
  simp

/-- An integral inequality already valid on a feasible rational relaxation
is a semantic CG cut with no loss from rounding. -/
def rationallyValidCut
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hintegral : FormIntegralReal intVars target.form)
    (hrhs : IsIntVal target.rhs)
    (hvalid :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a) :
    SemanticCut intVars rows target where
  bound := target.rhs
  integral := hintegral
  valid := hvalid
  rhs_eq := (cast_floor_eq_of_isIntVal hrhs).symm

/-- A rationally valid integral inequality is present after one semantic CG
round, provided the current relaxation is rationally feasible. -/
def consequence_of_rationally_valid
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hfeasible : RatFeasible rows)
    (hintegral : FormIntegralReal intVars target.form)
    (hrhs : IsIntVal target.rhs)
    (hvalid :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a) :
    SemanticRankConsequence intVars rows target := by
  let round : SemanticRound intVars rows :=
    { feasible := hfeasible
      targets := [target]
      valid := by
        intro candidate hcandidate
        have heq : candidate = target := by
          simpa using hcandidate
        subst candidate
        exact rationallyValidCut hintegral hrhs hvalid }
  refine
    { finalRows := round.finalRows
      derivation := .round round (.done round.finalRows)
      mem_target := ?_ }
  simp [round, SemanticRound.finalRows, prependTargets]

/-- Pointwise finite-rank outcome for an inequality already valid on the
rational relaxation.  If the relaxation is empty, replay terminates with the
rank-zero refutation instead. -/
theorem finiteRankOutcome_of_rationally_valid
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hintegral : FormIntegralReal intVars target.form)
    (hrhs : IsIntVal target.rhs)
    (hvalid :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a) :
    Nonempty (SemanticRankRefutation intVars rows) ∨
      Nonempty (SemanticRankConsequence intVars rows target) := by
  by_cases hfeasible : RatFeasible rows
  · exact
      Or.inr
        ⟨consequence_of_rationally_valid
          hfeasible hintegral hrhs hvalid⟩
  · exact
      Or.inl
        ⟨
          { finalRows := rows
            derivation := .done rows
            infeasible := by
              intro a hrows
              exact hfeasible ⟨a, hrows⟩ }⟩

/-- The lattice-free affine-hull case directly supplies the refutation side
of every pointwise finite-rank outcome. -/
theorem finiteRankOutcome_of_implied_nonintegral_equality
    {intVars : List Nat} {rows : List Le} {target : Le}
    {form : LinForm} {bound : ℚ}
    (hintegral : FormIntegralReal intVars form)
    (hequality :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        LinForm.eval form a = bound)
    (hbound : ¬IsIntVal bound) :
    Nonempty (SemanticRankRefutation intVars rows) ∨
      Nonempty (SemanticRankConsequence intVars rows target) :=
  Or.inl
    (refutation_of_implied_nonintegral_equality
      hintegral hequality hbound)

end LeanVIPR.Completeness.RankBaseCases
