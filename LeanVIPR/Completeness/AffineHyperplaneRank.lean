module

public import LeanVIPR.Completeness.IntegerHullTargets

@[expose] public section

/-!
# One-round refutation of a nonintegral affine hull

If a rational relaxation forces an integer-valued form to equal a
nonintegral rational constant, two opposite Chvátal--Gomory cuts make the
relaxation rationally infeasible in one round.  This is the lattice-free
affine-hull case in the classical finite-rank proof.
-/

namespace LeanVIPR.Completeness.AffineHyperplaneRank

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
  LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness

def upperTarget (form : LinForm) (bound : ℚ) : Le :=
  ⟨form, ((⌊bound⌋ : ℤ) : ℚ)⟩

def lowerTarget (form : LinForm) (bound : ℚ) : Le :=
  ⟨LinForm.scale (-1) form, ((⌊-bound⌋ : ℤ) : ℚ)⟩

theorem neg_formIntegralReal
    {intVars : List Nat} {form : LinForm}
    (hintegral : FormIntegralReal intVars form) :
    FormIntegralReal intVars (LinForm.scale (-1) form) := by
  intro a hint
  obtain ⟨value, hvalue⟩ := hintegral a hint
  refine ⟨-value, ?_⟩
  rw [evalReal_scale, hvalue]
  push_cast
  ring

def upperCut
    {intVars : List Nat} {rows : List Le}
    (form : LinForm) (bound : ℚ)
    (hintegral : FormIntegralReal intVars form)
    (hequality :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        LinForm.eval form a = bound) :
    SemanticCut intVars rows (upperTarget form bound) where
  bound := bound
  integral := hintegral
  valid a hrows := (hequality a hrows).le
  rhs_eq := rfl

def lowerCut
    {intVars : List Nat} {rows : List Le}
    (form : LinForm) (bound : ℚ)
    (hintegral : FormIntegralReal intVars form)
    (hequality :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        LinForm.eval form a = bound) :
    SemanticCut intVars rows (lowerTarget form bound) where
  bound := -bound
  integral := neg_formIntegralReal hintegral
  valid a hrows := by
    change
      LinForm.eval (LinForm.scale (-1) form) a ≤ -bound
    rw [LinForm.eval_scale, hequality a hrows]
    norm_num
  rhs_eq := rfl

theorem not_mem_intCastRange_of_not_isIntVal
    {bound : ℚ} (hbound : ¬IsIntVal bound) :
    bound ∉ Set.range (fun value : ℤ => (value : ℚ)) := by
  rintro ⟨value, hvalue⟩
  apply hbound
  exact ⟨value, hvalue.symm⟩

/-- An implied nonintegral equality on an integer-valued form has a semantic
CG refutation of rank at most one. -/
theorem refutation_of_implied_nonintegral_equality
    {intVars : List Nat} {rows : List Le}
    {form : LinForm} {bound : ℚ}
    (hintegral : FormIntegralReal intVars form)
    (hequality :
      ∀ a : Valuation,
        (∀ row ∈ rows, Le.sat row a) →
        LinForm.eval form a = bound)
    (hbound : ¬IsIntVal bound) :
    Nonempty (SemanticRankRefutation intVars rows) := by
  by_cases hfeasible : RatFeasible rows
  · let upper := upperTarget form bound
    let lower := lowerTarget form bound
    let round : SemanticRound intVars rows :=
      { feasible := hfeasible
        targets := [upper, lower]
        valid := by
          intro target htarget
          by_cases hupper : target = upper
          · subst target
            exact upperCut form bound hintegral hequality
          · have hlower : target = lower := by
              simpa [hupper] using htarget
            subst target
            exact lowerCut form bound hintegral hequality }
    have hinfeasible : RatInfeasible round.finalRows := by
      intro a hrows
      have hupper : Le.sat upper a := by
        apply hrows upper
        simp [round, SemanticRound.finalRows,
          prependTargets, upper, lower]
      have hlower : Le.sat lower a := by
        apply hrows lower
        simp [round, SemanticRound.finalRows,
          prependTargets, upper, lower]
      change
        LinForm.eval form a ≤ ((⌊bound⌋ : ℤ) : ℚ)
        at hupper
      change
        LinForm.eval (LinForm.scale (-1) form) a ≤
          ((⌊-bound⌋ : ℤ) : ℚ)
        at hlower
      rw [LinForm.eval_scale, Int.floor_neg] at hlower
      have hceil :
          ⌈bound⌉ = ⌊bound⌋ + 1 :=
        (Int.ceil_eq_floor_add_one_iff_notMem bound).2
          (not_mem_intCastRange_of_not_isIntVal hbound)
      rw [hceil] at hlower
      push_cast at hlower
      linarith
    exact
      ⟨
        { finalRows := round.finalRows
          derivation := .round round (.done round.finalRows)
          infeasible := hinfeasible }⟩
  · exact
      ⟨
        { finalRows := rows
          derivation := .done rows
          infeasible := by
            intro a hrows
            exact hfeasible ⟨a, hrows⟩ }⟩

end LeanVIPR.Completeness.AffineHyperplaneRank
