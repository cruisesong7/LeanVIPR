module

public import LeanVIPR.Completeness.RankBaseCases
public import LeanVIPR.Completeness.RecessionMonoid

@[expose] public section

/-!
# Integer-valid objectives on recession directions

If a rational polyhedron contains an integral point and an inequality is valid
on all of its integral points, then the inequality's left-hand side cannot
increase along a recession direction.  Otherwise a positive integral multiple
of that direction, added repeatedly to the integral point, eventually violates
the inequality.

This boundedness fact is used in the full-dimensional part of the classical
finite Chvátal--Gomory rank proof.
-/

namespace LeanVIPR.Completeness.RecessionObjective

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.IntegerProjection

/-- A LeanVIPR-valid inequality restricts to a valid inequality on the
finite-dimensional integer-point set. -/
theorem finite_valid_of_integer_valid
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hvalid :
      ∀ a : Valuation,
        (∀ idx ∈ intVars, IsIntVal (a idx)) →
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a) :
    ∀ point ∈ integerPoints intVars.toFinset rows,
      finiteEval intVars.toFinset target.form point ≤ target.rhs := by
  intro point hpoint
  let a := extendValuation point
  have hintegral :
      ∀ idx ∈ intVars, IsIntVal (a idx) := by
    intro idx hidx
    have hmem : idx ∈ intVars.toFinset := by
      simpa only [List.mem_toFinset] using hidx
    simpa [a, extendValuation, hmem] using
      hpoint.2 ⟨idx, hmem⟩
  have hrows :
      ∀ row ∈ rows, Le.sat row a := by
    intro row hrow
    exact hpoint.1 row hrow
  exact hvalid a hintegral hrows

/-- An integer-valid rational objective cannot increase along an integral
recession direction when an integral feasible base point exists. -/
theorem finiteEval_integral_recession_nonpos
    {vars : Finset Nat} {rows : List Le} {form : LinForm} {rhs : ℚ}
    (hpoint : (integerPoints vars rows).Nonempty)
    (hvalid :
      ∀ point ∈ integerPoints vars rows,
        finiteEval vars form point ≤ rhs)
    {direction : FiniteValuation vars}
    (hintegral : FiniteIntegral direction)
    (hdirection : direction ∈ recessionCone vars rows) :
    finiteEval vars form direction ≤ 0 := by
  by_contra hnonpositive
  have hpositive :
      0 < finiteEval vars form direction :=
    lt_of_not_ge hnonpositive
  obtain ⟨point, hpoint⟩ := hpoint
  obtain ⟨scale, hscale⟩ :=
    exists_nat_gt
      ((rhs - finiteEval vars form point) /
        finiteEval vars form direction)
  have hgap :
      rhs - finiteEval vars form point <
        (scale : ℚ) * finiteEval vars form direction :=
    (div_lt_iff₀ hpositive).mp hscale
  have hshift :
      point + (scale : ℚ) • direction ∈
        integerPoints vars rows :=
    add_integral_recession_mem_integerPoints
      hpoint hdirection hintegral scale
  have hbound :=
    hvalid
      (point + (scale : ℚ) • direction) hshift
  rw [finiteEval_add, finiteEval_smul] at hbound
  linarith

/-- The same nonincrease conclusion holds for every rational recession
direction, by scaling it to a positive integral recession direction. -/
theorem finiteEval_recession_nonpos
    {vars : Finset Nat} {rows : List Le} {form : LinForm} {rhs : ℚ}
    (hpoint : (integerPoints vars rows).Nonempty)
    (hvalid :
      ∀ point ∈ integerPoints vars rows,
        finiteEval vars form point ≤ rhs)
    {direction : FiniteValuation vars}
    (hdirection : direction ∈ recessionCone vars rows) :
    finiteEval vars form direction ≤ 0 := by
  obtain
      ⟨scale, hscalePositive, hintegral, hscaledDirection⟩ :=
    exists_integral_recession_multiple hdirection
  have hscaledNonpositive :
      finiteEval vars form ((scale : ℚ) • direction) ≤ 0 :=
    finiteEval_integral_recession_nonpos
      hpoint hvalid hintegral hscaledDirection
  rw [finiteEval_smul] at hscaledNonpositive
  have hscaleRational : (0 : ℚ) < scale := by
    positivity
  nlinarith

/-- LeanVIPR's pointwise validity premise therefore bounds the target form on
the entire rational recession cone whenever the mixed-integer set is
nonempty. -/
theorem recession_nonpos_of_integer_valid
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hpoint :
      (integerPoints intVars.toFinset rows).Nonempty)
    (hvalid :
      ∀ a : Valuation,
        (∀ idx ∈ intVars, IsIntVal (a idx)) →
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a)
    {direction : FiniteValuation intVars.toFinset}
    (hdirection :
      direction ∈ recessionCone intVars.toFinset rows) :
    finiteEval intVars.toFinset target.form direction ≤ 0 :=
  finiteEval_recession_nonpos
    hpoint (finite_valid_of_integer_valid hvalid) hdirection

end LeanVIPR.Completeness.RecessionObjective
