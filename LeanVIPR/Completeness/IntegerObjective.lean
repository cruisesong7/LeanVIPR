module

public import LeanVIPR.Completeness.RecessionObjective
public import LeanVIPR.Completeness.IntegerHull
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Maximizing integer-valid objectives on integer points

The affine Gordan--Dickson decomposition writes the integer points of a
rational polyhedron as finitely many integral base points plus the additive
monoid of integral recession directions.  If an objective is nonincreasing
on the recession cone, its maximum over all integer points is therefore
attained at one of the finitely many base points.
-/

namespace LeanVIPR.Completeness.IntegerObjective

open LeanVIPR.Cert
  LeanVIPR.Completeness.AffineMonoid
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.RecessionMonoid
  LeanVIPR.Completeness.RecessionObjective
open Set
open scoped Pointwise

/-- A linear objective nonincreasing on the recession cone attains its maximum
over every nonempty rational integer-point set. -/
theorem exists_integerPoint_maximizer
    {vars : Finset Nat} {rows : List Le} {form : LinForm}
    (hpoint : (integerPoints vars rows).Nonempty)
    (hrecession :
      ∀ direction ∈ recessionCone vars rows,
        finiteEval vars form direction ≤ 0) :
    ∃ maximizer,
      maximizer ∈ integerPoints vars rows ∧
      ∀ point ∈ integerPoints vars rows,
        finiteEval vars form point ≤
          finiteEval vars form maximizer := by
  obtain
      ⟨bases, generators, hbases, hgenerators,
        hpoints, _⟩ :=
    exists_finite_integerHull_decomposition vars rows
  have hbasesNonempty : bases.Nonempty := by
    obtain ⟨point, hpoint⟩ := hpoint
    rw [hpoints] at hpoint
    obtain
        ⟨_, ⟨base, hbase, rfl⟩,
          direction, hdirection, _⟩ :=
      hpoint
    exact ⟨base, hbase⟩
  obtain ⟨best, hbest, hmaximal⟩ :=
    Finset.exists_max_image bases
      (fun base => finiteEval vars form (decode base))
      hbasesNonempty
  refine ⟨decode best, hbases best hbest, ?_⟩
  intro point hpoint
  rw [hpoints] at hpoint
  obtain
      ⟨_, ⟨base, hbase, rfl⟩,
        direction, hdirection, rfl⟩ :=
    hpoint
  have hdirectionRecession :
      direction ∈ recessionCone vars rows :=
    closure_decode_recession
      (fun generator hgenerator =>
        (hgenerators generator hgenerator).2)
      hdirection
  have hdirectionNonpositive :
      finiteEval vars form direction ≤ 0 :=
    hrecession direction hdirectionRecession
  have hbaseBound :
      finiteEval vars form (decode base) ≤
        finiteEval vars form (decode best) :=
    hmaximal base hbase
  rw [finiteEval_add]
  linarith

/-- An inequality valid on a nonempty integer-point set has an integral
maximizer.  Recession nonincrease is discharged by the preceding rational
recession theorem. -/
theorem exists_integerPoint_maximizer_of_valid
    {vars : Finset Nat} {rows : List Le} {form : LinForm} {rhs : ℚ}
    (hpoint : (integerPoints vars rows).Nonempty)
    (hvalid :
      ∀ point ∈ integerPoints vars rows,
        finiteEval vars form point ≤ rhs) :
    ∃ maximizer,
      maximizer ∈ integerPoints vars rows ∧
      (∀ point ∈ integerPoints vars rows,
        finiteEval vars form point ≤
          finiteEval vars form maximizer) ∧
      finiteEval vars form maximizer ≤ rhs := by
  obtain ⟨maximizer, hmaximizer, hmaximum⟩ :=
    exists_integerPoint_maximizer hpoint
      (fun direction hdirection =>
        finiteEval_recession_nonpos
          hpoint hvalid hdirection)
  exact
    ⟨maximizer, hmaximizer, hmaximum,
      hvalid maximizer hmaximizer⟩

end LeanVIPR.Completeness.IntegerObjective
