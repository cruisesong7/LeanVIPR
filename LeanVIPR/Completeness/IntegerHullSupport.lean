module

public import LeanVIPR.Completeness.IntegerSupportFace

@[expose] public section

/-!
# Exposed support faces of the rational integer hull

An integral support witness bounds every integer point.  Convexity extends
that bound to the entire rational integer hull.  The equality set is a
nonempty convex exposed face, and either the objective is constant on the
whole integer hull or some hull point lies strictly below the support value.
This is the face dichotomy used by affine-dimension induction.
-/

namespace LeanVIPR.Completeness.IntegerHullSupport

open LeanVIPR.Cert
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.IntegerSupportFace

/-- The equality slice of the integer hull at an integral support value. -/
def supportFace
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    Set (FiniteValuation intVars.toFinset) :=
  {point |
    point ∈ integerHull intVars.toFinset rows ∧
      finiteEval intVars.toFinset target.form point =
        (witness.value : ℚ)}

theorem SupportWitness.integerHull_le
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    ∀ point ∈ integerHull intVars.toFinset rows,
      finiteEval intVars.toFinset target.form point ≤
        (witness.value : ℚ) := by
  have hsubset :
      integerHull intVars.toFinset rows ⊆
        {point |
          FiniteSat intVars.toFinset
            (supportRow target witness.value) point} := by
    apply convexHull_min
    · intro point hpoint
      exact witness.supportRow_valid point hpoint
    · exact finiteSat_convex intVars.toFinset
        (supportRow target witness.value)
  intro point hpoint
  exact hsubset hpoint

theorem supportFace_subset_integerHull
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    supportFace witness ⊆ integerHull intVars.toFinset rows :=
  fun _ hpoint => hpoint.1

theorem supportFace_convex
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    Convex ℚ (supportFace witness) := by
  intro left hleft right hright q r hq hr hsum
  constructor
  · exact
      integerHull_convex intVars.toFinset rows
        hleft.1 hright.1 hq hr hsum
  · rw [finiteEval_add, finiteEval_smul, finiteEval_smul,
      hleft.2, hright.2, ← add_mul, hsum, one_mul]

theorem SupportWitness.maximizer_mem_integerHull
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    witness.maximizer ∈ integerHull intVars.toFinset rows :=
  subset_convexHull ℚ
    (integerPoints intVars.toFinset rows)
    witness.maximizer_mem

theorem SupportWitness.maximizer_mem_supportFace
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    witness.maximizer ∈ supportFace witness :=
  ⟨LeanVIPR.Completeness.IntegerHullSupport.SupportWitness.maximizer_mem_integerHull
      witness,
    witness.maximizer_eq⟩

theorem supportFace_nonempty
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    (supportFace witness).Nonempty :=
  ⟨witness.maximizer,
    LeanVIPR.Completeness.IntegerHullSupport.SupportWitness.maximizer_mem_supportFace
      witness⟩

theorem supportFace_eq_integerHull_iff
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    supportFace witness = integerHull intVars.toFinset rows ↔
      ∀ point ∈ integerHull intVars.toFinset rows,
        finiteEval intVars.toFinset target.form point =
          (witness.value : ℚ) := by
  constructor
  · intro heq point hpoint
    have hface : point ∈ supportFace witness := by
      rw [heq]
      exact hpoint
    exact hface.2
  · intro hconstant
    apply Set.Subset.antisymm
    · exact supportFace_subset_integerHull witness
    · intro point hpoint
      exact ⟨hpoint, hconstant point hpoint⟩

/-- Either the support hyperplane contains the whole integer hull, or the
support face is proper because a hull point lies strictly below it. -/
theorem constant_or_exists_strictly_below
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    (∀ point ∈ integerHull intVars.toFinset rows,
      finiteEval intVars.toFinset target.form point =
        (witness.value : ℚ)) ∨
    ∃ point ∈ integerHull intVars.toFinset rows,
      finiteEval intVars.toFinset target.form point <
        (witness.value : ℚ) := by
  classical
  by_cases hconstant :
      ∀ point ∈ integerHull intVars.toFinset rows,
        finiteEval intVars.toFinset target.form point =
          (witness.value : ℚ)
  · exact Or.inl hconstant
  · right
    push Not at hconstant
    obtain ⟨point, hpoint, hne⟩ := hconstant
    exact
      ⟨point, hpoint,
        lt_of_le_of_ne
          (LeanVIPR.Completeness.IntegerHullSupport.SupportWitness.integerHull_le
            witness point hpoint)
          hne⟩

end LeanVIPR.Completeness.IntegerHullSupport
