module

public import LeanVIPR.Completeness.IntegerHullSupport
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Dimension drop at a proper integer-hull support face

The support face lies in the affine hyperplane through its integral maximizer
whose direction is the kernel of the target linear form.  A hull point lying
strictly below the support value cannot belong to that hyperplane, hence
cannot belong to the affine span of the support face.  Therefore the face's
affine span is strictly contained in the hull's affine span and has strictly
smaller finite dimension.
-/

namespace LeanVIPR.Completeness.SupportDimension

open LeanVIPR.Cert
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.IntegerHullSupport
  LeanVIPR.Completeness.IntegerSupportFace

/-- Finite affine dimension, represented by the finrank of the affine span's
direction submodule. -/
noncomputable def affineDimension {vars : Finset Nat}
    (set : Set (FiniteValuation vars)) : Nat :=
  Module.finrank ℚ (affineSpan ℚ set).direction

theorem finiteEval_sub
    (vars : Finset Nat) (form : LinForm)
    (left right : FiniteValuation vars) :
    finiteEval vars form (left - right) =
      finiteEval vars form left -
        finiteEval vars form right := by
  exact (evalLinear vars form).map_sub left right

/-- The affine hyperplane through the support maximizer parallel to the
kernel of the target form. -/
def supportHyperplane
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    AffineSubspace ℚ (FiniteValuation intVars.toFinset) :=
  AffineSubspace.mk' witness.maximizer
    (LinearMap.ker
      (evalLinear intVars.toFinset target.form))

theorem mem_supportHyperplane_iff
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target)
    (point : FiniteValuation intVars.toFinset) :
    point ∈ supportHyperplane witness ↔
      finiteEval intVars.toFinset target.form point =
        (witness.value : ℚ) := by
  rw [supportHyperplane, AffineSubspace.mem_mk']
  change
    finiteEval intVars.toFinset target.form
        (point - witness.maximizer) = 0 ↔ _
  rw [finiteEval_sub, witness.maximizer_eq]
  constructor <;> intro h <;> linarith

theorem supportFace_subset_supportHyperplane
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    supportFace witness ⊆ supportHyperplane witness := by
  intro point hpoint
  exact
    (mem_supportHyperplane_iff witness point).2
      hpoint.2

theorem affineSpan_supportFace_le_supportHyperplane
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    affineSpan ℚ (supportFace witness) ≤
      supportHyperplane witness :=
  affineSpan_le_of_subset_coe
    (supportFace_subset_supportHyperplane witness)

theorem affineSpan_supportFace_lt_integerHull
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target)
    {point : FiniteValuation intVars.toFinset}
    (hpoint :
      point ∈ integerHull intVars.toFinset rows)
    (hbelow :
      finiteEval intVars.toFinset target.form point <
        (witness.value : ℚ)) :
    affineSpan ℚ (supportFace witness) <
      affineSpan ℚ (integerHull intVars.toFinset rows) := by
  have hle :
      affineSpan ℚ (supportFace witness) ≤
        affineSpan ℚ (integerHull intVars.toFinset rows) :=
    affineSpan_mono ℚ
      (supportFace_subset_integerHull witness)
  apply lt_of_le_of_ne hle
  intro heq
  have hpointSpan :
      point ∈ affineSpan ℚ (supportFace witness) := by
    rw [heq]
    exact mem_affineSpan ℚ hpoint
  have hpointHyperplane :
      point ∈ supportHyperplane witness :=
    affineSpan_supportFace_le_supportHyperplane
      witness hpointSpan
  have heval :=
    (mem_supportHyperplane_iff witness point).1
      hpointHyperplane
  linarith

/-- A proper support face has strictly smaller affine dimension than the
integer hull. -/
theorem affineDimension_supportFace_lt
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target)
    {point : FiniteValuation intVars.toFinset}
    (hpoint :
      point ∈ integerHull intVars.toFinset rows)
    (hbelow :
      finiteEval intVars.toFinset target.form point <
        (witness.value : ℚ)) :
    affineDimension (supportFace witness) <
      affineDimension
        (integerHull intVars.toFinset rows) := by
  have hspan :
      affineSpan ℚ (supportFace witness) <
        affineSpan ℚ
          (integerHull intVars.toFinset rows) :=
    affineSpan_supportFace_lt_integerHull
      witness hpoint hbelow
  have hfaceNonempty :
      ((affineSpan ℚ (supportFace witness) :
        AffineSubspace ℚ
          (FiniteValuation intVars.toFinset)) :
        Set (FiniteValuation intVars.toFinset)).Nonempty := by
    exact
      ⟨witness.maximizer,
        mem_affineSpan ℚ
          (LeanVIPR.Completeness.IntegerHullSupport.SupportWitness.maximizer_mem_supportFace
            witness)⟩
  have hdirection :
      (affineSpan ℚ (supportFace witness)).direction <
        (affineSpan ℚ
          (integerHull intVars.toFinset rows)).direction :=
    AffineSubspace.direction_lt_of_nonempty
      hspan hfaceNonempty
  exact
    Submodule.finrank_lt_finrank_of_lt hdirection

/-- The support objective is either constant on the integer hull or passing to
its exposed support face strictly decreases affine dimension. -/
theorem constant_or_affineDimension_supportFace_lt
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    (∀ point ∈ integerHull intVars.toFinset rows,
      finiteEval intVars.toFinset target.form point =
        (witness.value : ℚ)) ∨
    affineDimension (supportFace witness) <
      affineDimension
        (integerHull intVars.toFinset rows) := by
  rcases constant_or_exists_strictly_below witness with
    hconstant | ⟨point, hpoint, hbelow⟩
  · exact Or.inl hconstant
  · exact
      Or.inr
        (affineDimension_supportFace_lt
          witness hpoint hbelow)

end LeanVIPR.Completeness.SupportDimension
