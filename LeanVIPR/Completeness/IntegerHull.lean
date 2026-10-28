module

public import LeanVIPR.Completeness.AffineMonoid
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Geometry.Convex.Cone.Basic

@[expose] public section

/-!
# Finite generation of the rational integer hull

The affine Gordan--Dickson construction gives finitely many integral base
points and a finitely generated additive recession monoid.  This file turns
that discrete decomposition into a convex-geometric description of the
rational integer hull.
-/

namespace LeanVIPR.Completeness.IntegerHull

open LeanVIPR.Cert LeanVIPR.Completeness.AffineMonoid
  LeanVIPR.Completeness.FinitePolyhedron LeanVIPR.Completeness.RecessionMonoid
open Set
open scoped Pointwise

/-- The convex hull of a generated additive monoid is the rational cone hull
of zero together with its generators. -/
theorem convexHull_addSubmonoidClosure_eq_coneHull
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (generators : Set V) :
    convexHull ℚ
        (AddSubmonoid.closure generators : Set V) =
      (ConvexCone.hull ℚ ({0} ∪ generators) : Set V) := by
  let monoid := AddSubmonoid.closure generators
  let hullSet := convexHull ℚ (monoid : Set V)
  have hzero : (0 : V) ∈ hullSet := by
    apply subset_convexHull ℚ (monoid : Set V)
    exact monoid.zero_mem
  have hadd :
      ∀ {left right : V},
        left ∈ hullSet →
          right ∈ hullSet →
            left + right ∈ hullSet := by
    intro left right hleft hright
    have hsum : left + right ∈ hullSet + hullSet :=
      ⟨left, hleft, right, hright, rfl⟩
    have hconvexSum :
        left + right ∈
          convexHull ℚ
            ((monoid : Set V) + (monoid : Set V)) := by
      rw [convexHull_add]
      exact hsum
    apply convexHull_mono _ hconvexSum
    rintro point
      ⟨first, hfirst, second, hsecond, rfl⟩
    exact monoid.add_mem hfirst hsecond
  have hsmul :
      ∀ {coefficient : ℚ}, 0 < coefficient →
        ∀ {point : V}, point ∈ hullSet →
          coefficient • point ∈ hullSet := by
    intro coefficient hcoefficient point hpoint
    have hnsmul :
        ∀ bound : ℕ, bound • point ∈ hullSet := by
      intro bound
      induction bound with
      | zero =>
          simpa using hzero
      | succ bound ih =>
          rw [succ_nsmul]
          exact hadd ih hpoint
    obtain ⟨bound, hbound⟩ :=
      exists_nat_gt coefficient
    have hboundPositive : (0 : ℚ) < bound :=
      hcoefficient.trans hbound
    have hboundPoint :
        (bound : ℚ) • point ∈ hullSet := by
      rw [Nat.cast_smul_eq_nsmul]
      exact hnsmul bound
    have hratio :
        coefficient / (bound : ℚ) ∈
          Set.Icc (0 : ℚ) 1 := by
      constructor
      · positivity
      · exact
          (div_le_one hboundPositive).2 hbound.le
    have hscaled :=
      (convex_convexHull ℚ (monoid : Set V))
        |>.smul_mem_of_zero_mem
          hzero hboundPoint hratio
    have hscalar :
        coefficient / (bound : ℚ) *
            (bound : ℚ) =
          coefficient := by
      field_simp
    simpa [smul_smul, hscalar] using hscaled
  let cone : ConvexCone ℚ V :=
    { carrier := hullSet
      smul_mem' := by
        intro coefficient hcoefficient point hpoint
        exact hsmul hcoefficient hpoint
      add_mem' := by
        intro left hleft right hright
        exact hadd hleft hright }
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro point hpoint
      induction hpoint using
          AddSubmonoid.closure_induction with
      | mem point hgenerator =>
          exact
            ConvexCone.subset_hull
              (Or.inr hgenerator)
      | zero =>
          exact
            ConvexCone.subset_hull
              (Or.inl rfl)
      | add left right _ _ hleft hright =>
          exact
            (ConvexCone.hull ℚ
              ({0} ∪ generators)).add_mem
              hleft hright
    · exact
        (ConvexCone.hull ℚ
          ({0} ∪ generators)).convex
  · exact
      ConvexCone.hull_min (C := cone)
        fun point hpoint => by
          rcases hpoint with rfl | hgenerator
          · exact hzero
          · exact
              subset_convexHull ℚ (monoid : Set V)
                (AddSubmonoid.subset_closure
                  hgenerator)

/-- Membership in a finitely generated rational cone is equivalent to a
finite nonnegative rational linear combination of its generators. -/
theorem mem_coneHull_finset_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (generators : Finset V) (point : V) :
    point ∈
        (ConvexCone.hull ℚ ({0} ∪ (generators : Set V)) :
          Set V) ↔
      ∃ weights : V → ℚ,
        (∀ generator ∈ generators, 0 ≤ weights generator) ∧
          ∑ generator ∈ generators,
              weights generator • generator =
            point := by
  classical
  let weightedSet : Set V :=
    {candidate |
      ∃ weights : V → ℚ,
        (∀ generator ∈ generators, 0 ≤ weights generator) ∧
          ∑ generator ∈ generators,
              weights generator • generator =
            candidate}
  let weightedCone : ConvexCone ℚ V :=
    { carrier := weightedSet
      smul_mem' := by
        intro coefficient hcoefficient candidate hcandidate
        change
          ∃ weights : V → ℚ,
            (∀ generator ∈ generators, 0 ≤ weights generator) ∧
              ∑ generator ∈ generators,
                  weights generator • generator =
                candidate
          at hcandidate
        change
          ∃ weights : V → ℚ,
            (∀ generator ∈ generators, 0 ≤ weights generator) ∧
              ∑ generator ∈ generators,
                  weights generator • generator =
                coefficient • candidate
        obtain ⟨weights, hweights, hcandidate⟩ := hcandidate
        refine
          ⟨fun generator => coefficient * weights generator,
            ?_, ?_⟩
        · intro generator hgenerator
          exact
            mul_nonneg hcoefficient.le
              (hweights generator hgenerator)
        · simp only [mul_smul]
          rw [← Finset.smul_sum, hcandidate]
      add_mem' := by
        intro left hleft right hright
        change
          ∃ weights : V → ℚ,
            (∀ generator ∈ generators, 0 ≤ weights generator) ∧
              ∑ generator ∈ generators,
                  weights generator • generator =
                left
          at hleft
        change
          ∃ weights : V → ℚ,
            (∀ generator ∈ generators, 0 ≤ weights generator) ∧
              ∑ generator ∈ generators,
                  weights generator • generator =
                right
          at hright
        change
          ∃ weights : V → ℚ,
            (∀ generator ∈ generators, 0 ≤ weights generator) ∧
              ∑ generator ∈ generators,
                  weights generator • generator =
                left + right
        obtain ⟨leftWeights, hleftWeights, hleft⟩ := hleft
        obtain ⟨rightWeights, hrightWeights, hright⟩ := hright
        refine
          ⟨fun generator =>
              leftWeights generator + rightWeights generator,
            ?_, ?_⟩
        · intro generator hgenerator
          exact
            add_nonneg
              (hleftWeights generator hgenerator)
              (hrightWeights generator hgenerator)
        · simp only [add_smul, Finset.sum_add_distrib]
          rw [hleft, hright] }
  constructor
  · apply ConvexCone.hull_min (C := weightedCone)
    intro generator hgenerator
    rcases hgenerator with rfl | hgenerator
    · exact
        ⟨0, by simp, by simp⟩
    · refine
        ⟨fun candidate => if candidate = generator then 1 else 0,
          ?_, ?_⟩
      · intro candidate _
        by_cases hcandidate : candidate = generator <;>
          simp [hcandidate]
      · rw [Finset.sum_eq_single generator]
        · simp
        · intro candidate _ hcandidate
          simp [hcandidate]
        · intro hnot
          exact (hnot hgenerator).elim
  · rintro ⟨weights, hweights, rfl⟩
    let cone :=
      ConvexCone.hull ℚ
        ({0} ∪ (generators : Set V))
    have hsum :
        ∀ selected : Finset V, selected ⊆ generators →
          ∑ generator ∈ selected,
              weights generator • generator ∈ cone := by
      intro selected hselected
      induction selected using Finset.induction with
      | empty =>
          simpa [cone] using
            (ConvexCone.subset_hull
              (s := ({0} ∪ (generators : Set V)))
              (Or.inl rfl))
      | @insert generator selected hnew ih =>
          rw [Finset.sum_insert hnew]
          apply cone.add_mem
          · by_cases hzero : weights generator = 0
            · simpa [hzero, cone] using
                (ConvexCone.subset_hull
                  (s := ({0} ∪ (generators : Set V)))
                  (Or.inl rfl))
            · apply cone.smul_mem
                (lt_of_le_of_ne
                  (hweights generator
                    (hselected (by simp)))
                  (Ne.symm hzero))
              exact
                ConvexCone.subset_hull
                  (Or.inr
                    (hselected (by simp)))
          · exact
              ih fun candidate hcandidate =>
                hselected (by simp [hcandidate])
    exact hsum generators fun _ hmember => hmember

/-- A finite polytope-plus-cone representation is exactly a pair of finite
nonnegative weight systems, with the polytope weights summing to one. -/
theorem mem_convexHull_add_coneHull_finset_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (bases generators : Finset V) (point : V) :
    point ∈
        convexHull ℚ (bases : Set V) +
          (ConvexCone.hull ℚ
            ({0} ∪ (generators : Set V)) : Set V) ↔
      ∃ baseWeights generatorWeights : V → ℚ,
        (∀ base ∈ bases, 0 ≤ baseWeights base) ∧
        (∑ base ∈ bases, baseWeights base) = 1 ∧
        (∀ generator ∈ generators,
          0 ≤ generatorWeights generator) ∧
        (∑ base ∈ bases, baseWeights base • base) +
            (∑ generator ∈ generators,
              generatorWeights generator • generator) =
          point := by
  constructor
  · rintro ⟨basePoint, hbasePoint, direction, hdirection, rfl⟩
    obtain
        ⟨baseWeights, hbaseWeights, hbaseSum, hbasePoint⟩ :=
      (Finset.mem_convexHull').mp hbasePoint
    obtain
        ⟨generatorWeights, hgeneratorWeights, hdirection⟩ :=
      (mem_coneHull_finset_iff generators direction).mp hdirection
    exact
      ⟨baseWeights, generatorWeights, hbaseWeights, hbaseSum,
        hgeneratorWeights, by rw [hbasePoint, hdirection]⟩
  · rintro
      ⟨baseWeights, generatorWeights, hbaseWeights, hbaseSum,
        hgeneratorWeights, rfl⟩
    exact
      ⟨∑ base ∈ bases, baseWeights base • base,
        (Finset.mem_convexHull').mpr
          ⟨baseWeights, hbaseWeights, hbaseSum, rfl⟩,
        ∑ generator ∈ generators,
          generatorWeights generator • generator,
        (mem_coneHull_finset_iff generators _).mpr
          ⟨generatorWeights, hgeneratorWeights, rfl⟩,
        rfl⟩

/-- The rational integer hull is a polytope generated by finitely many
integral points plus a rational cone generated by finitely many integral
recession directions. -/
theorem exists_finite_integerHull_cone_decomposition
    (vars : Finset Nat) (rows : List Le) :
    ∃ bases generators : Finset (Encoding vars rows),
      (∀ base ∈ bases,
        decode base ∈ integerPoints vars rows) ∧
      (∀ generator ∈ generators,
        FiniteIntegral (decode generator) ∧
          decode generator ∈ recessionCone vars rows) ∧
      integerPoints vars rows =
        (decode '' (bases : Set (Encoding vars rows))) +
          (AddSubmonoid.closure
            (decode '' (generators : Set (Encoding vars rows))) :
              Set (FiniteValuation vars)) ∧
      integerHull vars rows =
        convexHull ℚ
            (decode '' (bases : Set (Encoding vars rows))) +
          (ConvexCone.hull ℚ
            ({0} ∪ decode '' (generators : Set (Encoding vars rows))) :
              Set (FiniteValuation vars)) := by
  obtain
      ⟨bases, generators, hbases, hgenerators, hpoints, hhull⟩ :=
    exists_finite_integerHull_decomposition vars rows
  refine
    ⟨bases, generators, hbases, hgenerators, hpoints, ?_⟩
  rw [hhull, convexHull_addSubmonoidClosure_eq_coneHull]

end LeanVIPR.Completeness.IntegerHull
