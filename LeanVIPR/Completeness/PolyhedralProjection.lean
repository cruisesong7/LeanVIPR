module

public import LeanVIPR.Completeness.IntegerHull
public import LeanVIPR.Completeness.IntegerProjection
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# Finite extended formulations and rational projection

A finite set of base points and recession generators describes the set
`conv(B) + cone(R)` by nonnegative weight variables.  This file encodes that
description as finitely many sparse rational rows.  Fourier--Motzkin
elimination will then provide a finite halfspace description in the original
coordinates.
-/

namespace LeanVIPR.Completeness.PolyhedralProjection

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.FinitePolyhedron LeanVIPR.Completeness.FourierMotzkin
  LeanVIPR.Completeness.IntegerProjection LeanVIPR.Completeness.RecessionMonoid
open scoped Pointwise

/-- A bound strictly above every original variable index. -/
def freshStart (vars : Finset Nat) : Nat :=
  vars.sum fun idx => idx + 1

theorem mem_lt_freshStart {vars : Finset Nat} {idx : Nat}
    (hidx : idx ∈ vars) :
    idx < freshStart vars := by
  have hsingle :
      idx + 1 ≤ vars.sum (fun candidate => candidate + 1) := by
    exact
      Finset.single_le_sum
        (fun candidate _ => Nat.zero_le (candidate + 1))
        hidx
  unfold freshStart
  omega

/-- Index of one convex-combination weight. -/
def baseWeightIndex (vars : Finset Nat) (idx : Nat) : Nat :=
  freshStart vars + idx

/-- Index of one conical-combination weight. -/
def generatorWeightIndex
    (vars : Finset Nat) (baseCount idx : Nat) : Nat :=
  freshStart vars + baseCount + idx

theorem original_ne_baseWeightIndex
    {vars : Finset Nat} {original idx : Nat}
    (horiginal : original ∈ vars) :
    original ≠ baseWeightIndex vars idx := by
  intro heq
  have hlt := mem_lt_freshStart horiginal
  unfold baseWeightIndex at heq
  omega

theorem original_ne_generatorWeightIndex
    {vars : Finset Nat} {original baseCount idx : Nat}
    (horiginal : original ∈ vars) :
    original ≠ generatorWeightIndex vars baseCount idx := by
  intro heq
  have hlt := mem_lt_freshStart horiginal
  unfold generatorWeightIndex at heq
  omega

/-- Indices of all auxiliary weights in one finite extended formulation. -/
def weightVars (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) : List Nat :=
  (List.range bases.length).map (baseWeightIndex vars) ++
    (List.range generators.length).map
      (generatorWeightIndex vars bases.length)

theorem weightVars_disjoint
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) :
    ∀ idx ∈ weightVars vars bases generators,
      idx ∉ vars := by
  intro idx hidx hvars
  rcases List.mem_append.mp hidx with hbase | hgenerator
  · obtain ⟨weight, _, rfl⟩ := List.mem_map.mp hbase
    exact original_ne_baseWeightIndex hvars rfl
  · obtain ⟨weight, _, rfl⟩ := List.mem_map.mp hgenerator
    exact original_ne_generatorWeightIndex hvars rfl

/-- Eliminating several variables preserves satisfaction by the same
valuation. -/
theorem eliminateMany_sound :
    ∀ (eliminated : List Nat) {rows : List Le} {a : Valuation},
      (∀ row ∈ rows, Le.sat row a) →
      ∀ row ∈ eliminateMany eliminated rows, Le.sat row a := by
  intro eliminated
  induction eliminated with
  | nil =>
      exact fun hrows => hrows
  | cons idx eliminated ih =>
      intro rows a hrows
      exact ih (eliminate_sound hrows)

/-- Sparse terms for the contribution of convex-combination weights to one
original coordinate. -/
def baseWeightTerms (vars : Finset Nat)
    (bases : List (FiniteValuation vars)) (coordinate : vars) : LinForm :=
  List.ofFn (n := bases.length) fun idx =>
    { idx := baseWeightIndex vars idx
      coeff := -(bases.get idx coordinate) }

/-- Sparse terms for the contribution of conical-combination weights to one
original coordinate. -/
def generatorWeightTerms (vars : Finset Nat)
    (baseCount : Nat)
    (generators : List (FiniteValuation vars))
    (coordinate : vars) : LinForm :=
  List.ofFn (n := generators.length) fun idx =>
    { idx := generatorWeightIndex vars baseCount idx
      coeff := -(generators.get idx coordinate) }

/-- The equation saying that one original coordinate equals the corresponding
weighted sum of base points and recession generators. -/
def coordinateForm (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (coordinate : vars) : LinForm :=
  { idx := coordinate, coeff := 1 } ::
    (baseWeightTerms vars bases coordinate ++
      generatorWeightTerms vars bases.length generators coordinate)

/-- Sum of all convex-combination weights. -/
def baseWeightSumForm (vars : Finset Nat)
    (bases : List (FiniteValuation vars)) : LinForm :=
  List.ofFn (n := bases.length) fun idx =>
    { idx := baseWeightIndex vars idx, coeff := 1 }

/-- The one-term form `-weight`. -/
def negBaseWeightForm (vars : Finset Nat)
    (idx : Nat) : LinForm :=
  [{ idx := baseWeightIndex vars idx, coeff := -1 }]

/-- The one-term form `-weight` for a recession generator. -/
def negGeneratorWeightForm (vars : Finset Nat)
    (baseCount idx : Nat) : LinForm :=
  [{ idx := generatorWeightIndex vars baseCount idx, coeff := -1 }]

/-- Encode one rational equality by two `≤` rows. -/
def equalityRows (form : LinForm) (rhs : ℚ) : List Le :=
  [⟨form, rhs⟩, ⟨LinForm.scale (-1) form, -rhs⟩]

theorem sat_equalityRows_iff {form : LinForm} {rhs : ℚ}
    (a : Valuation) :
    (∀ row ∈ equalityRows form rhs, Le.sat row a) ↔
      LinForm.eval form a = rhs := by
  constructor
  · intro hrows
    have hforward := hrows ⟨form, rhs⟩ (by simp [equalityRows])
    have hbackward :=
      hrows ⟨LinForm.scale (-1) form, -rhs⟩
        (by simp [equalityRows])
    simp only [Le.sat, LinForm.eval_scale] at hforward hbackward
    linarith
  · intro heq row hrow
    simp [equalityRows] at hrow
    rcases hrow with rfl | rfl
    · exact heq.le
    · simp [Le.sat, heq]

@[simp]
theorem eval_baseWeightTerms
    (vars : Finset Nat)
    (bases : List (FiniteValuation vars))
    (coordinate : vars) (a : Valuation) :
    LinForm.eval (baseWeightTerms vars bases coordinate) a =
      ∑ idx : Fin bases.length,
        -(bases.get idx coordinate) *
          a (baseWeightIndex vars idx) := by
  unfold baseWeightTerms LinForm.eval
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

@[simp]
theorem eval_generatorWeightTerms
    (vars : Finset Nat) (baseCount : Nat)
    (generators : List (FiniteValuation vars))
    (coordinate : vars) (a : Valuation) :
    LinForm.eval
        (generatorWeightTerms vars baseCount generators coordinate) a =
      ∑ idx : Fin generators.length,
        -(generators.get idx coordinate) *
          a (generatorWeightIndex vars baseCount idx) := by
  unfold generatorWeightTerms LinForm.eval
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

@[simp]
theorem eval_coordinateForm
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (coordinate : vars) (a : Valuation) :
    LinForm.eval (coordinateForm vars bases generators coordinate) a =
      a coordinate -
        ∑ idx : Fin bases.length,
          a (baseWeightIndex vars idx) * bases.get idx coordinate -
        ∑ idx : Fin generators.length,
          a (generatorWeightIndex vars bases.length idx) *
            generators.get idx coordinate := by
  change
    1 * a coordinate +
        LinForm.eval
          (baseWeightTerms vars bases coordinate ++
            generatorWeightTerms vars bases.length generators coordinate) a =
      _
  rw [LinForm.eval_append, eval_baseWeightTerms,
    eval_generatorWeightTerms]
  have hbase :
      (∑ idx : Fin bases.length,
          -bases.get idx coordinate *
            a (baseWeightIndex vars idx)) =
        -(∑ idx : Fin bases.length,
          a (baseWeightIndex vars idx) * bases.get idx coordinate) := by
    calc
      (∑ idx : Fin bases.length,
          -bases.get idx coordinate *
            a (baseWeightIndex vars idx)) =
          ∑ idx : Fin bases.length,
            -(bases.get idx coordinate *
              a (baseWeightIndex vars idx)) := by
            apply Finset.sum_congr rfl
            intro idx _
            ring
      _ = -(∑ idx : Fin bases.length,
          bases.get idx coordinate *
            a (baseWeightIndex vars idx)) := by
            rw [Finset.sum_neg_distrib]
      _ = -(∑ idx : Fin bases.length,
          a (baseWeightIndex vars idx) *
            bases.get idx coordinate) := by
            congr 1
            apply Finset.sum_congr rfl
            intro idx _
            ring
  have hgenerators :
      (∑ idx : Fin generators.length,
          -generators.get idx coordinate *
            a (generatorWeightIndex vars bases.length idx)) =
        -(∑ idx : Fin generators.length,
          a (generatorWeightIndex vars bases.length idx) *
            generators.get idx coordinate) := by
    calc
      (∑ idx : Fin generators.length,
          -generators.get idx coordinate *
            a (generatorWeightIndex vars bases.length idx)) =
          ∑ idx : Fin generators.length,
            -(generators.get idx coordinate *
              a (generatorWeightIndex vars bases.length idx)) := by
            apply Finset.sum_congr rfl
            intro idx _
            ring
      _ = -(∑ idx : Fin generators.length,
          generators.get idx coordinate *
            a (generatorWeightIndex vars bases.length idx)) := by
            rw [Finset.sum_neg_distrib]
      _ = -(∑ idx : Fin generators.length,
          a (generatorWeightIndex vars bases.length idx) *
            generators.get idx coordinate) := by
            congr 1
            apply Finset.sum_congr rfl
            intro idx _
            ring
  rw [hbase, hgenerators]
  ring

@[simp]
theorem eval_baseWeightSumForm
    (vars : Finset Nat)
    (bases : List (FiniteValuation vars)) (a : Valuation) :
    LinForm.eval (baseWeightSumForm vars bases) a =
      ∑ idx : Fin bases.length, a (baseWeightIndex vars idx) := by
  unfold baseWeightSumForm LinForm.eval
  rw [List.map_ofFn, List.sum_ofFn]
  simp

/-- Point represented by the auxiliary weights of a valuation. -/
def weightedPoint (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (a : Valuation) : FiniteValuation vars :=
  fun coordinate =>
    (∑ idx : Fin bases.length,
      a (baseWeightIndex vars idx) * bases.get idx coordinate) +
    ∑ idx : Fin generators.length,
      a (generatorWeightIndex vars bases.length idx) *
        generators.get idx coordinate

/-- Coordinate equations of the finite extended formulation. -/
noncomputable def coordinateRows (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) : List Le :=
  vars.attach.toList.flatMap fun coordinate =>
    equalityRows (coordinateForm vars bases generators coordinate) 0

/-- The equation that convex-combination weights sum to one. -/
def baseWeightSumRows (vars : Finset Nat)
    (bases : List (FiniteValuation vars)) : List Le :=
  equalityRows (baseWeightSumForm vars bases) 1

/-- Nonnegativity rows for convex-combination weights. -/
def baseWeightNonnegativeRows (vars : Finset Nat)
    (bases : List (FiniteValuation vars)) : List Le :=
  (List.range bases.length).map fun idx =>
    ⟨negBaseWeightForm vars idx, 0⟩

/-- Nonnegativity rows for conical-combination weights. -/
def generatorWeightNonnegativeRows (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) : List Le :=
  (List.range generators.length).map fun idx =>
    ⟨negGeneratorWeightForm vars bases.length idx, 0⟩

/-- A rational extended formulation for the finite polytope plus cone. -/
noncomputable def extendedRows (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) : List Le :=
  coordinateRows vars bases generators ++
    baseWeightSumRows vars bases ++
    baseWeightNonnegativeRows vars bases ++
    generatorWeightNonnegativeRows vars bases generators

theorem sat_coordinateRows_iff
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (a : Valuation) :
    (∀ row ∈ coordinateRows vars bases generators, Le.sat row a) ↔
      restrictValuation (vars := vars) a =
        weightedPoint vars bases generators a := by
  constructor
  · intro hrows
    funext coordinate
    have hequality :
        ∀ row ∈
            equalityRows
              (coordinateForm vars bases generators coordinate) 0,
          Le.sat row a := by
      intro row hrow
      apply hrows row
      apply List.mem_flatMap.mpr
      exact ⟨coordinate, by simp, hrow⟩
    have hform :=
      (sat_equalityRows_iff a).mp hequality
    rw [eval_coordinateForm] at hform
    change a coordinate =
      weightedPoint vars bases generators a coordinate
    unfold weightedPoint
    linarith
  · intro hpoint row hrow
    obtain ⟨coordinate, _, hrow⟩ :=
      List.mem_flatMap.mp hrow
    have hcoordinate := congrFun hpoint coordinate
    change a coordinate =
      weightedPoint vars bases generators a coordinate
      at hcoordinate
    unfold weightedPoint at hcoordinate
    have hform :
        LinForm.eval
            (coordinateForm vars bases generators coordinate) a =
          0 := by
      rw [eval_coordinateForm, hcoordinate]
      ring
    exact ((sat_equalityRows_iff a).mpr hform) row hrow

theorem sat_baseWeightSumRows_iff
    (vars : Finset Nat)
    (bases : List (FiniteValuation vars))
    (a : Valuation) :
    (∀ row ∈ baseWeightSumRows vars bases, Le.sat row a) ↔
      (∑ idx : Fin bases.length,
        a (baseWeightIndex vars idx)) = 1 := by
  rw [baseWeightSumRows, sat_equalityRows_iff,
    eval_baseWeightSumForm]

theorem sat_baseWeightNonnegativeRows_iff
    (vars : Finset Nat)
    (bases : List (FiniteValuation vars))
    (a : Valuation) :
    (∀ row ∈ baseWeightNonnegativeRows vars bases, Le.sat row a) ↔
      ∀ idx : Fin bases.length,
        0 ≤ a (baseWeightIndex vars idx) := by
  constructor
  · intro hrows idx
    have hrow :=
      hrows ⟨negBaseWeightForm vars idx, 0⟩
        (List.mem_map.mpr
          ⟨idx, List.mem_range.mpr idx.isLt, rfl⟩)
    simpa [Le.sat, negBaseWeightForm, LinForm.eval] using hrow
  · intro hweights row hrow
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hrow
    have hlt := List.mem_range.mp hidx
    simpa [Le.sat, negBaseWeightForm, LinForm.eval] using
      hweights ⟨idx, hlt⟩

theorem sat_generatorWeightNonnegativeRows_iff
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (a : Valuation) :
    (∀ row ∈ generatorWeightNonnegativeRows vars bases generators,
        Le.sat row a) ↔
      ∀ idx : Fin generators.length,
        0 ≤ a (generatorWeightIndex vars bases.length idx) := by
  constructor
  · intro hrows idx
    have hrow :=
      hrows
        ⟨negGeneratorWeightForm vars bases.length idx, 0⟩
        (List.mem_map.mpr
          ⟨idx, List.mem_range.mpr idx.isLt, rfl⟩)
    simpa [Le.sat, negGeneratorWeightForm, LinForm.eval] using hrow
  · intro hweights row hrow
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hrow
    have hlt := List.mem_range.mp hidx
    simpa [Le.sat, negGeneratorWeightForm, LinForm.eval] using
      hweights ⟨idx, hlt⟩

theorem sat_extendedRows_iff
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (a : Valuation) :
    (∀ row ∈ extendedRows vars bases generators, Le.sat row a) ↔
      restrictValuation (vars := vars) a =
          weightedPoint vars bases generators a ∧
        (∑ idx : Fin bases.length,
          a (baseWeightIndex vars idx)) = 1 ∧
        (∀ idx : Fin bases.length,
          0 ≤ a (baseWeightIndex vars idx)) ∧
        ∀ idx : Fin generators.length,
          0 ≤ a
            (generatorWeightIndex vars bases.length idx) := by
  constructor
  · intro hrows
    have hcoordinate :
        ∀ row ∈ coordinateRows vars bases generators,
          Le.sat row a := by
      intro row hrow
      exact hrows row (by simp [extendedRows, hrow])
    have hsum :
        ∀ row ∈ baseWeightSumRows vars bases,
          Le.sat row a := by
      intro row hrow
      exact hrows row (by simp [extendedRows, hrow])
    have hbase :
        ∀ row ∈ baseWeightNonnegativeRows vars bases,
          Le.sat row a := by
      intro row hrow
      exact hrows row (by simp [extendedRows, hrow])
    have hgenerators :
        ∀ row ∈
            generatorWeightNonnegativeRows vars bases generators,
          Le.sat row a := by
      intro row hrow
      exact hrows row (by simp [extendedRows, hrow])
    exact
      ⟨(sat_coordinateRows_iff vars bases generators a).mp hcoordinate,
        (sat_baseWeightSumRows_iff vars bases a).mp hsum,
        (sat_baseWeightNonnegativeRows_iff vars bases a).mp hbase,
        (sat_generatorWeightNonnegativeRows_iff
          vars bases generators a).mp hgenerators⟩
  · rintro ⟨hcoordinate, hsum, hbase, hgenerators⟩
    intro row hrow
    unfold extendedRows at hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · rcases List.mem_append.mp hrow with hrow | hrow
      · rcases List.mem_append.mp hrow with hrow | hrow
        · exact
            (sat_coordinateRows_iff vars bases generators a).mpr
              hcoordinate row hrow
        · exact
            (sat_baseWeightSumRows_iff vars bases a).mpr
              hsum row hrow
      · exact
          (sat_baseWeightNonnegativeRows_iff vars bases a).mpr
            hbase row hrow
    · exact
        (sat_generatorWeightNonnegativeRows_iff
          vars bases generators a).mpr
            hgenerators row hrow

/-- All original and auxiliary indices used by the extended formulation. -/
noncomputable def extendedSupport (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) : List Nat :=
  vars.toList ++ weightVars vars bases generators

theorem baseWeightIndex_mem_weightVars
    {vars : Finset Nat}
    {bases generators : List (FiniteValuation vars)}
    (idx : Fin bases.length) :
    baseWeightIndex vars idx ∈ weightVars vars bases generators := by
  apply List.mem_append.mpr
  left
  exact
    List.mem_map.mpr
      ⟨idx, List.mem_range.mpr idx.isLt, rfl⟩

theorem generatorWeightIndex_mem_weightVars
    {vars : Finset Nat}
    {bases generators : List (FiniteValuation vars)}
    (idx : Fin generators.length) :
    generatorWeightIndex vars bases.length idx ∈
      weightVars vars bases generators := by
  apply List.mem_append.mpr
  right
  exact
    List.mem_map.mpr
      ⟨idx, List.mem_range.mpr idx.isLt, rfl⟩

theorem coordinateForm_supported
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (coordinate : vars) :
    ∀ term ∈ coordinateForm vars bases generators coordinate,
      term.idx ∈ extendedSupport vars bases generators := by
  intro term hterm
  simp only [coordinateForm, List.mem_cons, List.mem_append] at hterm
  rcases hterm with rfl | hterm
  · apply List.mem_append.mpr
    left
    simpa using coordinate.property
  · apply List.mem_append.mpr
    right
    rcases hterm with hterm | hterm
    · obtain ⟨idx, rfl⟩ := List.mem_ofFn.mp hterm
      exact baseWeightIndex_mem_weightVars idx
    · obtain ⟨idx, rfl⟩ := List.mem_ofFn.mp hterm
      exact generatorWeightIndex_mem_weightVars idx

theorem baseWeightSumForm_supported
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) :
    ∀ term ∈ baseWeightSumForm vars bases,
      term.idx ∈ extendedSupport vars bases generators := by
  intro term hterm
  obtain ⟨idx, rfl⟩ := List.mem_ofFn.mp hterm
  apply List.mem_append.mpr
  right
  exact baseWeightIndex_mem_weightVars idx

theorem equalityRows_supported
    {support : List Nat} {form : LinForm} {rhs : ℚ}
    (hform : ∀ term ∈ form, term.idx ∈ support) :
    FarkasCompleteness.RowsSupported support
      (equalityRows form rhs) := by
  intro row hrow term hterm
  simp [equalityRows] at hrow
  rcases hrow with rfl | rfl
  · exact hform term hterm
  · obtain ⟨source, hsource, hidx⟩ :=
      mem_scale_index hterm
    rw [hidx]
    exact hform source hsource

theorem extendedRows_supported
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) :
    FarkasCompleteness.RowsSupported
      (extendedSupport vars bases generators)
      (extendedRows vars bases generators) := by
  intro row hrow term hterm
  unfold extendedRows at hrow
  rcases List.mem_append.mp hrow with hrow | hrow
  · rcases List.mem_append.mp hrow with hrow | hrow
    · rcases List.mem_append.mp hrow with hrow | hrow
      · obtain ⟨coordinate, _, hrow⟩ :=
          List.mem_flatMap.mp hrow
        exact
          equalityRows_supported
            (coordinateForm_supported vars bases generators coordinate)
            row hrow term hterm
      · exact
          equalityRows_supported
            (baseWeightSumForm_supported vars bases generators)
            row hrow term hterm
    · obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hrow
      simp only [negBaseWeightForm, List.mem_cons,
        List.not_mem_nil, or_false] at hterm
      subst term
      apply List.mem_append.mpr
      right
      exact
        baseWeightIndex_mem_weightVars
          ⟨idx, List.mem_range.mp hidx⟩
  · obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hrow
    simp only [negGeneratorWeightForm, List.mem_cons,
      List.not_mem_nil, or_false] at hterm
    subst term
    apply List.mem_append.mpr
    right
    exact
      generatorWeightIndex_mem_weightVars
        ⟨idx, List.mem_range.mp hidx⟩

/-- Eliminate all auxiliary weights and canonicalize the surviving sparse
forms. -/
noncomputable def projectedExtendedRows (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) : List Le :=
  (eliminateMany (weightVars vars bases generators)
    (extendedRows vars bases generators)).map canonicalRow

theorem projectedExtendedRows_supported
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars)) :
    FinitePolyhedron.RowsSupported vars
      (projectedExtendedRows vars bases generators) := by
  intro row hrow term hterm
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hrow
  have hdata := mem_canonicalForm hterm
  have hcoeff : coeffAt term.idx raw.form ≠ 0 := by
    intro hzero
    exact hdata.2 (hdata.1.trans hzero)
  obtain ⟨source, hsource, hsourceIdx⟩ :=
    coeffAt_ne_zero_has_term hcoeff
  have heliminatedSupported :
      FarkasCompleteness.RowsSupported
        (extendedSupport vars bases generators)
        (eliminateMany (weightVars vars bases generators)
          (extendedRows vars bases generators)) :=
    eliminateMany_supported _
      (extendedRows_supported vars bases generators)
  have hsupport :=
    heliminatedSupported raw hraw source hsource
  unfold extendedSupport at hsupport
  rcases List.mem_append.mp hsupport with horiginal | hweight
  · simpa [hsourceIdx] using horiginal
  · have hzero :=
      eliminateMany_coeff_zero_of_mem hweight raw hraw
    rw [hsourceIdx] at hzero
    exact (hdata.2 (hdata.1.trans hzero)).elim

/-- Positional nonnegative weights representing one point in a finite
polytope plus cone. -/
def HasWeightRepresentation
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars) : Prop :=
  ∃ baseWeights : Fin bases.length → ℚ,
    ∃ generatorWeights : Fin generators.length → ℚ,
      (∀ idx, 0 ≤ baseWeights idx) ∧
      (∑ idx, baseWeights idx) = 1 ∧
      (∀ idx, 0 ≤ generatorWeights idx) ∧
      point =
        fun coordinate =>
          (∑ idx,
            baseWeights idx * bases.get idx coordinate) +
          ∑ idx,
            generatorWeights idx *
              generators.get idx coordinate

/-- Combine an original point and two finite weight vectors into one global
valuation using the fresh auxiliary indices. -/
def representationValuation
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars)
    (baseWeights : Fin bases.length → ℚ)
    (generatorWeights : Fin generators.length → ℚ) :
    Valuation :=
  fun idx =>
    if hvars : idx ∈ vars then
      point ⟨idx, hvars⟩
    else
      let offset := idx - freshStart vars
      if hbase : offset < bases.length then
        baseWeights ⟨offset, hbase⟩
      else
        let generatorOffset := offset - bases.length
        if hgenerator : generatorOffset < generators.length then
          generatorWeights ⟨generatorOffset, hgenerator⟩
        else
          0

@[simp]
theorem representationValuation_original
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars)
    (baseWeights : Fin bases.length → ℚ)
    (generatorWeights : Fin generators.length → ℚ)
    (coordinate : vars) :
    representationValuation vars bases generators point
        baseWeights generatorWeights coordinate =
      point coordinate := by
  simp [representationValuation, coordinate.property]

@[simp]
theorem representationValuation_baseWeight
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars)
    (baseWeights : Fin bases.length → ℚ)
    (generatorWeights : Fin generators.length → ℚ)
    (idx : Fin bases.length) :
    representationValuation vars bases generators point
        baseWeights generatorWeights
        (baseWeightIndex vars idx) =
      baseWeights idx := by
  have hnot :
      baseWeightIndex vars idx ∉ vars := by
    intro hmem
    exact original_ne_baseWeightIndex hmem rfl
  have hoffset :
      baseWeightIndex vars idx - freshStart vars = idx := by
    unfold baseWeightIndex
    omega
  simp [representationValuation, hnot, hoffset, idx.isLt]

@[simp]
theorem representationValuation_generatorWeight
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars)
    (baseWeights : Fin bases.length → ℚ)
    (generatorWeights : Fin generators.length → ℚ)
    (idx : Fin generators.length) :
    representationValuation vars bases generators point
        baseWeights generatorWeights
        (generatorWeightIndex vars bases.length idx) =
      generatorWeights idx := by
  have hnot :
      generatorWeightIndex vars bases.length idx ∉ vars := by
    intro hmem
    exact original_ne_generatorWeightIndex hmem rfl
  have hoffset :
      generatorWeightIndex vars bases.length idx -
          freshStart vars =
        bases.length + idx := by
    unfold generatorWeightIndex
    omega
  have hnotBase : ¬bases.length + idx < bases.length := by
    omega
  have hgeneratorOffset :
      bases.length + idx - bases.length = idx := by
    omega
  simp [representationValuation, hnot, hoffset, hnotBase,
    hgeneratorOffset, idx.isLt]

theorem hasWeightRepresentation_iff_exists_extended
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars) :
    HasWeightRepresentation vars bases generators point ↔
      ∃ a : Valuation,
        restrictValuation (vars := vars) a = point ∧
          ∀ row ∈ extendedRows vars bases generators,
            Le.sat row a := by
  constructor
  · rintro
      ⟨baseWeights, generatorWeights, hbase, hsum,
        hgenerators, hpoint⟩
    let a :=
      representationValuation vars bases generators point
        baseWeights generatorWeights
    refine ⟨a, ?_, ?_⟩
    · funext coordinate
      simp [a, restrictValuation]
    · apply
        (sat_extendedRows_iff vars bases generators a).mpr
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show restrictValuation (vars := vars) a = point by
          funext coordinate
          simp [a, restrictValuation]]
        rw [hpoint]
        funext coordinate
        simp [weightedPoint, a]
      · simpa [a] using hsum
      · intro idx
        simpa [a] using hbase idx
      · intro idx
        simpa [a] using hgenerators idx
  · rintro ⟨a, hpoint, hrows⟩
    have hdata :=
      (sat_extendedRows_iff vars bases generators a).mp hrows
    refine
      ⟨fun idx => a (baseWeightIndex vars idx),
        fun idx =>
          a (generatorWeightIndex vars bases.length idx),
        hdata.2.2.1, hdata.2.1, hdata.2.2.2, ?_⟩
    rw [← hpoint, hdata.1]
    rfl

/-- The finite rows obtained by Fourier--Motzkin elimination define exactly
the points represented by the original finite bases and generators. -/
theorem mem_projectedExtendedRows_iff
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (point : FiniteValuation vars) :
    point ∈
        polyhedron vars
          (projectedExtendedRows vars bases generators) ↔
      HasWeightRepresentation vars bases generators point := by
  constructor
  · intro hprojected
    have heliminated :
        ∀ row ∈
            eliminateMany (weightVars vars bases generators)
              (extendedRows vars bases generators),
          Le.sat row (extendValuation point) := by
      intro row hrow
      have hcanonical :
          FiniteSat vars (canonicalRow row) point :=
        hprojected (canonicalRow row)
          (List.mem_map.mpr ⟨row, hrow, rfl⟩)
      exact
        (canonicalRow_sat_iff row (extendValuation point)).mp
          hcanonical
    obtain ⟨a, hextended, hagree⟩ :=
      eliminateMany_complete_agree
        (weightVars vars bases generators)
        vars.toList
        (extendedRows vars bases generators)
        (extendValuation point)
        (fun idx hidx hvars =>
          weightVars_disjoint vars bases generators idx hidx
            (by simpa using hvars))
        heliminated
    apply
      (hasWeightRepresentation_iff_exists_extended
        vars bases generators point).mpr
    refine ⟨a, ?_, hextended⟩
    funext coordinate
    rw [restrictValuation]
    rw [hagree coordinate (by simpa using coordinate.property)]
    exact congrFun (restrict_extend point) coordinate
  · intro hrepresentation
    obtain ⟨a, hpoint, hextended⟩ :=
      (hasWeightRepresentation_iff_exists_extended
        vars bases generators point).mp hrepresentation
    have heliminated :=
      eliminateMany_sound
        (weightVars vars bases generators) hextended
    intro row hrow
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hrow
    have hcanonical :
        Le.sat (canonicalRow raw) a :=
      (canonicalRow_sat_iff raw a).mpr
        (heliminated raw hraw)
    change
      finiteEval vars (canonicalRow raw).form point ≤
        (canonicalRow raw).rhs
    rw [← hpoint]
    rw [finiteEval_restrict
      (projectedExtendedRows_supported vars bases generators
        (canonicalRow raw)
        (List.mem_map.mpr ⟨raw, hraw, rfl⟩))]
    exact hcanonical

theorem sum_fin_get_eq_toFinset
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (values : List α) (hvalues : values.Nodup) (f : α → M) :
    (∑ idx : Fin values.length, f (values.get idx)) =
      ∑ value ∈ values.toFinset, f value := by
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]
  exact (List.sum_toFinset f hvalues).symm

/-- Positional weights over a duplicate-free enumeration are equivalent to
the usual finite polytope-plus-cone semantics. -/
theorem hasWeightRepresentation_iff_mem_convexHull_add_coneHull
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (hbases : bases.Nodup) (hgenerators : generators.Nodup)
    (point : FiniteValuation vars) :
    HasWeightRepresentation vars bases generators point ↔
      point ∈
        convexHull ℚ (bases.toFinset : Set (FiniteValuation vars)) +
          (ConvexCone.hull ℚ
            ({0} ∪
              (generators.toFinset :
                Set (FiniteValuation vars))) :
              Set (FiniteValuation vars)) := by
  classical
  constructor
  · rintro
      ⟨baseWeights, generatorWeights, hbaseWeights, hbaseSum,
        hgeneratorWeights, hpoint⟩
    let basePoint : FiniteValuation vars :=
      ∑ idx : Fin bases.length,
        baseWeights idx • bases.get idx
    let generatorPoint : FiniteValuation vars :=
      ∑ idx : Fin generators.length,
        generatorWeights idx • generators.get idx
    have hbasePoint :
        basePoint ∈
          convexHull ℚ
            (bases.toFinset : Set (FiniteValuation vars)) := by
      apply
        mem_convexHull_of_exists_fintype
          baseWeights (fun idx => bases.get idx)
          hbaseWeights hbaseSum
      · intro idx
        simpa using List.get_mem bases idx
      · rfl
    have hgeneratorPoint :
        generatorPoint ∈
          (ConvexCone.hull ℚ
            ({0} ∪
              (generators.toFinset :
                Set (FiniteValuation vars))) :
              Set (FiniteValuation vars)) := by
      let cone :=
        ConvexCone.hull ℚ
          ({0} ∪
            (generators.toFinset :
              Set (FiniteValuation vars)))
      have hsum :
          ∀ selected : Finset (Fin generators.length),
            ∑ idx ∈ selected,
                generatorWeights idx • generators.get idx ∈ cone := by
        intro selected
        induction selected using Finset.induction with
        | empty =>
            simpa [cone] using
              (ConvexCone.subset_hull
                (s := ({0} ∪
                  (generators.toFinset :
                    Set (FiniteValuation vars))))
                (Or.inl rfl))
        | @insert idx selected hidx ih =>
            rw [Finset.sum_insert hidx]
            apply cone.add_mem
            · by_cases hzero : generatorWeights idx = 0
              · simpa [hzero, cone] using
                  (ConvexCone.subset_hull
                    (s := ({0} ∪
                      (generators.toFinset :
                        Set (FiniteValuation vars))))
                    (Or.inl rfl))
              · apply cone.smul_mem
                  (lt_of_le_of_ne
                    (hgeneratorWeights idx)
                    (Ne.symm hzero))
                exact
                  ConvexCone.subset_hull
                    (Or.inr (by
                      simpa using List.get_mem generators idx))
            · exact ih
      change generatorPoint ∈ cone
      simpa [generatorPoint] using hsum Finset.univ
    refine
      ⟨basePoint, hbasePoint, generatorPoint, hgeneratorPoint, ?_⟩
    funext coordinate
    change
      basePoint coordinate + generatorPoint coordinate =
        point coordinate
    rw [hpoint]
    simp [basePoint, generatorPoint, smul_eq_mul]
  · rintro
      ⟨basePoint, hbasePoint, generatorPoint, hgeneratorPoint, rfl⟩
    obtain
        ⟨baseWeights, hbaseWeights, hbaseSum, hbasePoint⟩ :=
      (Finset.mem_convexHull').mp hbasePoint
    obtain
        ⟨generatorWeights, hgeneratorWeights, hgeneratorPoint⟩ :=
      (IntegerHull.mem_coneHull_finset_iff
        generators.toFinset generatorPoint).mp hgeneratorPoint
    refine
      ⟨fun idx => baseWeights (bases.get idx),
        fun idx => generatorWeights (generators.get idx),
        ?_, ?_, ?_, ?_⟩
    · intro idx
      exact
        hbaseWeights (bases.get idx)
          (by simpa using List.get_mem bases idx)
    · rw [sum_fin_get_eq_toFinset bases hbases]
      exact hbaseSum
    · intro idx
      exact
        hgeneratorWeights (generators.get idx)
          (by simpa using List.get_mem generators idx)
    · funext coordinate
      have hbaseVector :
          (∑ idx : Fin bases.length,
              baseWeights (bases.get idx) • bases.get idx) =
            basePoint := by
        calc
          (∑ idx : Fin bases.length,
              baseWeights (bases.get idx) • bases.get idx) =
              ∑ value ∈ bases.toFinset,
                baseWeights value • value :=
            sum_fin_get_eq_toFinset bases hbases
              (fun value => baseWeights value • value)
          _ = basePoint := hbasePoint
      have hgeneratorVector :
          (∑ idx : Fin generators.length,
              generatorWeights (generators.get idx) •
                generators.get idx) =
            generatorPoint := by
        calc
          (∑ idx : Fin generators.length,
              generatorWeights (generators.get idx) •
                generators.get idx) =
              ∑ value ∈ generators.toFinset,
                generatorWeights value • value :=
            sum_fin_get_eq_toFinset generators hgenerators
              (fun value => generatorWeights value • value)
          _ = generatorPoint := hgeneratorPoint
      have hbaseCoordinate :=
        congrFun hbaseVector coordinate
      have hgeneratorCoordinate :=
        congrFun hgeneratorVector coordinate
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        at hbaseCoordinate hgeneratorCoordinate
      change
        basePoint coordinate + generatorPoint coordinate =
          (∑ idx : Fin bases.length,
            baseWeights (bases.get idx) *
              bases.get idx coordinate) +
          ∑ idx : Fin generators.length,
            generatorWeights (generators.get idx) *
              generators.get idx coordinate
      rw [← hbaseCoordinate, ← hgeneratorCoordinate]

/-- Fourier--Motzkin projection turns a duplicate-free finite V-description
into an exact finite H-description. -/
theorem polyhedron_projectedExtendedRows_eq
    (vars : Finset Nat)
    (bases generators : List (FiniteValuation vars))
    (hbases : bases.Nodup) (hgenerators : generators.Nodup) :
    polyhedron vars (projectedExtendedRows vars bases generators) =
      convexHull ℚ
          (bases.toFinset : Set (FiniteValuation vars)) +
        (ConvexCone.hull ℚ
          ({0} ∪
            (generators.toFinset :
              Set (FiniteValuation vars))) :
            Set (FiniteValuation vars)) := by
  ext point
  rw [mem_projectedExtendedRows_iff]
  exact
    hasWeightRepresentation_iff_mem_convexHull_add_coneHull
      vars bases generators hbases hgenerators point

/-- Every rational integer hull has an exact finite rational halfspace
description. -/
theorem exists_finite_integerHull_rows
    (vars : Finset Nat) (rows : List Le) :
    ∃ hullRows : List Le,
      FinitePolyhedron.RowsSupported vars hullRows ∧
      integerHull vars rows =
        polyhedron vars hullRows := by
  obtain
      ⟨bases, generators, _, _, _, hhull⟩ :=
    IntegerHull.exists_finite_integerHull_cone_decomposition vars rows
  let basePoints : Finset (FiniteValuation vars) :=
    bases.image decode
  let generatorPoints : Finset (FiniteValuation vars) :=
    generators.image decode
  let baseList := basePoints.toList
  let generatorList := generatorPoints.toList
  let hullRows :=
    projectedExtendedRows vars baseList generatorList
  refine
    ⟨hullRows,
      projectedExtendedRows_supported vars baseList generatorList,
      ?_⟩
  have hprojected :=
    polyhedron_projectedExtendedRows_eq
      vars baseList generatorList
      basePoints.nodup_toList generatorPoints.nodup_toList
  rw [hhull]
  symm
  simpa [hullRows, baseList, generatorList, basePoints,
    generatorPoints] using hprojected

end LeanVIPR.Completeness.PolyhedralProjection
