module

public import LeanVIPR.Completeness.RecessionMonoid
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Order.WellFoundedSet

@[expose] public section

/-!
# Nonnegative encodings of integral feasible points

At a common affine denominator scale, an integral feasible point is represented
by signed natural coordinates and one natural slack coordinate for every row.
These encodings form a fiber of the homogeneous equation map used for recession
directions.
-/

namespace LeanVIPR.Completeness.AffineMonoid

open LeanVIPR.Cert LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.RecessionMonoid
open scoped Pointwise

/-- Nonnegative encodings of integral feasible points at a fixed affine
scale. -/
def affineSolutionSet
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    Set (Encoding vars rows) :=
  {encoding | ∀ rowIndex,
    equation scale encoding rowIndex =
      (scale : ℚ) * (rows.get rowIndex).rhs}

theorem mem_affineSolutionSet_iff
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    {encoding : Encoding vars rows} :
    encoding ∈ affineSolutionSet vars rows scale ↔
      ∀ rowIndex,
        equation scale encoding rowIndex =
          (scale : ℚ) * (rows.get rowIndex).rhs :=
  Iff.rfl

/-- Every affine solution encoding decodes to an integral feasible point. -/
theorem affineSolution_decode_integerPoint
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale : 0 < scale) {encoding : Encoding vars rows}
    (hsolution :
      encoding ∈ affineSolutionSet vars rows scale) :
    decode encoding ∈ integerPoints vars rows := by
  refine ⟨?_, decode_integral encoding⟩
  intro row hrow
  obtain ⟨rowIndex, hrowIndex⟩ := List.get_of_mem hrow
  have hequation := hsolution rowIndex
  rw [equation, hrowIndex] at hequation
  change
    finiteEval vars row.form (decode encoding) ≤ row.rhs
  have hslackNonnegative :
      (0 : ℚ) ≤ (slack encoding rowIndex : ℕ) := by
    positivity
  have hscalePositive : (0 : ℚ) < scale := by
    positivity
  nlinarith

/-- Every integral feasible point has a nonnegative affine solution
encoding. -/
theorem exists_affine_solution_encoding
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hrhs :
      ∀ row ∈ rows,
        IsIntVal ((scale : ℚ) * row.rhs))
    (hrowScale :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a))
    {point : FiniteValuation vars}
    (hpoint : point ∈ integerPoints vars rows) :
    ∃ encoding : Encoding vars rows,
      encoding ∈ affineSolutionSet vars rows scale ∧
      decode encoding = point := by
  have hslacks :=
    exists_feasible_slacks
      hrhs hrowScale hpoint.2 hpoint.1
  choose coordinate hcoordinate using hpoint.2
  have hindexedSlacks :
      ∀ rowIndex : Fin rows.length, ∃ rowSlack : ℕ,
        (scale : ℚ) *
              finiteEval vars
                (rows.get rowIndex).form point +
            (rowSlack : ℚ) =
          (scale : ℚ) *
            (rows.get rowIndex).rhs := by
    intro rowIndex
    exact
      hslacks (rows.get rowIndex)
        (List.get_mem rows rowIndex)
  choose rowSlack hrowSlack using hindexedSlacks
  let encoding : Encoding vars rows := fun coord =>
    match coord with
    | .inl idx => (coordinate idx).toNat
    | .inr (.inl idx) => (-coordinate idx).toNat
    | .inr (.inr rowIndex) => rowSlack rowIndex
  have hdecode : decode encoding = point := by
    funext idx
    have hsplit :
        ((coordinate idx).toNat : ℤ) -
            ((-coordinate idx).toNat : ℤ) =
          coordinate idx := by
      omega
    change
      ((coordinate idx).toNat : ℚ) -
          ((-coordinate idx).toNat : ℚ) =
        point idx
    rw [hcoordinate idx]
    exact_mod_cast hsplit
  refine ⟨encoding, ?_, hdecode⟩
  intro rowIndex
  rw [equation, hdecode]
  exact hrowSlack rowIndex

/-- At a positive affine scale, encodability is equivalent to integral
feasibility. -/
theorem exists_affine_solution_encoding_iff
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale : 0 < scale)
    (hrhs :
      ∀ row ∈ rows,
        IsIntVal ((scale : ℚ) * row.rhs))
    (hrowScale :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a))
    (point : FiniteValuation vars) :
    (∃ encoding : Encoding vars rows,
        encoding ∈ affineSolutionSet vars rows scale ∧
        decode encoding = point) ↔
      point ∈ integerPoints vars rows := by
  constructor
  · rintro ⟨encoding, hsolution, rfl⟩
    exact
      affineSolution_decode_integerPoint
        hscale hsolution
  · exact
      exists_affine_solution_encoding
        hrhs hrowScale

/-- Adding a homogeneous solution to an affine solution preserves the affine
fiber. -/
theorem add_solution_mem_affineSolutionSet
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    {base direction : Encoding vars rows}
    (hbase :
      base ∈ affineSolutionSet vars rows scale)
    (hdirection :
      direction ∈ solutionMonoid vars rows scale) :
    base + direction ∈ affineSolutionSet vars rows scale := by
  intro rowIndex
  rw [equation_add]
  change
    equation scale base rowIndex +
        equation scale direction rowIndex =
      _
  rw [hbase rowIndex]
  rw [(mem_solutionMonoid_iff.mp hdirection) rowIndex]
  simp

/-- Minimal elements of the affine natural-number solution fiber. -/
def minimalAffineEncodings
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    Set (Encoding vars rows) :=
  {encoding |
    Minimal
      (· ∈ affineSolutionSet vars rows scale)
      encoding}

/-- Dickson's lemma makes the set of minimal affine encodings finite. -/
theorem minimalAffineEncodings_finite
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    (minimalAffineEncodings vars rows scale).Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro first hfirst second hsecond hne hle
  have hge : second ≤ first :=
    hsecond.2 hfirst.1 hle
  exact hne (le_antisymm hle hge)

/-- Every affine encoding is a minimal affine encoding plus a homogeneous
solution. -/
theorem exists_minimal_add_solution
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    {encoding : Encoding vars rows}
    (hencoding :
      encoding ∈ affineSolutionSet vars rows scale) :
    ∃ base : Encoding vars rows,
      base ∈ minimalAffineEncodings vars rows scale ∧
      ∃ direction : Encoding vars rows,
        direction ∈ solutionMonoid vars rows scale ∧
        encoding = base + direction := by
  have hpwo :
      (affineSolutionSet vars rows scale).IsPWO :=
    Set.isPWO_of_wellQuasiOrderedLE _
  obtain ⟨base, hbaseLe, hbaseMinimal⟩ :=
    hpwo.exists_le_minimal hencoding
  let direction : Encoding vars rows := fun coord =>
    encoding coord - base coord
  have hsum : base + direction = encoding := by
    funext coord
    have hcoord : base coord ≤ encoding coord :=
      hbaseLe coord
    exact Nat.add_sub_of_le hcoord
  have hdirection :
      direction ∈ solutionMonoid vars rows scale := by
    apply mem_solutionMonoid_iff.mpr
    intro rowIndex
    have hencodingEquation := hencoding rowIndex
    have hbaseEquation := hbaseMinimal.1 rowIndex
    have hadd :=
      congrFun
        (equation_add scale base direction)
        rowIndex
    rw [hsum] at hadd
    change
      equation scale encoding rowIndex =
        equation scale base rowIndex +
          equation scale direction rowIndex
        at hadd
    linarith
  exact
    ⟨base, hbaseMinimal, direction, hdirection,
      hsum.symm⟩

/-- A finite family of minimal affine encodings generates the whole affine
fiber modulo the homogeneous solution monoid. -/
theorem exists_finite_affine_bases
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    ∃ bases : Finset (Encoding vars rows),
      (∀ base ∈ bases,
        base ∈ affineSolutionSet vars rows scale) ∧
      ∀ encoding ∈ affineSolutionSet vars rows scale,
        ∃ base ∈ bases,
          ∃ direction ∈ solutionMonoid vars rows scale,
            encoding = base + direction := by
  let minimalSet :=
    minimalAffineEncodings vars rows scale
  have hfinite : minimalSet.Finite :=
    minimalAffineEncodings_finite vars rows scale
  let bases := hfinite.toFinset
  refine ⟨bases, ?_, ?_⟩
  · intro base hbase
    have hminimal : base ∈ minimalSet := by
      simpa [bases] using hbase
    exact hminimal.1
  · intro encoding hencoding
    obtain
        ⟨base, hbase, direction, hdirection,
          hdecompose⟩ :=
      exists_minimal_add_solution hencoding
    refine
      ⟨base, ?_, direction, hdirection, hdecompose⟩
    simpa [bases, minimalSet] using hbase

/-- Integral feasible points are a finite union of translates of one finitely
generated integral recession monoid. -/
theorem exists_finite_integerPoint_decomposition
    (vars : Finset Nat) (rows : List Le) :
    ∃ bases generators : Finset (Encoding vars rows),
      (∀ base ∈ bases,
        decode base ∈ integerPoints vars rows) ∧
      (∀ generator ∈ generators,
        FiniteIntegral (decode generator) ∧
          decode generator ∈
            recessionCone vars rows) ∧
      ∀ point ∈ integerPoints vars rows,
        ∃ base ∈ bases,
          ∃ direction : FiniteValuation vars,
            direction ∈
              AddSubmonoid.closure
                (decode '' (generators :
                  Set (Encoding vars rows))) ∧
            point = decode base + direction := by
  obtain ⟨scale, hscale, hrhs, hrowScale⟩ :=
    exists_rows_affine_integral_scale vars rows
  obtain ⟨bases, hbases, hbaseGenerate⟩ :=
    exists_finite_affine_bases vars rows scale
  obtain ⟨generatorSet, hgenerators, hfinite⟩ :=
    (AddSubmonoid.fg_iff _).1 (solutionMonoid_fg vars rows scale)
  refine ⟨bases, hfinite.toFinset, ?_, ?_, ?_⟩
  · intro base hbase
    exact
      affineSolution_decode_integerPoint
        hscale (hbases base hbase)
  · intro generator hgenerator
    apply solution_decode_integral_recession hscale
    rw [← hgenerators]
    exact AddSubmonoid.subset_closure (hfinite.mem_toFinset.mp hgenerator)
  · intro point hpoint
    obtain ⟨encoding, hencoding, hdecode⟩ :=
      exists_affine_solution_encoding
        hrhs hrowScale hpoint
    obtain
        ⟨base, hbase, direction, hdirection,
          hdecompose⟩ :=
      hbaseGenerate encoding hencoding
    refine
      ⟨base, hbase, decode direction, ?_, ?_⟩
    · apply decode_mem_closure_image hfinite.toFinset
      rw [Set.Finite.coe_toFinset, hgenerators]
      exact hdirection
    · rw [← hdecode, hdecompose, decode_add]

/-- The finite affine decomposition gives an exact Minkowski-sum description
of the integer points and hence of their convex hull. -/
theorem exists_finite_integerHull_decomposition
    (vars : Finset Nat) (rows : List Le) :
    ∃ bases generators : Finset (Encoding vars rows),
      (∀ base ∈ bases,
        decode base ∈ integerPoints vars rows) ∧
      (∀ generator ∈ generators,
        FiniteIntegral (decode generator) ∧
          decode generator ∈
            recessionCone vars rows) ∧
      integerPoints vars rows =
        (decode '' (bases :
          Set (Encoding vars rows))) +
          (AddSubmonoid.closure
            (decode '' (generators :
              Set (Encoding vars rows))) :
                Set (FiniteValuation vars)) ∧
      integerHull vars rows =
        convexHull ℚ
            (decode '' (bases :
              Set (Encoding vars rows))) +
          convexHull ℚ
            (AddSubmonoid.closure
              (decode '' (generators :
                Set (Encoding vars rows))) :
                  Set (FiniteValuation vars)) := by
  obtain
      ⟨bases, generators, hbases, hgenerators,
        hdecompose⟩ :=
    exists_finite_integerPoint_decomposition vars rows
  have hpoints :
      integerPoints vars rows =
        (decode '' (bases :
          Set (Encoding vars rows))) +
          (AddSubmonoid.closure
            (decode '' (generators :
              Set (Encoding vars rows))) :
                Set (FiniteValuation vars)) := by
    apply Set.Subset.antisymm
    · intro point hpoint
      obtain
          ⟨base, hbase, direction, hdirection,
            hpointEq⟩ :=
        hdecompose point hpoint
      exact
        ⟨decode base, ⟨base, hbase, rfl⟩,
          direction, hdirection, hpointEq.symm⟩
    · rintro point
        ⟨_, ⟨base, hbase, rfl⟩,
          direction, hdirection, rfl⟩
      have hdirectionIntegral :
          FiniteIntegral direction :=
        closure_decode_integral
          (fun generator hgenerator =>
            (hgenerators generator hgenerator).1)
          hdirection
      have hdirectionRecession :
          direction ∈ recessionCone vars rows :=
        closure_decode_recession
          (fun generator hgenerator =>
            (hgenerators generator hgenerator).2)
          hdirection
      simpa using
        add_integral_recession_mem_integerPoints
          (hbases base hbase) hdirectionRecession
          hdirectionIntegral 1
  refine
    ⟨bases, generators, hbases, hgenerators,
      hpoints, ?_⟩
  rw [integerHull, hpoints, convexHull_add]

end LeanVIPR.Completeness.AffineMonoid
