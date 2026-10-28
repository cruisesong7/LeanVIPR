module

public import LeanVIPR.Completeness.FinitePolyhedron
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

/-!
# Nonnegative encodings of integral recession directions

Gordan's lemma applies to additive submonoids of finite powers of the natural
numbers. An integral recession direction may have signed coordinates, so this
file represents each coordinate as the difference of two natural numbers and
reserves one further natural coordinate for every row slack.
-/

namespace LeanVIPR.Completeness.RecessionMonoid

open LeanVIPR.Cert LeanVIPR.Completeness.FinitePolyhedron

/-- Positive coordinates, negative coordinates, and one slack coordinate for
each row occurrence. -/
abbrev Coordinate (vars : Finset Nat) (rows : List Le) :=
  Sum vars (Sum vars (Fin rows.length))

/-- A finite nonnegative encoding used by the Gordan-lemma construction. -/
abbrev Encoding (vars : Finset Nat) (rows : List Le) :=
  Coordinate vars rows → ℕ

def positive {vars : Finset Nat} {rows : List Le}
    (encoding : Encoding vars rows) (idx : vars) : ℕ :=
  encoding (.inl idx)

def negative {vars : Finset Nat} {rows : List Le}
    (encoding : Encoding vars rows) (idx : vars) : ℕ :=
  encoding (.inr (.inl idx))

def slack {vars : Finset Nat} {rows : List Le}
    (encoding : Encoding vars rows) (idx : Fin rows.length) : ℕ :=
  encoding (.inr (.inr idx))

/-- Decode the signed coordinates; row slacks do not affect the direction. -/
def decode {vars : Finset Nat} {rows : List Le}
    (encoding : Encoding vars rows) : FiniteValuation vars :=
  fun idx =>
    (positive encoding idx : ℚ) -
      (negative encoding idx : ℚ)

@[simp]
theorem decode_zero (vars : Finset Nat) (rows : List Le) :
    decode (0 : Encoding vars rows) = 0 := by
  funext idx
  simp [decode, positive, negative]

@[simp]
theorem decode_add {vars : Finset Nat} {rows : List Le}
    (left right : Encoding vars rows) :
    decode (left + right) = decode left + decode right := by
  funext idx
  simp [decode, positive, negative]
  ring

/-- Decoding is an additive homomorphism from nonnegative encodings to
rational directions. -/
def decodeHom (vars : Finset Nat) (rows : List Le) :
    Encoding vars rows →+ FiniteValuation vars where
  toFun := decode
  map_zero' := decode_zero vars rows
  map_add' := decode_add

@[simp]
theorem decodeHom_apply {vars : Finset Nat} {rows : List Le}
    (encoding : Encoding vars rows) :
    decodeHom vars rows encoding = decode encoding :=
  rfl

/-- Every decoded direction is coordinatewise integral. -/
theorem decode_integral {vars : Finset Nat} {rows : List Le}
    (encoding : Encoding vars rows) :
    FiniteIntegral (decode encoding) := by
  intro idx
  refine
    ⟨(positive encoding idx : ℤ) -
        (negative encoding idx : ℤ), ?_⟩
  simp [decode]

/-- The scaled row equation associated with one encoded direction and one row
occurrence. -/
def equation {vars : Finset Nat} {rows : List Le}
    (scale : ℕ) (encoding : Encoding vars rows)
    (rowIndex : Fin rows.length) : ℚ :=
  (scale : ℚ) *
      finiteEval vars (rows.get rowIndex).form (decode encoding) +
    (slack encoding rowIndex : ℚ)

@[simp]
theorem equation_zero
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    equation scale (0 : Encoding vars rows) = 0 := by
  funext rowIndex
  change (scale : ℚ) *
      finiteEval vars (rows.get rowIndex).form
        (decode (0 : Encoding vars rows)) +
      (slack (0 : Encoding vars rows) rowIndex : ℚ) = 0
  rw [decode_zero]
  have hzero :=
    (evalLinear vars (rows.get rowIndex).form).map_zero
  change
    finiteEval vars (rows.get rowIndex).form 0 = 0
      at hzero
  rw [hzero]
  simp [slack]

@[simp]
theorem equation_add
    {vars : Finset Nat} {rows : List Le}
    (scale : ℕ) (left right : Encoding vars rows) :
    equation scale (left + right) =
      equation scale left + equation scale right := by
  funext rowIndex
  simp [equation, slack, finiteEval_add]
  ring

/-- All scaled row equations, viewed as one additive homomorphism. -/
def equationHom
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    Encoding vars rows →+ (Fin rows.length → ℚ) where
  toFun := equation scale
  map_zero' := equation_zero vars rows scale
  map_add' := equation_add scale

@[simp]
theorem equationHom_apply
    {vars : Finset Nat} {rows : List Le}
    (scale : ℕ) (encoding : Encoding vars rows)
    (rowIndex : Fin rows.length) :
    equationHom vars rows scale encoding rowIndex =
      equation scale encoding rowIndex :=
  rfl

/-- Nonnegative encodings whose scaled row equations all vanish. -/
def solutionMonoid
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    AddSubmonoid (Encoding vars rows) :=
  (equationHom vars rows scale).eqLocusM 0

theorem mem_solutionMonoid_iff
    {vars : Finset Nat} {rows : List Le}
    {scale : ℕ} {encoding : Encoding vars rows} :
    encoding ∈ solutionMonoid vars rows scale ↔
      ∀ rowIndex, equation scale encoding rowIndex = 0 := by
  change equationHom vars rows scale encoding = 0 ↔ _
  constructor
  · intro h rowIndex
    exact congrFun h rowIndex
  · intro h
    funext rowIndex
    exact h rowIndex

/-- Every solution encoding decodes to a recession direction. -/
theorem solution_decode_recession
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale : 0 < scale) {encoding : Encoding vars rows}
    (hsolution :
      encoding ∈ solutionMonoid vars rows scale) :
    decode encoding ∈ recessionCone vars rows := by
  intro row hrow
  obtain ⟨rowIndex, hrowIndex⟩ :=
    List.get_of_mem hrow
  have hequation :=
    (mem_solutionMonoid_iff.mp hsolution) rowIndex
  rw [equation, hrowIndex] at hequation
  have hslackNonnegative :
      (0 : ℚ) ≤ (slack encoding rowIndex : ℕ) := by
    positivity
  have hscalePositive : (0 : ℚ) < scale := by
    positivity
  nlinarith

/-- Every solution encoding decodes to an integral recession direction. -/
theorem solution_decode_integral_recession
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale : 0 < scale) {encoding : Encoding vars rows}
    (hsolution :
      encoding ∈ solutionMonoid vars rows scale) :
    FiniteIntegral (decode encoding) ∧
      decode encoding ∈ recessionCone vars rows :=
  ⟨decode_integral encoding,
    solution_decode_recession hscale hsolution⟩

/-- Every integral recession direction is represented by a solution
encoding. -/
theorem exists_solution_encoding
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hrowScale :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a))
    {direction : FiniteValuation vars}
    (hintegral : FiniteIntegral direction)
    (hdirection : direction ∈ recessionCone vars rows) :
    ∃ encoding : Encoding vars rows,
      encoding ∈ solutionMonoid vars rows scale ∧
      decode encoding = direction := by
  have hslacks :=
    exists_recession_slacks
      hrowScale hintegral hdirection
  choose coordinate hcoordinate using hintegral
  have hindexedSlacks :
      ∀ rowIndex : Fin rows.length, ∃ rowSlack : ℕ,
        (scale : ℚ) *
            finiteEval vars
              (rows.get rowIndex).form direction =
          -(rowSlack : ℚ) := by
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
  have hdecode : decode encoding = direction := by
    funext idx
    have hsplit :
        ((coordinate idx).toNat : ℤ) -
            ((-coordinate idx).toNat : ℤ) =
          coordinate idx := by
      omega
    change
      ((coordinate idx).toNat : ℚ) -
          ((-coordinate idx).toNat : ℚ) =
        direction idx
    rw [hcoordinate idx]
    exact_mod_cast hsplit
  refine ⟨encoding, ?_, hdecode⟩
  apply mem_solutionMonoid_iff.mpr
  intro rowIndex
  rw [equation, hdecode]
  change
    (scale : ℚ) *
        finiteEval vars
          (rows.get rowIndex).form direction +
      (rowSlack rowIndex : ℚ) = 0
  rw [hrowSlack rowIndex]
  ring

/-- For a positive integralizing scale, the decoded solution monoid is exactly
the set of integral recession directions. -/
theorem exists_solution_encoding_iff
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale : 0 < scale)
    (hrowScale :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a))
    (direction : FiniteValuation vars) :
    (∃ encoding : Encoding vars rows,
        encoding ∈ solutionMonoid vars rows scale ∧
        decode encoding = direction) ↔
      FiniteIntegral direction ∧
        direction ∈ recessionCone vars rows := by
  constructor
  · rintro ⟨encoding, hsolution, rfl⟩
    exact
      solution_decode_integral_recession
        hscale hsolution
  · rintro ⟨hintegral, hdirection⟩
    exact
      exists_solution_encoding
        hrowScale hintegral hdirection

/-- Gordan's lemma: the nonnegative solution monoid of the scaled row
equations has a finite generating set. -/
theorem solutionMonoid_fg
    (vars : Finset Nat) (rows : List Le) (scale : ℕ) :
    (solutionMonoid vars rows scale).FG := by
  letI : ExistsAddOfLE (Encoding vars rows) :=
    { exists_add_of_le := by
        intro first second h
        let difference : Encoding vars rows :=
          fun idx => second idx - first idx
        refine ⟨difference, ?_⟩
        funext idx
        have hidx := h idx
        dsimp [difference]
        dsimp at hidx
        omega }
  letI : CanonicallyOrderedAdd (Encoding vars rows) :=
    { le_add_self := by
        intro first second idx
        dsimp
        omega
      le_self_add := by
        intro first second idx
        dsimp
        omega }
  letI :
      IsOrderedCancelAddMonoid
        (Encoding vars rows) :=
    { add_le_add_left :=
        fun _ _ h _ idx => by
          have hidx := h idx
          dsimp at hidx ⊢
          omega
      le_of_add_le_add_left :=
        fun _ _ _ h idx =>
          by
            have hidx := h idx
            dsimp at hidx ⊢
            omega
      le_of_add_le_add_right :=
        fun _ _ _ h idx =>
          by
            have hidx := h idx
            dsimp at hidx ⊢
            omega }
  exact
    AddSubmonoid.fg_eqLocusM
      (equationHom vars rows scale) 0

/-- Additive generation transports through decoding. -/
theorem decode_mem_closure_image
    {vars : Finset Nat} {rows : List Le}
    (generators : Finset (Encoding vars rows))
    {encoding : Encoding vars rows}
    (hencoding :
      encoding ∈ AddSubmonoid.closure
        (generators : Set (Encoding vars rows))) :
    decode encoding ∈ AddSubmonoid.closure
      (decode '' (generators :
        Set (Encoding vars rows))) := by
  induction hencoding using
      AddSubmonoid.closure_induction with
  | mem candidate hcandidate =>
      apply AddSubmonoid.subset_closure
      exact ⟨candidate, hcandidate, rfl⟩
  | zero =>
      rw [decode_zero]
      exact AddSubmonoid.zero_mem _
  | add left right _ _ hleft hright =>
      rw [decode_add]
      exact AddSubmonoid.add_mem _ hleft hright

/-- A finite decoded family additively generates every integral recession
direction. -/
theorem exists_finite_integral_recession_generators
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale : 0 < scale)
    (hrowScale :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a)) :
    ∃ generators : Finset (Encoding vars rows),
      (∀ encoding ∈ generators,
        FiniteIntegral (decode encoding) ∧
          decode encoding ∈ recessionCone vars rows) ∧
      ∀ direction : FiniteValuation vars,
        FiniteIntegral direction →
        direction ∈ recessionCone vars rows →
        direction ∈ AddSubmonoid.closure
          (decode '' (generators :
            Set (Encoding vars rows))) := by
  obtain ⟨generatorSet, hgenerators, hfinite⟩ :=
    (AddSubmonoid.fg_iff _).1 (solutionMonoid_fg vars rows scale)
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro encoding hencoding
    apply solution_decode_integral_recession hscale
    rw [← hgenerators]
    exact AddSubmonoid.subset_closure (hfinite.mem_toFinset.mp hencoding)
  · intro direction hintegral hdirection
    obtain ⟨encoding, hsolution, hdecode⟩ :=
      exists_solution_encoding
        hrowScale hintegral hdirection
    rw [← hdecode]
    apply decode_mem_closure_image hfinite.toFinset
    rw [Set.Finite.coe_toFinset, hgenerators]
    exact hsolution

/-- Additive combinations of decoded generators remain recession
directions. -/
theorem closure_decode_recession
    {vars : Finset Nat} {rows : List Le}
    {generators : Finset (Encoding vars rows)}
    (hgenerators :
      ∀ encoding ∈ generators,
        decode encoding ∈ recessionCone vars rows)
    {direction : FiniteValuation vars}
    (hdirection :
      direction ∈ AddSubmonoid.closure
        (decode '' (generators :
          Set (Encoding vars rows)))) :
    direction ∈ recessionCone vars rows := by
  induction hdirection using
      AddSubmonoid.closure_induction with
  | mem candidate hcandidate =>
      obtain ⟨encoding, hencoding, rfl⟩ := hcandidate
      exact hgenerators encoding hencoding
  | zero =>
      exact zero_mem_recessionCone vars rows
  | add left right _ _ hleft hright =>
      intro row hrow
      rw [finiteEval_add]
      exact
        add_nonpos (hleft row hrow) (hright row hrow)

/-- Additive combinations of decoded integral generators remain integral. -/
theorem closure_decode_integral
    {vars : Finset Nat} {rows : List Le}
    {generators : Finset (Encoding vars rows)}
    (hgenerators :
      ∀ encoding ∈ generators,
        FiniteIntegral (decode encoding))
    {direction : FiniteValuation vars}
    (hdirection :
      direction ∈
        AddSubmonoid.closure
          (decode '' (generators :
            Set (Encoding vars rows)))) :
    FiniteIntegral direction := by
  induction hdirection using
      AddSubmonoid.closure_induction with
  | mem candidate hcandidate =>
      obtain ⟨encoding, hencoding, rfl⟩ :=
        hcandidate
      exact hgenerators encoding hencoding
  | zero =>
      intro idx
      exact ⟨0, by simp⟩
  | add left right _ _ hleft hright =>
      intro idx
      obtain ⟨leftValue, hleftValue⟩ := hleft idx
      obtain ⟨rightValue, hrightValue⟩ :=
        hright idx
      refine ⟨leftValue + rightValue, ?_⟩
      change left idx + right idx = _
      rw [hleftValue, hrightValue]
      push_cast
      ring

/-- A finite decoded family rationally generates the full recession cone: a
direction belongs to the cone exactly when some positive natural multiple
belongs to the additive monoid generated by that family. -/
theorem exists_finite_rational_recession_generators
    (vars : Finset Nat) (rows : List Le) :
    ∃ generators : Finset (Encoding vars rows),
      (∀ encoding ∈ generators,
        FiniteIntegral (decode encoding) ∧
          decode encoding ∈ recessionCone vars rows) ∧
      ∀ direction : FiniteValuation vars,
        direction ∈ recessionCone vars rows ↔
          ∃ denominator : ℕ, 0 < denominator ∧
            (denominator : ℚ) • direction ∈
              AddSubmonoid.closure
                (decode '' (generators :
                  Set (Encoding vars rows))) := by
  obtain ⟨rowScale, hrowScalePositive, hrowScale⟩ :=
    exists_rows_integral_scale vars rows
  obtain
      ⟨generators, hgenerators, hintegralGenerate⟩ :=
    exists_finite_integral_recession_generators
      hrowScalePositive hrowScale
  refine ⟨generators, hgenerators, ?_⟩
  intro direction
  constructor
  · intro hdirection
    obtain
        ⟨denominator, hdenominatorPositive,
          hintegral, hscaledDirection⟩ :=
      exists_integral_recession_multiple hdirection
    exact
      ⟨denominator, hdenominatorPositive,
        hintegralGenerate
          _ hintegral hscaledDirection⟩
  · rintro
      ⟨denominator, hdenominatorPositive, hgenerated⟩
    have hscaledDirection :
        (denominator : ℚ) • direction ∈
          recessionCone vars rows :=
      closure_decode_recession
        (fun encoding hencoding =>
          (hgenerators encoding hencoding).2)
        hgenerated
    intro row hrow
    have hrowScaled := hscaledDirection row hrow
    rw [finiteEval_smul] at hrowScaled
    have hdenominatorRat :
        (0 : ℚ) < denominator := by
      positivity
    nlinarith

end LeanVIPR.Completeness.RecessionMonoid
