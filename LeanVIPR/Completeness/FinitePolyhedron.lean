module

public import LeanVIPR.Completeness.FiniteRankCriterion
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Defs

@[expose] public section

/-!
# Finite-dimensional semantics for rational row systems

LeanVIPR valuations are functions `Nat → ℚ`, while polyhedral geometry is most
naturally developed in a finite-dimensional space.  For a finite variable set,
this file restricts valuations to the corresponding finite subtype and proves
that sparse-row feasibility and mixed-integer infeasibility are unchanged.
-/

namespace LeanVIPR.Completeness.FinitePolyhedron

open LeanVIPR.Cert LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.IntegerProjection LeanVIPR.Cert.ViprSystem

abbrev FiniteValuation (vars : Finset Nat) := vars → ℚ

def restrictValuation {vars : Finset Nat}
    (a : Valuation) : FiniteValuation vars :=
  fun idx => a idx

def extendValuation {vars : Finset Nat}
    (a : FiniteValuation vars) : Valuation :=
  fun idx => if hidx : idx ∈ vars then a ⟨idx, hidx⟩ else 0

@[simp]
theorem restrict_extend {vars : Finset Nat}
    (a : FiniteValuation vars) :
    restrictValuation (extendValuation a) = a := by
  funext idx
  simp [restrictValuation, extendValuation, idx.property]

theorem extend_restrict_of_mem {vars : Finset Nat}
    (a : Valuation) {idx : Nat} (hidx : idx ∈ vars) :
    extendValuation (vars := vars)
        (restrictValuation (vars := vars) a) idx = a idx := by
  simp [extendValuation, restrictValuation, hidx]

def FormSupported (vars : Finset Nat) (form : LinForm) : Prop :=
  ∀ term ∈ form, term.idx ∈ vars

def RowsSupported (vars : Finset Nat) (rows : List Le) : Prop :=
  ∀ row ∈ rows, FormSupported vars row.form

def finiteEval (vars : Finset Nat) (form : LinForm)
    (a : FiniteValuation vars) : ℚ :=
  LinForm.eval form (extendValuation a)

theorem finiteEval_restrict {vars : Finset Nat} {form : LinForm}
    (hsupported : FormSupported vars form) (a : Valuation) :
    finiteEval vars form (restrictValuation a) =
      LinForm.eval form a := by
  induction form with
  | nil => rfl
  | cons term form ih =>
      change term.coeff *
            extendValuation (vars := vars)
              (restrictValuation (vars := vars) a) term.idx +
            finiteEval vars form (restrictValuation a) =
          term.coeff * a term.idx + LinForm.eval form a
      rw [extend_restrict_of_mem a
        (hsupported term (by simp))]
      rw [ih fun candidate hcandidate =>
        hsupported candidate (by simp [hcandidate])]

theorem finiteEval_add (vars : Finset Nat) (form : LinForm)
    (left right : FiniteValuation vars) :
    finiteEval vars form (left + right) =
      finiteEval vars form left + finiteEval vars form right := by
  induction form with
  | nil => simp [finiteEval, LinForm.eval]
  | cons term form ih =>
      change term.coeff *
            extendValuation (vars := vars) (left + right) term.idx +
            finiteEval vars form (left + right) =
          term.coeff * extendValuation left term.idx +
              finiteEval vars form left +
            (term.coeff * extendValuation right term.idx +
              finiteEval vars form right)
      rw [ih]
      by_cases hidx : term.idx ∈ vars
      · simp [extendValuation, hidx]
        ring
      · simp [extendValuation, hidx]

theorem finiteEval_smul (vars : Finset Nat) (form : LinForm)
    (q : ℚ) (a : FiniteValuation vars) :
    finiteEval vars form (q • a) =
      q * finiteEval vars form a := by
  induction form with
  | nil => simp [finiteEval, LinForm.eval]
  | cons term form ih =>
      change term.coeff *
            extendValuation (vars := vars) (q • a) term.idx +
            finiteEval vars form (q • a) =
          q * (term.coeff * extendValuation a term.idx +
            finiteEval vars form a)
      rw [ih]
      by_cases hidx : term.idx ∈ vars
      · simp [extendValuation, hidx]
        ring
      · simp [extendValuation, hidx]

def evalLinear (vars : Finset Nat) (form : LinForm) :
    FiniteValuation vars →ₗ[ℚ] ℚ where
  toFun := finiteEval vars form
  map_add' := finiteEval_add vars form
  map_smul' q a := by
    simp [finiteEval_smul, smul_eq_mul]

def FiniteSat (vars : Finset Nat) (row : Le)
    (a : FiniteValuation vars) : Prop :=
  finiteEval vars row.form a ≤ row.rhs

def polyhedron (vars : Finset Nat) (rows : List Le) :
    Set (FiniteValuation vars) :=
  {a | ∀ row ∈ rows, FiniteSat vars row a}

def FiniteRatFeasible (vars : Finset Nat) (rows : List Le) : Prop :=
  (polyhedron vars rows).Nonempty

theorem finiteSat_convex (vars : Finset Nat) (row : Le) :
    Convex ℚ {a : FiniteValuation vars | FiniteSat vars row a} := by
  intro left hleft right hright q r hq hr hsum
  change finiteEval vars row.form left ≤ row.rhs at hleft
  change finiteEval vars row.form right ≤ row.rhs at hright
  change finiteEval vars row.form (q • left + r • right) ≤ row.rhs
  rw [finiteEval_add, finiteEval_smul, finiteEval_smul]
  calc
    q * finiteEval vars row.form left +
        r * finiteEval vars row.form right ≤
      q * row.rhs + r * row.rhs :=
        add_le_add
          (mul_le_mul_of_nonneg_left hleft hq)
          (mul_le_mul_of_nonneg_left hright hr)
    _ = row.rhs := by
      rw [← add_mul, hsum, one_mul]

theorem polyhedron_convex (vars : Finset Nat) (rows : List Le) :
    Convex ℚ (polyhedron vars rows) := by
  intro left hleft right hright q r hq hr hsum row hrow
  exact finiteSat_convex vars row
    (hleft row hrow) (hright row hrow) hq hr hsum

/-- Homogeneous directions that do not increase any defining row. -/
def recessionCone (vars : Finset Nat) (rows : List Le) :
    Set (FiniteValuation vars) :=
  {direction |
    ∀ row ∈ rows,
      finiteEval vars row.form direction ≤ 0}

theorem zero_mem_recessionCone (vars : Finset Nat) (rows : List Le) :
    (0 : FiniteValuation vars) ∈ recessionCone vars rows := by
  intro row _
  change evalLinear vars row.form 0 ≤ 0
  simp

theorem recessionCone_convex (vars : Finset Nat) (rows : List Le) :
    Convex ℚ (recessionCone vars rows) := by
  intro left hleft right hright q r hq hr _ row hrow
  rw [finiteEval_add, finiteEval_smul, finiteEval_smul]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos hq (hleft row hrow))
    (mul_nonpos_of_nonneg_of_nonpos hr (hright row hrow))

theorem add_smul_recession_mem_polyhedron
    (vars : Finset Nat) (rows : List Le)
    {point direction : FiniteValuation vars}
    (hpoint : point ∈ polyhedron vars rows)
    (hdirection : direction ∈ recessionCone vars rows)
    {q : ℚ} (hq : 0 ≤ q) :
    point + q • direction ∈ polyhedron vars rows := by
  intro row hrow
  change finiteEval vars row.form (point + q • direction) ≤ row.rhs
  rw [finiteEval_add, finiteEval_smul]
  have hdir :
      q * finiteEval vars row.form direction ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq
      (hdirection row hrow)
  have hpointRow := hpoint row hrow
  change finiteEval vars row.form point ≤ row.rhs at hpointRow
  linarith

/-- For a nonempty row polyhedron, the homogeneous row definition is
equivalent to preserving feasibility under every nonnegative displacement. -/
theorem mem_recessionCone_iff
    {vars : Finset Nat} {rows : List Le}
    (hfeasible : FiniteRatFeasible vars rows)
    (direction : FiniteValuation vars) :
    direction ∈ recessionCone vars rows ↔
      ∀ point ∈ polyhedron vars rows, ∀ q : ℚ, 0 ≤ q →
        point + q • direction ∈ polyhedron vars rows := by
  constructor
  · intro hdirection point hpoint q hq
    exact add_smul_recession_mem_polyhedron vars rows
      hpoint hdirection hq
  · intro hpreserves row hrow
    by_contra hnonpos
    have hpositive :
        0 < finiteEval vars row.form direction :=
      lt_of_not_ge hnonpos
    obtain ⟨point, hpoint⟩ := hfeasible
    let slack : ℚ :=
      row.rhs - finiteEval vars row.form point + 1
    have hslackPositive : 0 < slack := by
      have hpointRow := hpoint row hrow
      change finiteEval vars row.form point ≤ row.rhs at hpointRow
      dsimp [slack]
      linarith
    let q : ℚ :=
      slack / finiteEval vars row.form direction
    have hq : 0 ≤ q :=
      le_of_lt (div_pos hslackPositive hpositive)
    have hshift :=
      hpreserves point hpoint q hq row hrow
    change finiteEval vars row.form
        (point + q • direction) ≤ row.rhs at hshift
    rw [finiteEval_add, finiteEval_smul] at hshift
    have hqmul :
        q * finiteEval vars row.form direction = slack := by
      dsimp [q]
      field_simp
    rw [hqmul] at hshift
    dsimp [slack] at hshift
    linarith

def FiniteIntegral {vars : Finset Nat}
    (a : FiniteValuation vars) : Prop :=
  ∀ idx, IsIntVal (a idx)

/-- A finite sparse rational form has a positive common denominator. -/
theorem exists_form_integral_scale (form : LinForm) :
    ∃ scale : ℕ, 0 < scale ∧
      ∀ term ∈ form, IsIntVal ((scale : ℚ) * term.coeff) := by
  let scale : ℕ := (form.map fun term => term.coeff.den).prod
  have hscalePositive : 0 < scale := by
    dsimp [scale]
    exact List.prod_pos fun denominator hdenominator => by
      obtain ⟨term, hterm, rfl⟩ :=
        List.mem_map.mp hdenominator
      exact term.coeff.den_pos
  refine ⟨scale, hscalePositive, ?_⟩
  intro term hterm
  have hmem :
      term.coeff.den ∈
        form.map (fun candidate => candidate.coeff.den) :=
    List.mem_map.mpr ⟨term, hterm, rfl⟩
  have hdiv : term.coeff.den ∣ scale := by
    dsimp [scale]
    exact List.dvd_prod hmem
  obtain ⟨factor, hfactor⟩ := hdiv
  refine ⟨(factor : ℤ) * term.coeff.num, ?_⟩
  rw [hfactor]
  push_cast
  calc
    ((term.coeff.den : ℚ) * (factor : ℚ)) * term.coeff =
        (factor : ℚ) *
          ((term.coeff.den : ℚ) * term.coeff) := by
      ring
    _ = (factor : ℚ) * term.coeff.num := by
      rw [Rat.den_mul_eq_num]

/-- Scaling every coefficient to an integer makes evaluation integral on
integral finite valuations. -/
theorem scaled_finiteEval_integral
    {vars : Finset Nat} {form : LinForm} {scale : ℕ}
    (hcoeff :
      ∀ term ∈ form,
        IsIntVal ((scale : ℚ) * term.coeff))
    (a : FiniteValuation vars) (hintegral : FiniteIntegral a) :
    IsIntVal ((scale : ℚ) * finiteEval vars form a) := by
  induction form with
  | nil =>
      exact ⟨0, by simp [finiteEval, LinForm.eval]⟩
  | cons term tail ih =>
      have htermCoeff := hcoeff term (by simp)
      have htailCoeff :
          ∀ candidate ∈ tail,
            IsIntVal ((scale : ℚ) * candidate.coeff) := by
        intro candidate hcandidate
        exact hcoeff candidate (by simp [hcandidate])
      have hvalue :
          IsIntVal (extendValuation a term.idx) := by
        by_cases hidx : term.idx ∈ vars
        · simpa [extendValuation, hidx] using
            hintegral ⟨term.idx, hidx⟩
        · exact ⟨0, by simp [extendValuation, hidx]⟩
      obtain ⟨coefficient, hcoefficient⟩ := htermCoeff
      obtain ⟨value, hvalue⟩ := hvalue
      obtain ⟨tailValue, htailValue⟩ := ih htailCoeff
      refine ⟨coefficient * value + tailValue, ?_⟩
      change (scale : ℚ) *
          (term.coeff * extendValuation a term.idx +
            finiteEval vars tail a) = _
      rw [mul_add, ← mul_assoc, hcoefficient, hvalue, htailValue]
      push_cast
      ring

/-- A finite sparse rational form has a positive scale whose evaluation is
integral on every integral finite valuation. -/
theorem exists_finiteEval_integral_scale
    (vars : Finset Nat) (form : LinForm) :
    ∃ scale : ℕ, 0 < scale ∧
      ∀ a : FiniteValuation vars, FiniteIntegral a →
        IsIntVal ((scale : ℚ) * finiteEval vars form a) := by
  obtain ⟨scale, hpositive, hcoeff⟩ :=
    exists_form_integral_scale form
  exact
    ⟨scale, hpositive,
      fun a ha => scaled_finiteEval_integral hcoeff a ha⟩

/-- One denominator scale integralizes every row in a finite system. -/
theorem exists_rows_integral_scale
    (vars : Finset Nat) (rows : List Le) :
    ∃ scale : ℕ, 0 < scale ∧
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a) := by
  obtain ⟨scale, hpositive, hcoeff⟩ :=
    exists_form_integral_scale
      (rows.flatMap fun row => row.form)
  refine ⟨scale, hpositive, ?_⟩
  intro row hrow a ha
  apply scaled_finiteEval_integral _ a ha
  intro term hterm
  apply hcoeff term
  exact List.mem_flatMap.mpr ⟨row, hrow, hterm⟩

/-- One denominator scale integralizes every row coefficient and right-hand
side. -/
theorem exists_rows_affine_integral_scale
    (vars : Finset Nat) (rows : List Le) :
    ∃ scale : ℕ, 0 < scale ∧
      (∀ row ∈ rows, IsIntVal ((scale : ℚ) * row.rhs)) ∧
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal ((scale : ℚ) * finiteEval vars row.form a) := by
  obtain ⟨scale, hpositive, hcoeff⟩ :=
    exists_form_integral_scale
      (rows.flatMap fun row =>
        { idx := 0, coeff := row.rhs } :: row.form)
  refine ⟨scale, hpositive, ?_, ?_⟩
  · intro row hrow
    exact hcoeff { idx := 0, coeff := row.rhs }
      (List.mem_flatMap.mpr ⟨row, hrow, by simp⟩)
  · intro row hrow a ha
    apply scaled_finiteEval_integral _ a ha
    intro term hterm
    apply hcoeff term
    exact List.mem_flatMap.mpr ⟨row, hrow, by simp [hterm]⟩

/-- A nonnegative rational integer is a natural number. -/
theorem isIntVal_nonneg_eq_nat {q : ℚ}
    (hintegral : IsIntVal q) (hnonneg : 0 ≤ q) :
    ∃ slack : ℕ, q = (slack : ℚ) := by
  obtain ⟨value, hvalue⟩ := hintegral
  have hvalueNonneg : 0 ≤ value := by
    exact_mod_cast (hvalue ▸ hnonneg)
  let slack : ℕ := value.toNat
  have hslack : (slack : ℤ) = value := by
    dsimp [slack]
    rw [Int.ofNat_toNat]
    exact max_eq_left hvalueNonneg
  refine ⟨slack, ?_⟩
  rw [hvalue]
  exact_mod_cast hslack.symm

/-- Integral feasible points admit natural slack coordinates after affine row
scaling. -/
theorem exists_feasible_slacks
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hrhs : ∀ row ∈ rows, IsIntVal ((scale : ℚ) * row.rhs))
    (heval :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal ((scale : ℚ) * finiteEval vars row.form a))
    {point : FiniteValuation vars}
    (hintegral : FiniteIntegral point)
    (hpoint : point ∈ polyhedron vars rows) :
    ∀ row ∈ rows, ∃ slack : ℕ,
      (scale : ℚ) * finiteEval vars row.form point +
          (slack : ℚ) =
        (scale : ℚ) * row.rhs := by
  intro row hrow
  obtain ⟨evalValue, hevalValue⟩ :=
    heval row hrow point hintegral
  obtain ⟨rhsValue, hrhsValue⟩ := hrhs row hrow
  have hgapIntegral :
      IsIntVal
        ((scale : ℚ) * row.rhs -
          (scale : ℚ) * finiteEval vars row.form point) := by
    refine ⟨rhsValue - evalValue, ?_⟩
    rw [hrhsValue, hevalValue]
    push_cast
    ring
  have hpointRow := hpoint row hrow
  have hgapNonneg :
      0 ≤ (scale : ℚ) * row.rhs -
        (scale : ℚ) * finiteEval vars row.form point := by
    change finiteEval vars row.form point ≤ row.rhs at hpointRow
    have hscaleNonneg : (0 : ℚ) ≤ scale := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpointRow hscaleNonneg]
  obtain ⟨slack, hslack⟩ :=
    isIntVal_nonneg_eq_nat hgapIntegral hgapNonneg
  refine ⟨slack, ?_⟩
  linarith

/-- A nonpositive rational integer is the negation of a natural number. -/
theorem isIntVal_nonpos_eq_neg_nat {q : ℚ}
    (hintegral : IsIntVal q) (hnonpos : q ≤ 0) :
    ∃ slack : ℕ, q = -(slack : ℚ) := by
  obtain ⟨value, hvalue⟩ := hintegral
  have hvalueNonpos : value ≤ 0 := by
    exact_mod_cast (hvalue ▸ hnonpos)
  let slack : ℕ := (-value).toNat
  have hslack : (slack : ℤ) = -value := by
    dsimp [slack]
    rw [Int.ofNat_toNat]
    exact max_eq_left (by omega)
  refine ⟨slack, ?_⟩
  rw [hvalue]
  have hinteger : value = -(slack : ℤ) := by
    omega
  exact_mod_cast hinteger

/-- Integral recession directions admit natural slack coordinates after a
common row scaling. -/
theorem exists_recession_slacks
    {vars : Finset Nat} {rows : List Le} {scale : ℕ}
    (hscale :
      ∀ row ∈ rows, ∀ a : FiniteValuation vars,
        FiniteIntegral a →
          IsIntVal
            ((scale : ℚ) * finiteEval vars row.form a))
    {direction : FiniteValuation vars}
    (hintegral : FiniteIntegral direction)
    (hdirection : direction ∈ recessionCone vars rows) :
    ∀ row ∈ rows, ∃ slack : ℕ,
      (scale : ℚ) * finiteEval vars row.form direction =
        -(slack : ℚ) := by
  intro row hrow
  apply isIntVal_nonpos_eq_neg_nat
  · exact hscale row hrow direction hintegral
  · exact mul_nonpos_of_nonneg_of_nonpos
      (by positivity : (0 : ℚ) ≤ scale)
      (hdirection row hrow)

/-- Every finite rational vector has a positive natural multiple with integral
coordinates. -/
theorem finite_rational_vector_integral_scale {vars : Finset Nat}
    (direction : FiniteValuation vars) :
    ∃ scale : ℕ, 0 < scale ∧
      FiniteIntegral ((scale : ℚ) • direction) := by
  let scale : ℕ := ∏ idx : vars, (direction idx).den
  have hscalePositive : 0 < scale := by
    dsimp [scale]
    exact Finset.prod_pos fun idx _ => (direction idx).den_pos
  refine ⟨scale, hscalePositive, ?_⟩
  intro idx
  have hdiv : (direction idx).den ∣ scale := by
    dsimp [scale]
    exact Finset.dvd_prod_of_mem
      (fun candidate => (direction candidate).den)
      (Finset.mem_univ idx)
  obtain ⟨factor, hfactor⟩ := hdiv
  refine ⟨(factor : ℤ) * (direction idx).num, ?_⟩
  change (scale : ℚ) * direction idx = _
  rw [hfactor]
  push_cast
  calc
    (((direction idx).den : ℚ) * (factor : ℚ)) * direction idx =
        (factor : ℚ) *
          (((direction idx).den : ℚ) * direction idx) := by
      ring
    _ = (factor : ℚ) * (direction idx).num := by
      rw [Rat.den_mul_eq_num]

/-- Every rational recession direction has a positive integral recession
multiple. -/
theorem exists_integral_recession_multiple
    {vars : Finset Nat} {rows : List Le}
    {direction : FiniteValuation vars}
    (hdirection : direction ∈ recessionCone vars rows) :
    ∃ scale : ℕ, 0 < scale ∧
      FiniteIntegral ((scale : ℚ) • direction) ∧
      (scale : ℚ) • direction ∈ recessionCone vars rows := by
  obtain ⟨scale, hscalePositive, hintegral⟩ :=
    finite_rational_vector_integral_scale direction
  refine ⟨scale, hscalePositive, hintegral, ?_⟩
  intro row hrow
  rw [finiteEval_smul]
  exact mul_nonpos_of_nonneg_of_nonpos
    (by positivity : (0 : ℚ) ≤ scale)
    (hdirection row hrow)

theorem ratFeasible_iff_finite {vars : Finset Nat} {rows : List Le}
    (hsupported : RowsSupported vars rows) :
    RatFeasible rows ↔ FiniteRatFeasible vars rows := by
  constructor
  · rintro ⟨a, hrows⟩
    refine ⟨restrictValuation a, ?_⟩
    intro row hrow
    unfold FiniteSat
    rw [finiteEval_restrict (hsupported row hrow)]
    exact hrows row hrow
  · rintro ⟨a, hrows⟩
    refine ⟨extendValuation a, ?_⟩
    intro row hrow
    exact hrows row hrow

def FiniteNoIntSolution (vars : Finset Nat) (rows : List Le) : Prop :=
  ∀ a : FiniteValuation vars,
    FiniteIntegral a →
    (∀ row ∈ rows, FiniteSat vars row a) →
    False

theorem rowsSupported_toFinset {intVars : List Nat} {rows : List Le}
    (hsupported : RowsOnIntVars intVars rows) :
    RowsSupported intVars.toFinset rows := by
  intro row hrow term hterm
  simpa using hsupported row hrow term hterm

theorem noIntSolution_iff_finite {intVars : List Nat} {rows : List Le}
    (hsupported : RowsOnIntVars intVars rows) :
    IntegerProjection.NoIntSolution intVars rows ↔
      FiniteNoIntSolution intVars.toFinset rows := by
  have hrowsSupported : RowsSupported intVars.toFinset rows := by
    exact rowsSupported_toFinset hsupported
  constructor
  · intro hno a hintegral hrows
    apply hno (extendValuation (vars := intVars.toFinset) a)
    · intro idx hidx
      have hmem : idx ∈ intVars.toFinset := by
        simpa only [List.mem_toFinset] using hidx
      simpa [extendValuation, hmem] using
        hintegral ⟨idx, hmem⟩
    · intro row hrow
      exact hrows row hrow
  · intro hno a hintegral hrows
    apply hno (restrictValuation (vars := intVars.toFinset) a)
    · intro idx
      apply hintegral idx.1
      simpa only [List.mem_toFinset] using idx.property
    · intro row hrow
      unfold FiniteSat
      rw [finiteEval_restrict (hrowsSupported row hrow)]
      exact hrows row hrow

def integerPoints (vars : Finset Nat) (rows : List Le) :
    Set (FiniteValuation vars) :=
  {a | a ∈ polyhedron vars rows ∧ FiniteIntegral a}

/-- Integral feasible points remain integral and feasible after displacement
by a natural multiple of an integral recession direction. -/
theorem add_integral_recession_mem_integerPoints
    {vars : Finset Nat} {rows : List Le}
    {point direction : FiniteValuation vars}
    (hpoint : point ∈ integerPoints vars rows)
    (hdirection : direction ∈ recessionCone vars rows)
    (hintegral : FiniteIntegral direction)
    (scale : ℕ) :
    point + (scale : ℚ) • direction ∈ integerPoints vars rows := by
  refine
    ⟨add_smul_recession_mem_polyhedron vars rows hpoint.1 hdirection ?_, ?_⟩
  · positivity
  · intro idx
    obtain ⟨pointValue, hpointValue⟩ := hpoint.2 idx
    obtain ⟨directionValue, hdirectionValue⟩ := hintegral idx
    refine ⟨pointValue + (scale : ℤ) * directionValue, ?_⟩
    change point idx + (scale : ℚ) * direction idx = _
    rw [hpointValue, hdirectionValue]
    push_cast
    ring

def integerHull (vars : Finset Nat) (rows : List Le) :
    Set (FiniteValuation vars) :=
  convexHull ℚ (integerPoints vars rows)

theorem integerPoints_subset_polyhedron (vars : Finset Nat)
    (rows : List Le) :
    integerPoints vars rows ⊆ polyhedron vars rows := by
  rintro a ⟨ha, _⟩
  exact ha

theorem integerHull_convex (vars : Finset Nat) (rows : List Le) :
    Convex ℚ (integerHull vars rows) :=
  convex_convexHull ℚ (integerPoints vars rows)

theorem integerHull_subset_polyhedron (vars : Finset Nat)
    (rows : List Le) :
    integerHull vars rows ⊆ polyhedron vars rows :=
  convexHull_min
    (integerPoints_subset_polyhedron vars rows)
    (polyhedron_convex vars rows)

theorem integerPoints_empty_iff (vars : Finset Nat) (rows : List Le) :
    integerPoints vars rows = ∅ ↔
      FiniteNoIntSolution vars rows := by
  constructor
  · intro hempty a hintegral hrows
    have ha : a ∈ integerPoints vars rows :=
      ⟨hrows, hintegral⟩
    rw [hempty] at ha
    exact ha
  · intro hno
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro a ⟨hrows, hintegral⟩
    exact hno a hintegral hrows

theorem integerHull_empty_iff (vars : Finset Nat) (rows : List Le) :
    integerHull vars rows = ∅ ↔
      FiniteNoIntSolution vars rows := by
  constructor
  · intro hhull
    apply (integerPoints_empty_iff vars rows).mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hmem : a ∈ integerHull vars rows :=
      subset_convexHull ℚ (integerPoints vars rows) ha
    rw [hhull] at hmem
    exact hmem
  · intro hno
    have hpoints :
        integerPoints vars rows = ∅ :=
      (integerPoints_empty_iff vars rows).mpr hno
    simp [integerHull, hpoints, convexHull_empty]

/-- Explicit integral lower and upper bounds for every finite coordinate. -/
def HasIntegralCoordinateBounds (vars : Finset Nat)
    (rows : List Le) : Prop :=
  ∃ lower upper : vars → ℤ,
    ∀ point ∈ polyhedron vars rows, ∀ idx,
      (lower idx : ℚ) ≤ point idx ∧
      point idx ≤ (upper idx : ℚ)

/-- A row polyhedron with explicit integral coordinate bounds contains only
finitely many integral points. -/
theorem integerPoints_finite_of_coordinateBounds
    {vars : Finset Nat} {rows : List Le}
    (hbounded : HasIntegralCoordinateBounds vars rows) :
    (integerPoints vars rows).Finite := by
  obtain ⟨lower, upper, hbounds⟩ := hbounded
  let box : Set (vars → ℤ) :=
    {point | ∀ idx, point idx ∈ Set.Icc (lower idx) (upper idx)}
  have hboxFinite : box.Finite := by
    dsimp [box]
    apply Set.Finite.pi'
    intro idx
    exact Set.finite_Icc (lower idx) (upper idx)
  let castPoint : (vars → ℤ) → FiniteValuation vars :=
    fun point idx => (point idx : ℚ)
  apply (hboxFinite.image castPoint).subset
  intro point hpoint
  have hintegral := hpoint.2
  choose integerPoint hintegerPoint using hintegral
  refine ⟨integerPoint, ?_, ?_⟩
  · intro idx
    have hbound := hbounds point hpoint.1 idx
    rw [hintegerPoint idx] at hbound
    constructor
    · exact_mod_cast hbound.1
    · exact_mod_cast hbound.2
  · funext idx
    exact (hintegerPoint idx).symm

/-- In the coordinate-bounded case, the integer hull is generated by a finite
set of integral feasible points. -/
theorem exists_finite_integerHull_generators
    {vars : Finset Nat} {rows : List Le}
    (hbounded : HasIntegralCoordinateBounds vars rows) :
    ∃ points : Finset (FiniteValuation vars),
      integerHull vars rows =
        convexHull ℚ (points : Set (FiniteValuation vars)) := by
  let hfinite :=
    integerPoints_finite_of_coordinateBounds hbounded
  exact ⟨hfinite.toFinset, by simp [integerHull]⟩

theorem formIntegralReal_ratToReal {intVars : List Nat}
    {form : LinForm} (hintegral : FormIntegralReal intVars form)
    (a : Valuation)
    (hint : ∀ idx ∈ intVars, IsIntVal (a idx)) :
    IsIntVal (LinForm.eval form a) := by
  have hintReal :
      ∀ idx ∈ intVars,
        IsIntReal (ViprCompleteness.ratToReal a idx) := by
    intro idx hidx
    change IsIntReal ((a idx : ℚ) : ℝ)
    exact isIntReal_of_isIntVal (hint idx hidx)
  obtain ⟨z, hz⟩ :=
    hintegral (ViprCompleteness.ratToReal a) hintReal
  refine ⟨z, ?_⟩
  rw [ViprCompleteness.evalReal_ratToReal] at hz
  exact_mod_cast hz

/-- The semantic Chvátal--Gomory closure: retain the current relaxation and
intersect it with every semantic CG cut valid for that relaxation. -/
def cgClosure (intVars : List Nat) (rows : List Le) :
    Set (FiniteValuation intVars.toFinset) :=
  {a |
    a ∈ polyhedron intVars.toFinset rows ∧
    ∀ target, SemanticCut intVars rows target →
      FiniteSat intVars.toFinset target a}

theorem cgClosure_subset_polyhedron (intVars : List Nat)
    (rows : List Le) :
    cgClosure intVars rows ⊆
      polyhedron intVars.toFinset rows := by
  rintro a ⟨hrows, _⟩
  exact hrows

theorem cgClosure_convex (intVars : List Nat) (rows : List Le) :
    Convex ℚ (cgClosure intVars rows) := by
  intro left hleft right hright q r hq hr hsum
  refine ⟨?_, ?_⟩
  · exact polyhedron_convex intVars.toFinset rows
      hleft.1 hright.1 hq hr hsum
  · intro target cut
    exact finiteSat_convex intVars.toFinset target
      (hleft.2 target cut) (hright.2 target cut)
      hq hr hsum

theorem integerPoints_subset_cgClosure (intVars : List Nat)
    (rows : List Le) :
    integerPoints intVars.toFinset rows ⊆
      cgClosure intVars rows := by
  rintro a ⟨hrows, hintegral⟩
  refine ⟨hrows, ?_⟩
  intro target cut
  let b := extendValuation a
  have hbIntegral :
      ∀ idx ∈ intVars, IsIntVal (b idx) := by
    intro idx hidx
    have hmem : idx ∈ intVars.toFinset := by
      simpa only [List.mem_toFinset] using hidx
    simpa [b, extendValuation, hmem] using
      hintegral ⟨idx, hmem⟩
  have hevalIntegral :
      IsIntVal (LinForm.eval target.form b) :=
    formIntegralReal_ratToReal cut.integral b hbIntegral
  have hbound :
      Le.sat ⟨target.form, cut.bound⟩ b := by
    exact cut.valid b fun row hrow => hrows row hrow
  have hrounded :=
    rnd_sound target.form cut.bound b hevalIntegral hbound
  change LinForm.eval target.form b ≤ target.rhs
  rw [cut.rhs_eq]
  exact hrounded

theorem integerHull_subset_cgClosure (intVars : List Nat)
    (rows : List Le) :
    integerHull intVars.toFinset rows ⊆
      cgClosure intVars rows :=
  convexHull_min
    (integerPoints_subset_cgClosure intVars rows)
    (cgClosure_convex intVars rows)

end LeanVIPR.Completeness.FinitePolyhedron
