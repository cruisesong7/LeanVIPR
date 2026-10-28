module

public import LeanVIPR.Cert.Vipr

@[expose] public section

/-!
# Fourier--Motzkin elimination over VIPR linear rows

This module begins the constructive proof of rational Farkas completeness used
by `ViprCompleteness`.  It eliminates one variable from a finite list of `≤`
rows.  Every generated row is an explicit nonnegative `lin` combination of two
input rows, so the construction can later be compiled directly to VIPR.

Sparse forms need not be canonical: a variable may occur more than once.
`LinForm.coeff` therefore sums all occurrences of the requested index.
-/

namespace LeanVIPR.Completeness.FourierMotzkin

open LeanVIPR.Cert

/-- The total coefficient of one variable in a possibly non-canonical sparse form. -/
def coeffAt (idx : Nat) : LinForm → ℚ
  | [] => 0
  | t :: f => (if t.idx = idx then t.coeff else 0) + coeffAt idx f

/-- Remove every occurrence of one variable from a sparse form. -/
def withoutVar (idx : Nat) : LinForm → LinForm
  | [] => []
  | t :: f => if t.idx = idx then withoutVar idx f else t :: withoutVar idx f

@[simp]
theorem coeffAt_nil (idx : Nat) : coeffAt idx [] = 0 := by
  rfl

@[simp]
theorem coeffAt_cons (idx : Nat) (t : Term) (f : LinForm) :
    coeffAt idx (t :: f) =
      (if t.idx = idx then t.coeff else 0) + coeffAt idx f := by
  rfl

@[simp]
theorem withoutVar_nil (idx : Nat) : withoutVar idx [] = [] := by
  rfl

@[simp]
theorem withoutVar_cons (idx : Nat) (t : Term) (f : LinForm) :
    withoutVar idx (t :: f) =
      if t.idx = idx then withoutVar idx f else t :: withoutVar idx f := by
  rfl

/-- Split evaluation into the selected variable and the remaining sparse form. -/
theorem eval_eq_coeff_mul_add (f : LinForm) (a : Valuation) (idx : Nat) :
    f.eval a = coeffAt idx f * a idx + (withoutVar idx f).eval a := by
  induction f with
  | nil => simp [LinForm.eval]
  | cons t f ih =>
      change t.coeff * a t.idx + LinForm.eval f a =
        coeffAt idx (t :: f) * a idx + LinForm.eval (withoutVar idx (t :: f)) a
      rw [ih]
      by_cases h : t.idx = idx
      · simp [LinForm.eval, coeffAt, withoutVar, h]
        ring
      · simp [LinForm.eval, coeffAt, withoutVar, h]
        ring

@[simp]
theorem coeffAt_append (idx : Nat) (f g : LinForm) :
    coeffAt idx (f ++ g) = coeffAt idx f + coeffAt idx g := by
  induction f with
  | nil => simp [coeffAt]
  | cons t f ih =>
      simp [coeffAt, ih]
      ring

@[simp]
theorem coeffAt_scale (idx : Nat) (y : ℚ) (f : LinForm) :
    coeffAt idx (LinForm.scale y f) = y * coeffAt idx f := by
  induction f with
  | nil => simp [LinForm.scale]
  | cons t f ih =>
      change (if t.idx = idx then y * t.coeff else 0) +
          coeffAt idx (LinForm.scale y f) =
        y * ((if t.idx = idx then t.coeff else 0) + coeffAt idx f)
      rw [ih]
      by_cases h : t.idx = idx
      · simp [h]
        ring
      · simp [h]

/-- The coefficient of a variable in a `lin` combination is the corresponding
combination of the parent coefficients. -/
theorem coeff_combineForm (comb : List (ℚ × Le)) (idx : Nat) :
    coeffAt idx (combineForm comb) =
      (comb.map fun p => p.1 * coeffAt idx p.2.form).sum := by
  induction comb with
  | nil => simp [combineForm]
  | cons p comb ih =>
      simp [combineForm, ih]

/-- Cancel `idx` between a row with negative coefficient and a row with positive
coefficient.  The two multipliers are nonnegative under those sign conditions. -/
def cancelPair (idx : Nat) (lower upper : Le) : Le :=
  combine
    [(-coeffAt idx lower.form, upper), (coeffAt idx upper.form, lower)]

@[simp]
theorem cancelPair_coeff (idx : Nat) (lower upper : Le) :
    coeffAt idx (cancelPair idx lower upper).form = 0 := by
  simp [cancelPair, combine, coeff_combineForm]
  ring

/-- A cancellation row is a sound `lin` consequence of its two parents. -/
theorem cancelPair_sound {idx : Nat} {lower upper : Le} {a : Valuation}
    (hlowerCoeff : coeffAt idx lower.form < 0)
    (hupperCoeff : 0 < coeffAt idx upper.form)
    (hlower : Le.sat lower a)
    (hupper : Le.sat upper a) :
    Le.sat (cancelPair idx lower upper) a := by
  apply lin_sound
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · linarith
    · linarith
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hupper
    · exact hlower

/-- Rows that impose lower bounds on the eliminated variable. -/
def lowerRows (idx : Nat) (rows : List Le) : List Le :=
  rows.filter fun c => coeffAt idx c.form < 0

/-- Rows that impose upper bounds on the eliminated variable. -/
def upperRows (idx : Nat) (rows : List Le) : List Le :=
  rows.filter fun c => 0 < coeffAt idx c.form

/-- Rows independent of the eliminated variable. -/
def zeroRows (idx : Nat) (rows : List Le) : List Le :=
  rows.filter fun c => coeffAt idx c.form = 0

/-- Eliminate one variable by retaining independent rows and combining every
lower-bound row with every upper-bound row. -/
def eliminate (idx : Nat) (rows : List Le) : List Le :=
  zeroRows idx rows ++
    (lowerRows idx rows).flatMap fun lower =>
      (upperRows idx rows).map fun upper => cancelPair idx lower upper

/-- Every row produced by one-variable elimination is independent of that variable. -/
theorem eliminate_coeff_zero {idx : Nat} {rows : List Le} {c : Le}
    (hc : c ∈ eliminate idx rows) :
    coeffAt idx c.form = 0 := by
  rcases List.mem_append.mp hc with hc | hc
  · exact of_decide_eq_true (List.mem_filter.mp hc).2
  · obtain ⟨lower, hlower, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨upper, _, rfl⟩ := List.mem_map.mp hc
    exact cancelPair_coeff idx lower upper

/-- Satisfaction of the input rows implies satisfaction of every eliminated row. -/
theorem eliminate_sound {idx : Nat} {rows : List Le} {a : Valuation}
    (hrows : ∀ c ∈ rows, Le.sat c a) :
    ∀ c ∈ eliminate idx rows, Le.sat c a := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hrows c (List.mem_of_mem_filter hc)
  · obtain ⟨lower, hlower, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨upper, hupper, rfl⟩ := List.mem_map.mp hc
    exact cancelPair_sound
      (of_decide_eq_true (List.mem_filter.mp hlower).2)
      (of_decide_eq_true (List.mem_filter.mp hupper).2)
      (hrows lower (List.mem_of_mem_filter hlower))
      (hrows upper (List.mem_of_mem_filter hupper))

/-- Replace one coordinate of a valuation. -/
def assignVar (a : Valuation) (idx : Nat) (x : ℚ) : Valuation :=
  fun j => if j = idx then x else a j

@[simp]
theorem assignVar_same (a : Valuation) (idx : Nat) (x : ℚ) :
    assignVar a idx x idx = x := by
  simp [assignVar]

@[simp]
theorem assignVar_of_ne {a : Valuation} {idx j : Nat} {x : ℚ} (h : j ≠ idx) :
    assignVar a idx x j = a j := by
  simp [assignVar, h]

/-- Evaluation after assigning one coordinate, without requiring canonical sparse forms. -/
theorem eval_assignVar (f : LinForm) (a : Valuation) (idx : Nat) (x : ℚ) :
    LinForm.eval f (assignVar a idx x) =
      coeffAt idx f * x + LinForm.eval (withoutVar idx f) a := by
  induction f with
  | nil => simp [LinForm.eval]
  | cons t f ih =>
      change t.coeff * assignVar a idx x t.idx +
          LinForm.eval f (assignVar a idx x) =
        coeffAt idx (t :: f) * x + LinForm.eval (withoutVar idx (t :: f)) a
      rw [ih]
      by_cases h : t.idx = idx
      · simp [LinForm.eval, coeffAt, withoutVar, h]
        ring
      · simp [LinForm.eval, coeffAt, withoutVar, h]
        ring

/-- The value at which a nonzero-coefficient row is tight in the eliminated variable. -/
def boundary (idx : Nat) (a : Valuation) (c : Le) : ℚ :=
  (c.rhs - LinForm.eval (withoutVar idx c.form) a) / coeffAt idx c.form

theorem sat_assign_of_lower_bound {idx : Nat} {a : Valuation} {c : Le} {x : ℚ}
    (hcoeff : coeffAt idx c.form < 0)
    (hbound : boundary idx a c ≤ x) :
    Le.sat c (assignVar a idx x) := by
  rw [Le.sat, eval_assignVar]
  unfold boundary at hbound
  have hmul := (div_le_iff_of_neg hcoeff).mp hbound
  linarith

theorem sat_assign_of_upper_bound {idx : Nat} {a : Valuation} {c : Le} {x : ℚ}
    (hcoeff : 0 < coeffAt idx c.form)
    (hbound : x ≤ boundary idx a c) :
    Le.sat c (assignVar a idx x) := by
  rw [Le.sat, eval_assignVar]
  unfold boundary at hbound
  have hmul := (le_div_iff₀ hcoeff).mp hbound
  linarith

theorem sat_assign_of_coeff_zero {idx : Nat} {a : Valuation} {c : Le} {x : ℚ}
    (hcoeff : coeffAt idx c.form = 0)
    (hsat : Le.sat c a) :
    Le.sat c (assignVar a idx x) := by
  rw [Le.sat, eval_assignVar, hcoeff]
  simp only [zero_mul, zero_add]
  rw [Le.sat, eval_eq_coeff_mul_add c.form a idx, hcoeff] at hsat
  simpa using hsat

/-- A generated pair row states exactly that its lower boundary does not exceed
its upper boundary. -/
theorem boundary_le_boundary_of_cancelPair {idx : Nat} {a : Valuation}
    {lower upper : Le}
    (hlowerCoeff : coeffAt idx lower.form < 0)
    (hupperCoeff : 0 < coeffAt idx upper.form)
    (hpair : Le.sat (cancelPair idx lower upper) a) :
    boundary idx a lower ≤ boundary idx a upper := by
  have hpair' :
      (-coeffAt idx lower.form) * LinForm.eval upper.form a +
        coeffAt idx upper.form * LinForm.eval lower.form a ≤
      (-coeffAt idx lower.form) * upper.rhs +
        coeffAt idx upper.form * lower.rhs := by
    simpa [Le.sat, cancelPair, combine, eval_combineForm] using hpair
  rw [eval_eq_coeff_mul_add upper.form a idx,
    eval_eq_coeff_mul_add lower.form a idx] at hpair'
  unfold boundary
  apply (div_le_iff_of_neg hlowerCoeff).2
  rw [show
    ((upper.rhs - LinForm.eval (withoutVar idx upper.form) a) /
        coeffAt idx upper.form) * coeffAt idx lower.form =
      (coeffAt idx lower.form *
        (upper.rhs - LinForm.eval (withoutVar idx upper.form) a)) /
          coeffAt idx upper.form by ring]
  apply (div_le_iff₀ hupperCoeff).2
  nlinarith

@[simp]
theorem mem_lowerRows {idx : Nat} {rows : List Le} {c : Le} :
    c ∈ lowerRows idx rows ↔ c ∈ rows ∧ coeffAt idx c.form < 0 := by
  simp [lowerRows]

@[simp]
theorem mem_upperRows {idx : Nat} {rows : List Le} {c : Le} :
    c ∈ upperRows idx rows ↔ c ∈ rows ∧ 0 < coeffAt idx c.form := by
  simp [upperRows]

@[simp]
theorem mem_zeroRows {idx : Nat} {rows : List Le} {c : Le} :
    c ∈ zeroRows idx rows ↔ c ∈ rows ∧ coeffAt idx c.form = 0 := by
  simp [zeroRows]

theorem cancelPair_mem_eliminate {idx : Nat} {rows : List Le} {lower upper : Le}
    (hlower : lower ∈ lowerRows idx rows)
    (hupper : upper ∈ upperRows idx rows) :
    cancelPair idx lower upper ∈ eliminate idx rows := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨lower, hlower, List.mem_map.mpr ⟨upper, hupper, rfl⟩⟩

/-- The reverse Fourier--Motzkin direction.  A rational valuation of the
projected rows extends to a rational valuation of all original rows. -/
theorem eliminate_complete {idx : Nat} {rows : List Le} {a : Valuation}
    (helim : ∀ c ∈ eliminate idx rows, Le.sat c a) :
    ∃ x : ℚ, ∀ c ∈ rows, Le.sat c (assignVar a idx x) := by
  by_cases hlower : lowerRows idx rows = []
  · by_cases hupper : upperRows idx rows = []
    · refine ⟨0, ?_⟩
      intro c hc
      rcases lt_trichotomy (coeffAt idx c.form) 0 with hneg | hzero | hpos
      · have hm : c ∈ lowerRows idx rows := mem_lowerRows.mpr ⟨hc, hneg⟩
        simp [hlower] at hm
      · apply sat_assign_of_coeff_zero hzero
        apply helim c
        exact List.mem_append.mpr (Or.inl (mem_zeroRows.mpr ⟨hc, hzero⟩))
      · have hm : c ∈ upperRows idx rows := mem_upperRows.mpr ⟨hc, hpos⟩
        simp [hupper] at hm
    · let bounds := (upperRows idx rows).map (boundary idx a)
      have hbounds : bounds ≠ [] := by
        simp [bounds, hupper]
      refine ⟨bounds.min hbounds, ?_⟩
      intro c hc
      rcases lt_trichotomy (coeffAt idx c.form) 0 with hneg | hzero | hpos
      · have hm : c ∈ lowerRows idx rows := mem_lowerRows.mpr ⟨hc, hneg⟩
        simp [hlower] at hm
      · apply sat_assign_of_coeff_zero hzero
        apply helim c
        exact List.mem_append.mpr (Or.inl (mem_zeroRows.mpr ⟨hc, hzero⟩))
      · apply sat_assign_of_upper_bound hpos
        apply List.min_le_of_mem
        exact List.mem_map.mpr ⟨c, mem_upperRows.mpr ⟨hc, hpos⟩, rfl⟩
  · let bounds := (lowerRows idx rows).map (boundary idx a)
    have hbounds : bounds ≠ [] := by
      simp [bounds, hlower]
    refine ⟨bounds.max hbounds, ?_⟩
    intro c hc
    rcases lt_trichotomy (coeffAt idx c.form) 0 with hneg | hzero | hpos
    · apply sat_assign_of_lower_bound hneg
      apply List.le_max_of_mem
      exact List.mem_map.mpr ⟨c, mem_lowerRows.mpr ⟨hc, hneg⟩, rfl⟩
    · apply sat_assign_of_coeff_zero hzero
      apply helim c
      exact List.mem_append.mpr (Or.inl (mem_zeroRows.mpr ⟨hc, hzero⟩))
    · apply sat_assign_of_upper_bound hpos
      apply (List.max_le_iff hbounds).2
      intro b hb
      obtain ⟨lower, hlowerMem, rfl⟩ := List.mem_map.mp hb
      have hlowerCoeff := (mem_lowerRows.mp hlowerMem).2
      apply boundary_le_boundary_of_cancelPair hlowerCoeff hpos
      apply helim
      exact cancelPair_mem_eliminate hlowerMem (mem_upperRows.mpr ⟨hc, hpos⟩)

/-- One-variable Fourier--Motzkin elimination preserves rational feasibility. -/
theorem feasible_eliminate_iff {idx : Nat} {rows : List Le} :
    (∃ a : Valuation, ∀ c ∈ rows, Le.sat c a) ↔
      ∃ a : Valuation, ∀ c ∈ eliminate idx rows, Le.sat c a := by
  constructor
  · rintro ⟨a, hrows⟩
    exact ⟨a, eliminate_sound hrows⟩
  · rintro ⟨a, helim⟩
    obtain ⟨x, hrows⟩ := eliminate_complete helim
    exact ⟨assignVar a idx x, hrows⟩

end LeanVIPR.Completeness.FourierMotzkin
