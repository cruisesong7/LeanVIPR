module

public import LeanVIPR.Completeness.FourierMotzkin
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Constructive rational Farkas completeness

This module iterates the exact one-variable Fourier--Motzkin construction and
tracks every generated row back to a nonnegative combination of the original
rows.  An infeasible finite rational `≤` system therefore yields explicit
rational Farkas multipliers.
-/

namespace LeanVIPR.Completeness.FarkasCompleteness

open LeanVIPR.Cert LeanVIPR.Completeness.FourierMotzkin

/-- A finite rational `≤` system has no rational solution. -/
def RatInfeasible (rows : List Le) : Prop :=
  ∀ a : Valuation, (∀ c ∈ rows, Le.sat c a) → False

/-- Resolve multiplier indices against the original row list. -/
def resolveLe (base : List Le) (comb : List (ℚ × Nat)) : List (ℚ × Le) :=
  comb.map fun p => (p.1, base.getD p.2 default)

/-- Evaluation of an indexed combination of original rows. -/
def indexedEval (base : List Le) (comb : List (ℚ × Nat)) (a : Valuation) : ℚ :=
  (comb.map fun p => p.1 * LinForm.eval (base.getD p.2 default).form a).sum

/-- Right-hand side of an indexed combination of original rows. -/
def indexedRhs (base : List Le) (comb : List (ℚ × Nat)) : ℚ :=
  (comb.map fun p => p.1 * (base.getD p.2 default).rhs).sum

theorem resolveLe_eval (base : List Le) (comb : List (ℚ × Nat)) (a : Valuation) :
    LinForm.eval (combineForm (resolveLe base comb)) a = indexedEval base comb a := by
  rw [eval_combineForm]
  unfold resolveLe indexedEval
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rfl

theorem resolveLe_rhs (base : List Le) (comb : List (ℚ × Nat)) :
    (combine (resolveLe base comb)).rhs = indexedRhs base comb := by
  unfold LeanVIPR.Cert.combine resolveLe indexedRhs
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rfl

/-- A derived row together with explicit nonnegative multipliers on original rows. -/
structure Derived (base : List Le) (row : Le) where
  comb : List (ℚ × Nat)
  referencesPast : ∀ p ∈ comb, p.2 < base.length
  nonnegative : ∀ p ∈ comb, 0 ≤ p.1
  eval_eq : ∀ a, indexedEval base comb a = LinForm.eval row.form a
  rhs_eq : indexedRhs base comb = row.rhs

def scaleComb (q : ℚ) (comb : List (ℚ × Nat)) : List (ℚ × Nat) :=
  comb.map fun p => (q * p.1, p.2)

@[simp]
theorem indexedEval_append (base : List Le) (xs ys : List (ℚ × Nat)) (a : Valuation) :
    indexedEval base (xs ++ ys) a =
      indexedEval base xs a + indexedEval base ys a := by
  simp [indexedEval]

@[simp]
theorem indexedRhs_append (base : List Le) (xs ys : List (ℚ × Nat)) :
    indexedRhs base (xs ++ ys) = indexedRhs base xs + indexedRhs base ys := by
  simp [indexedRhs]

@[simp]
theorem indexedEval_scaleComb (base : List Le) (q : ℚ)
    (comb : List (ℚ × Nat)) (a : Valuation) :
    indexedEval base (scaleComb q comb) a = q * indexedEval base comb a := by
  induction comb with
  | nil => simp [scaleComb, indexedEval]
  | cons p comb ih =>
      change q * p.1 * LinForm.eval (base.getD p.2 default).form a +
          indexedEval base (scaleComb q comb) a =
        q * (p.1 * LinForm.eval (base.getD p.2 default).form a +
          indexedEval base comb a)
      rw [ih]
      ring

@[simp]
theorem indexedRhs_scaleComb (base : List Le) (q : ℚ) (comb : List (ℚ × Nat)) :
    indexedRhs base (scaleComb q comb) = q * indexedRhs base comb := by
  induction comb with
  | nil => simp [scaleComb, indexedRhs]
  | cons p comb ih =>
      change q * p.1 * (base.getD p.2 default).rhs +
          indexedRhs base (scaleComb q comb) =
        q * (p.1 * (base.getD p.2 default).rhs + indexedRhs base comb)
      rw [ih]
      ring

theorem derived_of_mem {base : List Le} {row : Le} (hrow : row ∈ base) :
    Nonempty (Derived base row) := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hrow
  refine ⟨
    { comb := [(1, i)]
      referencesPast := ?_
      nonnegative := ?_
      eval_eq := ?_
      rhs_eq := ?_ }⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hi
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    norm_num
  · intro a
    simp only [indexedEval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, one_mul]
    rw [List.getD_eq_getElem base default hi, hget]
  · simp only [indexedRhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, one_mul]
    rw [List.getD_eq_getElem base default hi, hget]

def Derived.combine {base : List Le} {left right : Le}
    (hleft : Derived base left) (hright : Derived base right)
    {qleft qright : ℚ} (hqleft : 0 ≤ qleft) (hqright : 0 ≤ qright) :
    Derived base (combine [(qleft, left), (qright, right)]) := by
  let comb := scaleComb qleft hleft.comb ++ scaleComb qright hright.comb
  refine
    { comb := comb
      referencesPast := ?_
      nonnegative := ?_
      eval_eq := ?_
      rhs_eq := ?_ }
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hleft.referencesPast q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hright.referencesPast q hq
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact mul_nonneg hqleft (hleft.nonnegative q hq)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact mul_nonneg hqright (hright.nonnegative q hq)
  · intro a
    simp only [comb, indexedEval_append, indexedEval_scaleComb]
    rw [hleft.eval_eq a, hright.eval_eq a]
    simp [LeanVIPR.Cert.combine, eval_combineForm]
  · simp only [comb, indexedRhs_append, indexedRhs_scaleComb]
    rw [hleft.rhs_eq, hright.rhs_eq]
    simp [LeanVIPR.Cert.combine]

theorem derived_cancelPair {base : List Le} {idx : Nat} {lower upper : Le}
    (hlower : Nonempty (Derived base lower))
    (hupper : Nonempty (Derived base upper))
    (hlowerCoeff : coeffAt idx lower.form < 0)
    (hupperCoeff : 0 < coeffAt idx upper.form) :
    Nonempty (Derived base (cancelPair idx lower upper)) := by
  obtain ⟨hlower⟩ := hlower
  obtain ⟨hupper⟩ := hupper
  exact ⟨hupper.combine hlower (neg_nonneg.mpr (le_of_lt hlowerCoeff))
    (le_of_lt hupperCoeff)⟩

/-- Eliminate a sequence of variables from left to right. -/
def eliminateMany : List Nat → List Le → List Le
  | [], rows => rows
  | idx :: rest, rows => eliminateMany rest (eliminate idx rows)

theorem feasible_eliminateMany_iff (vars : List Nat) (rows : List Le) :
    (∃ a : Valuation, ∀ c ∈ rows, Le.sat c a) ↔
      ∃ a : Valuation, ∀ c ∈ eliminateMany vars rows, Le.sat c a := by
  induction vars generalizing rows with
  | nil => rfl
  | cons idx rest ih =>
      rw [feasible_eliminate_iff]
      exact ih (eliminate idx rows)

theorem ratInfeasible_eliminateMany {vars : List Nat} {rows : List Le}
    (hinfeasible : RatInfeasible rows) :
    RatInfeasible (eliminateMany vars rows) := by
  intro a hrows
  have hnoBase : ¬∃ b : Valuation, ∀ c ∈ rows, Le.sat c b := by
    rintro ⟨b, hb⟩
    exact hinfeasible b hb
  have hnoFinal : ¬∃ b : Valuation, ∀ c ∈ eliminateMany vars rows, Le.sat c b := by
    simpa [feasible_eliminateMany_iff vars rows] using hnoBase
  exact hnoFinal ⟨a, hrows⟩

theorem eliminate_preserves_derived {base rows : List Le} {idx : Nat}
    (hrows : ∀ c ∈ rows, Nonempty (Derived base c)) :
    ∀ c ∈ eliminate idx rows, Nonempty (Derived base c) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hrows c (List.mem_of_mem_filter hc)
  · obtain ⟨lower, hlower, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨upper, hupper, rfl⟩ := List.mem_map.mp hc
    exact derived_cancelPair
      (hrows lower (List.mem_of_mem_filter hlower))
      (hrows upper (List.mem_of_mem_filter hupper))
      (of_decide_eq_true (List.mem_filter.mp hlower).2)
      (of_decide_eq_true (List.mem_filter.mp hupper).2)

theorem eliminateMany_preserves_derived {base rows : List Le} (vars : List Nat)
    (hrows : ∀ c ∈ rows, Nonempty (Derived base c)) :
    ∀ c ∈ eliminateMany vars rows, Nonempty (Derived base c) := by
  induction vars generalizing rows with
  | nil => exact hrows
  | cons idx rest ih =>
      exact ih (eliminate_preserves_derived hrows)

/-- The finite list of variable indices occurring in a row system. -/
def rowVars (rows : List Le) : List Nat :=
  rows.flatMap fun c => c.form.map Term.idx

/-- Every term in every row uses an index from `vars`. -/
def RowsSupported (vars : List Nat) (rows : List Le) : Prop :=
  ∀ c ∈ rows, ∀ t ∈ c.form, t.idx ∈ vars

theorem rowsSupported_rowVars (rows : List Le) : RowsSupported (rowVars rows) rows := by
  intro c hc t ht
  unfold rowVars
  apply List.mem_flatMap.mpr
  exact ⟨c, hc, List.mem_map.mpr ⟨t, ht, rfl⟩⟩

theorem mem_scale_index {q : ℚ} {f : LinForm} {t : Term}
    (ht : t ∈ LinForm.scale q f) :
    ∃ u ∈ f, t.idx = u.idx := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact ⟨u, hu, rfl⟩

theorem cancelPair_supported {vars : List Nat} {idx : Nat} {lower upper : Le}
    (hlower : ∀ t ∈ lower.form, t.idx ∈ vars)
    (hupper : ∀ t ∈ upper.form, t.idx ∈ vars) :
    ∀ t ∈ (cancelPair idx lower upper).form, t.idx ∈ vars := by
  intro t ht
  simp only [cancelPair, LeanVIPR.Cert.combine, combineForm] at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨u, hu, hidx⟩ := mem_scale_index ht
    rw [hidx]
    exact hupper u hu
  · have ht' : t ∈ LinForm.scale (coeffAt idx upper.form) lower.form := by
      simpa using ht
    obtain ⟨u, hu, hidx⟩ := mem_scale_index ht'
    rw [hidx]
    exact hlower u hu

theorem eliminate_preserves_supported {vars : List Nat} {idx : Nat} {rows : List Le}
    (hrows : RowsSupported vars rows) :
    RowsSupported vars (eliminate idx rows) := by
  intro c hc t ht
  rcases List.mem_append.mp hc with hc | hc
  · exact hrows c (List.mem_of_mem_filter hc) t ht
  · obtain ⟨lower, hlower, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨upper, hupper, rfl⟩ := List.mem_map.mp hc
    exact cancelPair_supported
      (hrows lower (List.mem_of_mem_filter hlower))
      (hrows upper (List.mem_of_mem_filter hupper)) t ht

theorem eliminateMany_supported {support : List Nat} {rows : List Le} (vars : List Nat)
    (hrows : RowsSupported support rows) :
    RowsSupported support (eliminateMany vars rows) := by
  induction vars generalizing rows with
  | nil => exact hrows
  | cons idx rest ih =>
      exact ih (eliminate_preserves_supported hrows)

theorem coeffAt_cancelPair (j idx : Nat) (lower upper : Le) :
    coeffAt j (cancelPair idx lower upper).form =
      -coeffAt idx lower.form * coeffAt j upper.form +
        coeffAt idx upper.form * coeffAt j lower.form := by
  simp [cancelPair, LeanVIPR.Cert.combine, coeff_combineForm]

theorem eliminate_preserves_coeff_zero {j idx : Nat} {rows : List Le}
    (hrows : ∀ c ∈ rows, coeffAt j c.form = 0) :
    ∀ c ∈ eliminate idx rows, coeffAt j c.form = 0 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hrows c (List.mem_of_mem_filter hc)
  · obtain ⟨lower, hlower, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨upper, hupper, rfl⟩ := List.mem_map.mp hc
    rw [coeffAt_cancelPair, hrows lower (List.mem_of_mem_filter hlower),
      hrows upper (List.mem_of_mem_filter hupper)]
    ring

theorem eliminateMany_preserves_coeff_zero {j : Nat} {rows : List Le}
    (vars : List Nat) (hrows : ∀ c ∈ rows, coeffAt j c.form = 0) :
    ∀ c ∈ eliminateMany vars rows, coeffAt j c.form = 0 := by
  induction vars generalizing rows with
  | nil => exact hrows
  | cons idx rest ih =>
      exact ih (eliminate_preserves_coeff_zero hrows)

theorem eliminateMany_coeff_zero_of_mem {j : Nat} {rows : List Le} {vars : List Nat}
    (hj : j ∈ vars) :
    ∀ c ∈ eliminateMany vars rows, coeffAt j c.form = 0 := by
  induction vars generalizing rows with
  | nil => simp at hj
  | cons idx rest ih =>
      rcases List.mem_cons.mp hj with rfl | hj
      · exact eliminateMany_preserves_coeff_zero rest fun c hc =>
          eliminate_coeff_zero hc
      · exact ih hj

theorem coeffAt_eq_zero_of_index_absent {idx : Nat} {f : LinForm}
    (h : ∀ t ∈ f, t.idx ≠ idx) :
    coeffAt idx f = 0 := by
  induction f with
  | nil => rfl
  | cons t f ih =>
      have ht := h t (by simp)
      have hf : ∀ u ∈ f, u.idx ≠ idx := by
        intro u hu
        exact h u (by simp [hu])
      simp [coeffAt, ht, ih hf]

/-- Convert a sparse form to the corresponding finitely supported coefficient map. -/
noncomputable def toFinsupp : LinForm → Nat →₀ ℚ
  | [] => 0
  | t :: f => Finsupp.single t.idx t.coeff + toFinsupp f

@[simp]
theorem toFinsupp_apply (f : LinForm) (idx : Nat) :
    toFinsupp f idx = coeffAt idx f := by
  induction f with
  | nil => simp [toFinsupp, coeffAt]
  | cons t f ih =>
      by_cases h : t.idx = idx
      · simp [toFinsupp, coeffAt, h, ih]
      · simp [toFinsupp, coeffAt, h, ih]

theorem eval_eq_finsupp_sum (f : LinForm) (a : Valuation) :
    LinForm.eval f a = (toFinsupp f).sum fun idx q => q * a idx := by
  induction f with
  | nil => simp [LinForm.eval, toFinsupp]
  | cons t f ih =>
      rw [show LinForm.eval (t :: f) a = t.coeff * a t.idx + LinForm.eval f a by
        simp [LinForm.eval]]
      rw [ih]
      rw [show toFinsupp (t :: f) =
        Finsupp.single t.idx t.coeff + toFinsupp f by rfl]
      rw [Finsupp.sum_add_index']
      · simp
      · intro idx
        ring
      · intro idx q₁ q₂
        ring

theorem eval_eq_zero_of_coeffAt_eq_zero {f : LinForm}
    (hcoeff : ∀ idx, coeffAt idx f = 0) (a : Valuation) :
    LinForm.eval f a = 0 := by
  rw [eval_eq_finsupp_sum]
  have hz : toFinsupp f = 0 := by
    ext idx
    simp [hcoeff idx]
  rw [hz]
  simp

theorem final_form_zero {rows : List Le} {c : Le}
    (hc : c ∈ eliminateMany (rowVars rows) rows) :
    ∀ a, LinForm.eval c.form a = 0 := by
  apply eval_eq_zero_of_coeffAt_eq_zero
  intro idx
  by_cases hidx : idx ∈ rowVars rows
  · exact eliminateMany_coeff_zero_of_mem hidx c hc
  · apply coeffAt_eq_zero_of_index_absent
    intro t ht hti
    apply hidx
    rw [← hti]
    exact eliminateMany_supported (rowVars rows) (rowsSupported_rowVars rows) c hc t ht

theorem exists_negative_rhs {rows : List Le}
    (hinfeasible : RatInfeasible rows)
    (hzero : ∀ c ∈ rows, ∀ a, LinForm.eval c.form a = 0) :
    ∃ c ∈ rows, c.rhs < 0 := by
  by_contra h
  have hrhs : ∀ c ∈ rows, 0 ≤ c.rhs := by
    intro c hc
    exact le_of_not_gt fun hneg => h ⟨c, hc, hneg⟩
  apply hinfeasible (fun _ => 0)
  intro c hc
  rw [Le.sat, hzero c hc]
  exact hrhs c hc

/-- Explicit rational Farkas multipliers for a finite `≤` system. -/
structure FarkasCertificate (base : List Le) where
  comb : List (ℚ × Nat)
  referencesPast : ∀ p ∈ comb, p.2 < base.length
  nonnegative : ∀ p ∈ comb, 0 ≤ p.1
  zero : ∀ a, indexedEval base comb a = 0
  negative : indexedRhs base comb < 0

/-- Constructive rational Farkas completeness for finite sparse `≤` systems. -/
theorem rationalFarkas_complete_le {rows : List Le}
    (hinfeasible : RatInfeasible rows) :
    Nonempty (FarkasCertificate rows) := by
  let final := eliminateMany (rowVars rows) rows
  have hfinalInfeasible : RatInfeasible final :=
    ratInfeasible_eliminateMany hinfeasible
  have hnegative : ∃ c ∈ final, c.rhs < 0 :=
    exists_negative_rhs hfinalInfeasible fun c hc => final_form_zero hc
  obtain ⟨c, hc, hcneg⟩ := hnegative
  have hderived : Nonempty (Derived rows c) :=
    eliminateMany_preserves_derived (rowVars rows) (fun d hd => derived_of_mem hd) c hc
  obtain ⟨d⟩ := hderived
  refine ⟨
    { comb := d.comb
      referencesPast := d.referencesPast
      nonnegative := d.nonnegative
      zero := ?_
      negative := ?_ }⟩
  · intro a
    rw [d.eval_eq a, final_form_zero hc a]
  · rw [d.rhs_eq]
    exact hcneg

/-- A Farkas certificate is directly a valid leaf of the branch-and-cut tree model. -/
theorem FarkasCertificate.refTreeValid {base : List Le}
    (cert : FarkasCertificate base) (isInt : Nat → Prop) :
    RefTree.Valid isInt base (.leaf (resolveLe base cert.comb)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact cert.nonnegative q hq
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hqLt := cert.referencesPast q hq
    rw [List.getD_eq_getElem base default hqLt]
    exact List.getElem_mem hqLt
  · intro a
    rw [← eval_combineForm, resolveLe_eval, cert.zero]
  · change (combine (resolveLe base cert.comb)).rhs < 0
    rw [resolveLe_rhs]
    exact cert.negative

/-- Every rationally infeasible `≤` system has a valid Farkas leaf. -/
theorem ratInfeasible_has_refTree_leaf {base : List Le} (isInt : Nat → Prop)
    (hinfeasible : RatInfeasible base) :
    ∃ tree, RefTree.Valid isInt base tree := by
  obtain ⟨cert⟩ := rationalFarkas_complete_le hinfeasible
  exact ⟨.leaf (resolveLe base cert.comb), cert.refTreeValid isInt⟩

end LeanVIPR.Completeness.FarkasCompleteness
