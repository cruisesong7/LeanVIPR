module

public import LeanVIPR.Impl.Form

@[expose] public section

/-!
# Facts about linear forms

Algebra over the sparse representation, and the agreement of the executable tests in
`LeanVIPR.Impl.Form` with the notions of `LeanVIPR.Spec.LinForm`. Infrastructure: these
are used throughout the soundness development rather than cited on their own.
-/

namespace LeanVIPR.Semantics

open Classical


variable {α : Type*}

/-- Pointwise-`≤` implies `≤` on list sums.
`private`). -/
theorem list_sum_le (l : List α) (f g : α → ℚ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have h0 : f a ≤ g a := h a (by simp)
      have iht : (t.map f).sum ≤ (t.map g).sum :=
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      linarith

theorem eval_combineForm (comb : List (ℚ × Le)) (a : Valuation) :
    (combineForm comb).eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  induction comb with
  | nil => simp [combineForm, LinForm.eval]
  | cons p ps ih =>
      simp only [combineForm, LinForm.eval_append, LinForm.eval_scale, ih,
        List.map_cons, List.sum_cons]

/-- **`lin` soundness (general form).**  If every row used in a nonnegative
combination holds at `a`, so does the combined row.  This is the "implication"
generalization of `farkas_le`. -/
theorem lin_sound (comb : List (ℚ × Le)) (a : Valuation)
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hsat : ∀ p ∈ comb, Le.sat p.2 a) :
    Le.sat (combine comb) a := by
  show (combine comb).form.eval a ≤ (combine comb).rhs
  simp only [combine, eval_combineForm]
  exact list_sum_le comb _ _ fun p hp => mul_le_mul_of_nonneg_left (hsat p hp) (hnn p hp)

theorem isIntVal_cast (n : ℤ) : IsIntVal ((n : ℚ)) := ⟨n, rfl⟩

/-- If every term of a form has integral coefficient and integral variable value at
`a`, the form evaluates to an integer at `a`. -/
theorem LinForm.eval_isInt (f : LinForm) (a : Valuation)
    (h : ∀ t ∈ f, IsIntVal t.coeff ∧ IsIntVal (a t.idx)) :
    IsIntVal (f.eval a) := by
  induction f with
  | nil => exact ⟨0, by simp [LinForm.eval]⟩
  | cons t ts ih =>
      obtain ⟨⟨c, hc⟩, ⟨v, hv⟩⟩ := h t (by simp)
      obtain ⟨m, hm⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
      refine ⟨c * v + m, ?_⟩
      have hm' : (ts.map (fun t => t.coeff * a t.idx)).sum = (m : ℚ) := hm
      simp only [LinForm.eval, List.map_cons, List.sum_cons]
      rw [hc, hv, hm']
      push_cast; ring

/-- **`rnd` soundness.**  If `form ≤ β` at `a` and `form.eval a` is an integer, then
`form ≤ ⌊β⌋` at `a`. -/
theorem rnd_sound (form : LinForm) (β : ℚ) (a : Valuation)
    (hInt : IsIntVal (form.eval a))
    (hsat : Le.sat ⟨form, β⟩ a) :
    Le.sat ⟨form, ((⌊β⌋ : ℤ) : ℚ)⟩ a := by
  obtain ⟨n, hn⟩ := hInt
  show form.eval a ≤ ((⌊β⌋ : ℤ) : ℚ)
  have hsat' : form.eval a ≤ β := hsat
  have hnβ : (n : ℚ) ≤ β := by rw [← hn]; exact hsat'
  have hfloor : n ≤ ⌊β⌋ := Int.le_floor.mpr hnβ
  rw [hn]; exact_mod_cast hfloor

theorem sat_leLower (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leLower i k) a ↔ a i ≤ k := by
  unfold leLower Le.sat LinForm.eval
  simp

theorem sat_leUpper (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leUpper i k) a ↔ k + 1 ≤ a i := by
  unfold leUpper Le.sat LinForm.eval
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor <;> intro h <;> linarith

theorem isIntValB_sound {q : ℚ} (h : isIntValB q = true) : IsIntVal q := by
  have hden : q.den = 1 := by simp only [isIntValB, beq_iff_eq] at h; exact h
  have key : ((q.num : ℤ) : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd
    simpa using hnd
  exact ⟨q.num, key.symm⟩

theorem addTerm_eval (al : List (Nat × ℚ)) (i : Nat) (c : ℚ) (a : Valuation) :
    evalAL (addTerm al i c) a = evalAL al a + c * a i := by
  induction al with
  | nil => simp [addTerm]
  | cons hd tl ih =>
      obtain ⟨j, d⟩ := hd
      by_cases heq : i = j
      · subst heq
        simp only [addTerm, beq_self_eq_true, ite_true, evalAL_cons]; ring
      · have hcond : ¬ ((i == j) = true) := by rw [beq_iff_eq]; exact heq
        simp only [addTerm, ite_eq_right hcond, evalAL_cons, ih]; ring

theorem normForm_foldl_eval (f : LinForm) (al : List (Nat × ℚ)) (a : Valuation) :
    evalAL (f.foldl (fun acc t => addTerm acc t.idx t.coeff) al) a
      = evalAL al a + f.eval a := by
  induction f generalizing al with
  | nil => simp [LinForm.eval]
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih (addTerm al t.idx t.coeff), addTerm_eval]
      have : LinForm.eval (t :: ts) a = t.coeff * a t.idx + LinForm.eval ts a := by
        simp [LinForm.eval]
      rw [this]; ring

theorem normForm_eval (f : LinForm) (a : Valuation) : evalAL (normForm f) a = f.eval a := by
  simpa [normForm] using normForm_foldl_eval f [] a

end LeanVIPR.Semantics
