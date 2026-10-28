module

public import LeanVIPR.Cert.LinCon
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Linear-form algebra for VIPR rows

Shared algebra over the sparse `Le` / `LinForm` / `Valuation` representation of
`LeanVIPR.Cert.LinCon`:

* combinations of rows (`combineForm`, `combine`) and their soundness (`lin_sound`);
* integer rounding (`rnd_sound`) and integrality of forms (`LinForm.eval_isInt`);
* the branch rows `leLower` / `leUpper` of an integer split;
* the refutation-tree model `RefTree` used by the completeness development;
* normalization of a form to per-index coefficient sums (`normForm`), which the
  executable rule checks use to decide identities between forms.
-/

namespace LeanVIPR.Cert

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

/-! ## Combining rows (`lin`) -/

/-- Scale every coefficient of a linear form by `y`. -/
def LinForm.scale (y : ℚ) (f : LinForm) : LinForm :=
  f.map (fun t => ⟨t.idx, y * t.coeff⟩)

@[simp] theorem LinForm.eval_append (f g : LinForm) (a : Valuation) :
    (f ++ g).eval a = f.eval a + g.eval a := by
  unfold LinForm.eval
  rw [List.map_append, List.sum_append]

@[simp] theorem LinForm.eval_scale (y : ℚ) (f : LinForm) (a : Valuation) :
    (LinForm.scale y f).eval a = y * f.eval a := by
  induction f with
  | nil => simp [LinForm.scale, LinForm.eval]
  | cons t ts ih =>
      unfold LinForm.scale LinForm.eval
      simp only [List.map_cons, List.sum_cons]
      -- reduce the tail via the induction hypothesis (stated with `scale`/`eval`)
      have key : ((ts.map (fun t => (⟨t.idx, y * t.coeff⟩ : Term))).map
                    (fun t => t.coeff * a t.idx)).sum
                = y * (ts.map (fun t => t.coeff * a t.idx)).sum := by
        have := ih
        unfold LinForm.scale LinForm.eval at this
        simpa using this
      rw [key]; ring

/-- The linear form of a nonnegative combination `[(y₁,c₁), …]`: the concatenation of
the scaled forms `yᵢ · cᵢ.form`. -/
def combineForm : List (ℚ × Le) → LinForm
  | [] => []
  | p :: ps => LinForm.scale p.1 p.2.form ++ combineForm ps

theorem eval_combineForm (comb : List (ℚ × Le)) (a : Valuation) :
    (combineForm comb).eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  induction comb with
  | nil => simp [combineForm, LinForm.eval]
  | cons p ps ih =>
      simp only [combineForm, LinForm.eval_append, LinForm.eval_scale, ih,
        List.map_cons, List.sum_cons]

/-- The `Le` obtained from a nonnegative combination of rows: linear part
`combineForm comb`, right-hand side `Σ yᵢ · cᵢ.rhs`. -/
def combine (comb : List (ℚ × Le)) : Le :=
  ⟨combineForm comb, (comb.map (fun p => p.1 * p.2.rhs)).sum⟩

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

/-! ## Integer rounding (`rnd`) -/

/-- A rational is integral if it is the cast of some integer. -/
def IsIntVal (q : ℚ) : Prop := ∃ n : ℤ, q = (n : ℚ)

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

/-! ## Integer split (`uns`) -/

/-- The branch constraint `x_i ≤ k`. -/
def leLower (i : Nat) (k : ℚ) : Le := ⟨[⟨i, 1⟩], k⟩
/-- The branch constraint `x_i ≥ k+1`, normalized to `-x_i ≤ -(k+1)`. -/
def leUpper (i : Nat) (k : ℚ) : Le := ⟨[⟨i, -1⟩], -(k + 1)⟩

theorem sat_leLower (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leLower i k) a ↔ a i ≤ k := by
  unfold leLower Le.sat LinForm.eval
  simp

theorem sat_leUpper (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leUpper i k) a ↔ k + 1 ≤ a i := by
  unfold leUpper Le.sat LinForm.eval
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor <;> intro h <;> linarith

/-! ## Branch-and-bound refutation trees: the automatic "proof by cases" checker

A VIPR `RTP infeas` certificate is, in essence, a proof by cases: `lin` leaves
refute LP branches, and `uns` splits combine the branches of an integer variable.
We model that directly as a refutation *tree* — the tree structure carries the
case-split ("assumption") bookkeeping, so a leaf's rows are exactly the branch bounds
accumulated on the path to it. A separate completeness argument is required to show
that every infeasible rational MILP admits a finite tree of this form. -/

/-- A branch-and-bound refutation: a direct Farkas combination refuting the current
rows (`leaf`), or an integer split on variable `i` at `k` with refutations of both
branches `x_i ≤ k` and `x_i ≥ k+1` (`split`). -/
inductive RefTree where
  | leaf (comb : List (ℚ × Le))
  | split (i : Nat) (k : ℤ) (lo hi : RefTree)
  | derive (comb : List (ℚ × Le)) (rnd : Bool) (sub : RefTree)

/-- The row a `derive` node introduces: the nonnegative combination `combine comb`,
optionally with its right-hand side rounded down (a `rnd`/cut step). -/
def deriveRow (comb : List (ℚ × Le)) (rnd : Bool) : Le :=
  if rnd then ⟨combineForm comb, ((⌊(combine comb).rhs⌋ : ℤ) : ℚ)⟩ else combine comb

/-- Decidable "is an integer" for `ℚ`. -/
def isIntValB (q : ℚ) : Bool := q.den == 1

theorem isIntValB_sound {q : ℚ} (h : isIntValB q = true) : IsIntVal q := by
  have hden : q.den = 1 := by simp only [isIntValB, beq_iff_eq] at h; exact h
  have key : ((q.num : ℤ) : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd
    simpa using hnd
  exact ⟨q.num, key.symm⟩

/-- Validity of a refutation tree against a row set and an integrality predicate.
`leaf comb`: nonnegative multipliers on rows drawn from `rows`, whose combination
cancels identically and has negative constant. `split i k lo hi`: `i` is
integer-constrained and each branch refutes `rows` extended with its bound. -/
def RefTree.Valid (isInt : Nat → Prop) : List Le → RefTree → Prop
  | rows, .leaf comb =>
      (∀ p ∈ comb, 0 ≤ p.1) ∧ (∀ p ∈ comb, p.2 ∈ rows) ∧
      (∀ a, (comb.map (fun p => p.1 * p.2.form.eval a)).sum = 0) ∧
      ((comb.map (fun p => p.1 * p.2.rhs)).sum < 0)
  | rows, .split i k lo hi =>
      isInt i ∧
      RefTree.Valid isInt (leLower i (k : ℚ) :: rows) lo ∧
      RefTree.Valid isInt (leUpper i (k : ℚ) :: rows) hi
  | rows, .derive comb rnd sub =>
      (∀ p ∈ comb, 0 ≤ p.1) ∧ (∀ p ∈ comb, p.2 ∈ rows) ∧
      (rnd = true → ∀ t ∈ combineForm comb, IsIntVal t.coeff ∧ isInt t.idx) ∧
      RefTree.Valid isInt (deriveRow comb rnd :: rows) sub

/-! ## Normalized forms

Identities between forms, such as identical cancellation `∀ a, f.eval a = 0`, are
decided by normalizing a form to per-index coefficient sums (`normForm`) and testing
the normalized coefficients (`formIsZero`). -/

/-- Value of a per-index coefficient association list at `a`. -/
def evalAL (al : List (Nat × ℚ)) (a : Valuation) : ℚ := (al.map (fun p => p.2 * a p.1)).sum

@[simp] theorem evalAL_nil (a : Valuation) : evalAL [] a = 0 := rfl
@[simp] theorem evalAL_cons (p : Nat × ℚ) (tl : List (Nat × ℚ)) (a : Valuation) :
    evalAL (p :: tl) a = p.2 * a p.1 + evalAL tl a := by simp [evalAL]

/-- Accumulate `(i, c)` into a per-index coefficient association list. -/
def addTerm : List (Nat × ℚ) → Nat → ℚ → List (Nat × ℚ)
  | [], i, c => [(i, c)]
  | (j, d) :: rest, i, c => if i == j then (j, d + c) :: rest else (j, d) :: addTerm rest i c

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

/-- Normalize a linear form to per-index coefficient sums. -/
def normForm (f : LinForm) : List (Nat × ℚ) :=
  f.foldl (fun acc t => addTerm acc t.idx t.coeff) []

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

/-- A linear form is identically zero if all its normalized coefficients vanish. -/
def formIsZero (f : LinForm) : Bool := (normForm f).all (fun p => p.2 == 0)

end LeanVIPR.Cert
