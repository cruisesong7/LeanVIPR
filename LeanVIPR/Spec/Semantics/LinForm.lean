module

public import LeanVIPR.Spec.Semantics.LinCon
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Linear-form algebra

Shared vocabulary for VIPR rows: scaling and combining sparse linear forms, the
normalized form, and the refutation trees the proof system is phrased over. Definitions
only; the algebraic facts about them are in `LeanVIPR.Thm.System.LinForm`, and the executable
tests that decide them are in `LeanVIPR.Impl.Checker.Form`.
-/

namespace LeanVIPR.Semantics

open Classical


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

/-- The `Le` obtained from a nonnegative combination of rows: linear part
`combineForm comb`, right-hand side `Σ yᵢ · cᵢ.rhs`. -/
def combine (comb : List (ℚ × Le)) : Le :=
  ⟨combineForm comb, (comb.map (fun p => p.1 * p.2.rhs)).sum⟩

/-! ## Integer rounding (`rnd`) -/

/-- A rational is integral if it is the cast of some integer. -/
def IsIntVal (q : ℚ) : Prop := ∃ n : ℤ, q = (n : ℚ)

/-! ## Integer split (`uns`) -/

/-- The branch constraint `x_i ≤ k`. -/
def leLower (i : Nat) (k : ℚ) : Le := ⟨[⟨i, 1⟩], k⟩

/-- The branch constraint `x_i ≥ k+1`, normalized to `-x_i ≤ -(k+1)`. -/
def leUpper (i : Nat) (k : ℚ) : Le := ⟨[⟨i, -1⟩], -(k + 1)⟩

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

/-- Normalize a linear form to per-index coefficient sums. -/
def normForm (f : LinForm) : List (Nat × ℚ) :=
  f.foldl (fun acc t => addTerm acc t.idx t.coeff) []

end LeanVIPR.Semantics
