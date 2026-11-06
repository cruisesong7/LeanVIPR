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

/-- Normalize a linear form by accumulating each term into an association list.

Not what the checker runs — `normForm` is — but it is the obvious way to write the
normalization, so `LeanVIPR.Thm.System.LinForm.normForm_eval_eq_assoc` cross-checks the
one against the other. It is quadratic in the number of terms, which on a certificate
whose objective mentions 280k variables costs hours. -/
def normFormAssoc (f : LinForm) : List (Nat × ℚ) :=
  f.foldl (fun acc t => addTerm acc t.idx t.coeff) []

/-- Fold runs of equal keys in a key-sorted list. -/
def combineAdj : List (Nat × ℚ) → List (Nat × ℚ)
  | [] => []
  | [p] => [p]
  | (i, a) :: (j, b) :: rest =>
      if i = j then combineAdj ((i, a + b) :: rest)
      else (i, a) :: combineAdj ((j, b) :: rest)
  termination_by l => l.length

/-! ### Sorting association lists by key

`List.mergeSort` would do, but it is defined by well-founded recursion and the Lean
kernel cannot reduce it, so kernel mode gets stuck on any certificate with a `lin` or
`rnd` step. The sort below is structurally recursive on a fuel argument, which both the
compiler and the kernel can run. Soundness never appeals to the fuel being sufficient:
`sortKV` permutes its input for every fuel, and only the distinct-keys argument in
`LeanVIPR.Thm.System.RuleComplete` needs the output to be sorted. -/

/-- Merge two key-sorted association lists. -/
def mergeKV : Nat → List (Nat × ℚ) → List (Nat × ℚ) → List (Nat × ℚ)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
      if x.1 ≤ y.1 then x :: mergeKV n xs (y :: ys) else y :: mergeKV n (x :: xs) ys

/-- Deal a list alternately into two lists of nearly equal length. -/
def splitAlt : List (Nat × ℚ) → List (Nat × ℚ) × List (Nat × ℚ)
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: rest => (a :: (splitAlt rest).1, b :: (splitAlt rest).2)

/-- Merge sort by key, with `fuel` bounding the recursion depth. -/
def msortKV : Nat → List (Nat × ℚ) → List (Nat × ℚ)
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | n + 1, a :: b :: rest =>
      let s := splitAlt (a :: b :: rest)
      mergeKV (s.1.length + s.2.length) (msortKV n s.1) (msortKV n s.2)

/-- Sort an association list by key. The list's own length is enough fuel. -/
def sortKV (l : List (Nat × ℚ)) : List (Nat × ℚ) := msortKV l.length l

/-! ### Normalizing by dense accumulation

Summing coefficients per index needs no comparisons at all when the indices are dense:
one array slot per variable, one addition per term, then a scan. That is `O(m + n)` for
`m` terms spanning `n` indices, against `O(m log m)` for the sort, and it allocates once
rather than per element. On the benchmark corpus it is 4x to 12x faster.

It is only better while `n` stays within a constant of `m`. A form with two terms whose
indices are 280000 apart would have the scan dominate everything, so `normForm` keeps the
sort for that case and picks between them. -/

/-- One past the largest index appearing in `f`. -/
def formWidth (f : LinForm) : Nat := f.foldl (fun w t => max w (t.idx + 1)) 0

/-- Add every term of `f` into a dense array of coefficients indexed by variable. -/
def denseAccum (n : Nat) (f : LinForm) : Array ℚ :=
  f.foldl (fun a t => a.set! t.idx (a[t.idx]! + t.coeff)) (Array.replicate n (0 : ℚ))

/-- The nonzero entries of a coefficient array, by ascending index. Counts down so the
result is built in ascending order without a reversal. -/
def collectNZ (arr : Array ℚ) : Nat → List (Nat × ℚ) → List (Nat × ℚ)
  | 0, acc => acc
  | i + 1, acc => collectNZ arr i (if arr[i]! == 0 then acc else (i, arr[i]!) :: acc)

/-- Normalize a linear form to per-index coefficient sums.

Dense accumulation when the indices are dense enough to pay for the scan, otherwise sort
and fold runs of equal indices. The two return different lists — dense drops entries that
cancel to zero, and the sort keeps them — and nothing may depend on which is used. What
the checker asks of either is proved of both: they agree on the value of the form
(`LeanVIPR.Thm.System.LinForm.normForm_eval`) and both leave the keys distinct
(`LeanVIPR.Thm.System.RuleComplete.normForm_keys_nodup`). Every test the checker runs on
the result — all coefficients zero, all coefficients integral, the value at a valuation —
is invariant under permutation and under dropping zeros. -/
def normFormDense (f : LinForm) : List (Nat × ℚ) :=
  let n := formWidth f
  collectNZ (denseAccum n f) n []

/-- Normalize by sorting on the index and folding runs of equal indices.

Slower than `normFormDense` when compiled, but it is plain structural list recursion,
which is also what the Lean kernel reduces cheaply: the kernel has neither in-place
writes nor contiguous random access, so `normFormDense` degrades to `O(m * n)` there.
`normForm` therefore costs kernel mode something, which measured as roughly 25% on two of
three kernel-mode examples. Giving each mode its own normalization would need the checker
parameterized by one, which it is not. -/
def normFormSort (f : LinForm) : List (Nat × ℚ) :=
  combineAdj (sortKV (f.map (fun t => (t.idx, t.coeff))))

/-- The normalization the compiled checker runs: dense accumulation where the index range
pays for itself, the sort otherwise. -/
def normForm (f : LinForm) : List (Nat × ℚ) :=
  if formWidth f ≤ 8 * f.length + 64 then normFormDense f else normFormSort f

end LeanVIPR.Semantics
