import LeanVIPRTactic

/-!
# Disjunctions encoded with a binary

Run as `examples/mip_tactic_tests.lean` is (`docs/TACTIC.md`). A disjunction of two
comparisons, or a `≠` over `ℕ` or `ℤ`, becomes a fresh `δ ∈ {0, 1}` with one indicator per
side, proved by cases on the disjunction; so `k` disjunctions cost one solver call where
splitting costs `2^k`. A disjunction with a side that has no finite big-M is split, as
before.
-/

-- 1. seven reals, each outside (2, 5) and at least 3, so each is at least 5; but they sum
-- to at most 34. Splitting needs 128 cases, over the cap of 64.
theorem gaps (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℝ)
    (b₁ : 3 ≤ x₁) (b₂ : 3 ≤ x₂) (b₃ : 3 ≤ x₃) (b₄ : 3 ≤ x₄) (b₅ : 3 ≤ x₅) (b₆ : 3 ≤ x₆)
    (b₇ : 3 ≤ x₇) (u₁ : x₁ ≤ 10) (u₂ : x₂ ≤ 10) (u₃ : x₃ ≤ 10) (u₄ : x₄ ≤ 10) (u₅ : x₅ ≤ 10)
    (u₆ : x₆ ≤ 10) (u₇ : x₇ ≤ 10)
    (h₁ : x₁ ≤ 2 ∨ 5 ≤ x₁) (h₂ : x₂ ≤ 2 ∨ 5 ≤ x₂) (h₃ : x₃ ≤ 2 ∨ 5 ≤ x₃)
    (h₄ : x₄ ≤ 2 ∨ 5 ≤ x₄) (h₅ : x₅ ≤ 2 ∨ 5 ≤ x₅) (h₆ : x₆ ≤ 2 ∨ 5 ≤ x₆)
    (h₇ : x₇ ≤ 2 ∨ 5 ≤ x₇)
    (hs : x₁ + x₂ + x₃ + x₄ + x₅ + x₆ + x₇ ≤ 34) : False := by
  mip

-- 2. the same with splitting forced fails at once, before solving any case
/-- would need 128 cases -/
#guard_msgs (substring := true) in
example (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℝ)
    (b₁ : 3 ≤ x₁) (b₂ : 3 ≤ x₂) (b₃ : 3 ≤ x₃) (b₄ : 3 ≤ x₄) (b₅ : 3 ≤ x₅) (b₆ : 3 ≤ x₆)
    (b₇ : 3 ≤ x₇) (u₁ : x₁ ≤ 10) (u₂ : x₂ ≤ 10) (u₃ : x₃ ≤ 10) (u₄ : x₄ ≤ 10) (u₅ : x₅ ≤ 10)
    (u₆ : x₆ ≤ 10) (u₇ : x₇ ≤ 10)
    (h₁ : x₁ ≤ 2 ∨ 5 ≤ x₁) (h₂ : x₂ ≤ 2 ∨ 5 ≤ x₂) (h₃ : x₃ ≤ 2 ∨ 5 ≤ x₃)
    (h₄ : x₄ ≤ 2 ∨ 5 ≤ x₄) (h₅ : x₅ ≤ 2 ∨ 5 ≤ x₅) (h₆ : x₆ ≤ 2 ∨ 5 ≤ x₆)
    (h₇ : x₇ ≤ 2 ∨ 5 ≤ x₇)
    (hs : x₁ + x₂ + x₃ + x₄ + x₅ + x₆ + x₇ ≤ 34) : False := by
  mip -encodeDisjunctions

-- 3. jobs of length 2, 3 and 4 on one machine within [0, 8], which needs 9
theorem sched (s₁ s₂ s₃ : ℤ) (h1 : 0 ≤ s₁) (h1' : s₁ + 2 ≤ 8) (h2 : 0 ≤ s₂) (h2' : s₂ + 3 ≤ 8)
    (h3 : 0 ≤ s₃) (h3' : s₃ + 4 ≤ 8)
    (d12 : s₁ + 2 ≤ s₂ ∨ s₂ + 3 ≤ s₁) (d13 : s₁ + 2 ≤ s₃ ∨ s₃ + 4 ≤ s₁)
    (d23 : s₂ + 3 ≤ s₃ ∨ s₃ + 4 ≤ s₂) : False := by
  mip

-- 4. `≠` over ℤ keeps its strength: read as `x + 1 ≤ y ∨ y + 1 ≤ x`
example (x y : ℤ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (h3 : 0 ≤ y) (h4 : y ≤ 1) (h5 : x ≠ y)
    (h6 : x + y ≠ 1) : False := by
  mip

-- 5. a side with no finite big-M (`x` has no upper bound) is split instead
example (x : ℤ) (h : x = 1 ∨ x = 2) (h2 : 3 ≤ x) : False := by
  mip

-- the axioms of the encoded proof are the standard three
/-- info: 'gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gaps
