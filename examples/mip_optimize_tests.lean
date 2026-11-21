import LeanVIPRTactic

/-!
# `mip_maximize` and `mip_minimize` tests

Run as `examples/mip_tactic_tests.lean` is (`docs/TACTIC.md`). Each call asks exact SCIP to
optimize, checks the `RTP range` certificate in the kernel, and adds `hbound`. Case 6 goes
through the integer fallback: SCIP's range certificate there has no objective-bound row
(scipopt/scip#305), so the bound is proved by `mip` instead, refuting `n ≥ 4`.
-/

-- 1. integer objective: the LP optimum is 6.5, the integer one 6
example (x y : ℤ) (h1 : x + y ≤ 4) (h2 : x - y ≤ 1) (h3 : 0 ≤ y) : 2*x + y ≤ 6 := by
  mip_maximize 2*x + y
  exact hbound
-- 2. the textbook LP from leanprover/lp's README: optimum 36
example (x₀ x₁ : ℚ) (_ : x₀ ≤ 4) (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18)
    (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) : 3 * x₀ + 5 * x₁ ≤ 36 := by
  mip_maximize 3 * x₀ + 5 * x₁
  exact hbound
-- 3. mixed: the LP maximum of x is 5/2, but x is an integer
example (x : ℤ) (y : ℚ) (h1 : (x : ℚ) + y ≤ 5/2) (h2 : 0 ≤ y) (h3 : y ≤ 1) : (x : ℚ) ≤ 2 := by
  mip_maximize (x : ℚ)
  exact hbound
-- 4. minimizing over the reals
example (a b : ℝ) (h1 : 1 ≤ a + b) (h2 : 0 ≤ a) (h3 : 0 ≤ b) : 2 ≤ 2*a + 3*b := by
  mip_minimize 2*a + 3*b
  exact hbound
-- 5. a named hypothesis
example (x y : ℤ) (h1 : x + y ≤ 4) (h2 : x - y ≤ 1) (h3 : 0 ≤ y) : x ≤ 2 := by
  mip_maximize hx : x
  exact hx
-- 6. naturals, where 2n ≤ 7 gives n ≤ 3
example (n : ℕ) (h : 2 * n ≤ 7) : n ≤ 3 := by
  mip_maximize n
  exact hbound
-- 7. an objective with a constant term
example (x : ℤ) (h1 : x ≤ 3) : x + 10 ≤ 13 := by
  mip_maximize x + 10
  exact hbound
-- 8. inconsistent hypotheses close the goal
example (x : ℤ) (h1 : 1 ≤ x) (h2 : x ≤ 0) : (1 : ℕ) = 2 := by
  mip_maximize x
-- 9. unbounded: must fail
example (x : ℤ) (h1 : 0 ≤ x) : True := by
  fail_if_success mip_maximize x
  trivial
