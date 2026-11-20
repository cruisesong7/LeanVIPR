import LeanVIPRTactic

/-!
# `mip` regression tests

Run with a certifying SCIP (`docs/TACTIC.md`):

```
LEANVIPR_SCIP=~/scip-exact/scipoptsuite-10.0.1/build/bin/scip lake env lean examples/mip_tactic_tests.lean
```

Each `by mip` asks exact SCIP for an infeasibility certificate and checks it in the kernel.
Two of these are out of reach of the usual tactics: Pugh's problem (1) needs the omega
test's dark shadow, which Lean's `omega` does not implement, and its LP relaxation is
feasible, so no Farkas argument (`linarith`, `lp`) proves it either; (9) is infeasible
only because `x` is an integer, in a problem with a rational variable, which `omega`
cannot state and `linarith` cannot use. The last two must fail.
-/

-- 1. Pugh's dark-shadow problem: `omega` cannot prove it
example (x y : ℤ) (h1 : 27 ≤ 11*x + 13*y) (h2 : 11*x + 13*y ≤ 45)
    (h3 : -10 ≤ 7*x - 9*y) (h4 : 7*x - 9*y ≤ 4) : False := by mip
-- 2. the roadmap's knapsack, as ¬ ∃
example : ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
    6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by mip
-- 3. a comparison goal
example (x y : ℤ) (h1 : x + y ≤ 3) (h2 : 0 ≤ y) : x ≤ 3 := by mip
-- 4. an equality goal (its negation is a ≠, split into < and >)
example (x : ℤ) (h1 : x ≤ 2) (h2 : 2 ≤ x) : x = 2 := by mip
-- 5. a ≠ hypothesis
example (x : ℤ) (h : x ≠ 0) (h1 : 0 ≤ x) (h2 : x ≤ 0) : False := by mip
-- 6. a ∨ hypothesis
example (x : ℤ) (h : x ≤ -1 ∨ 5 ≤ x) (h1 : 0 ≤ x) (h2 : x ≤ 4) : False := by mip
-- 7. natural numbers
example (n m : ℕ) (h : 2*n + 3*m = 7) (h2 : n ≤ 1) : False := by mip
-- 8. mixed ℤ and ℚ, infeasible already as an LP
example (x : ℤ) (y : ℚ) (h1 : 2 * (x : ℚ) + y ≤ 1) (h2 : 1 ≤ y) (h3 : 1 ≤ x) : False := by mip
-- 9. mixed ℤ and ℚ, infeasible only because x is an integer
example (x : ℤ) (y : ℚ) (h1 : 2 * (x : ℚ) = 1 + 2 * y) (h2 : 0 ≤ y) (h3 : y ≤ 1/4) :
    False := by mip
-- 10. reals with decimal coefficients
example (a b : ℝ) (h1 : 0.5 * a + b ≤ 1) (h2 : 2 ≤ a) (h3 : 0.25 ≤ b) : False := by mip
-- 11. strict over ℤ, tightened
example (x : ℤ) (h1 : 0 < x) (h2 : x < 1) : False := by mip
-- 12. strict over ℚ, where the relaxation is enough
example (q : ℚ) (h1 : q < 0) (h2 : 1 < q) : False := by mip
-- 13. division by a literal over ℚ
example (q : ℚ) (h : 1 ≤ q / 2) (h2 : q ≤ 1) : False := by mip
-- 14. a negated comparison
example (x : ℤ) (h : ¬ (x ≤ 5)) (h2 : x ≤ 5) : False := by mip
-- 15. strictness matters: must fail, and say why
example (q : ℚ) (h1 : q < 1) (h2 : 1 ≤ q) : False := by
  fail_if_success mip
  linarith
-- 16. a false goal: must fail
example (x : ℤ) (h1 : 0 ≤ x) (h2 : x ≤ 3) : x ≤ 2 := by
  fail_if_success mip
  sorry

-- the axioms of a `mip` proof are the standard three
theorem pugh (x y : ℤ) (h1 : 27 ≤ 11*x + 13*y) (h2 : 11*x + 13*y ≤ 45)
    (h3 : -10 ≤ 7*x - 9*y) (h4 : 7*x - 9*y ≤ 4) : False := by mip
#print axioms pugh
