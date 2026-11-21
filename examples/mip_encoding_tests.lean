import LeanVIPRTactic

/-!
# Encodings: indicators and products with a binary

Run as `examples/mip_tactic_tests.lean` is. An indicator `δ = 1 → a ≤ b` and a product
`δ * x` with `δ ∈ {0, 1}` are not linear; `mip` adds the linear facts they imply — big-M
and McCormick inequalities, with constants from the bounds in context — each proved by
splitting `δ = 0 ∨ δ = 1`, so nothing about an encoding is trusted. Cases 2 and 4 need the
integrality of `δ`: their LP relaxations are feasible, or bound the objective by 2.4.
-/

-- 1. an indicator, big-M with M from the bounds of x
example (z : ℤ) (x : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 5)
    (hind : z = 1 → x ≤ 1) (hz : z = 1) (hx : 2 ≤ x) : False := by mip
-- 2. two indicators: the LP relaxation (z = 1/2) is feasible, the integer problem is not
example (z : ℤ) (x : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 10)
    (h1 : z = 1 → x ≤ 2) (h2 : z = 0 → 8 ≤ x) (h3 : 3 ≤ x) (h4 : x ≤ 7) : False := by mip
-- 3. a product with a binary, McCormick: z·x ≤ x ≤ 2 < 3
example (z : ℤ) (x : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 4)
    (h : 3 ≤ (z : ℝ) * x) (h2 : x ≤ 2) : False := by mip
-- 4. maximizing a product with a binary: the LP bound is 2.4, the integer optimum 2
example (z : ℤ) (x : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 4)
    (h : x + 3 * (z : ℝ) ≤ 5) : (z : ℝ) * x ≤ 2 := by
  mip_maximize (z : ℝ) * x
  exact hbound
