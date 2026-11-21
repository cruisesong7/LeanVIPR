import LeanVIPRTactic

/- A machine is on (z = 1) or off (z = 0). It makes x ∈ [0, 10] units, but none when
   off; running it uses 4 units of a 12-unit capacity. Profit is 3 per unit minus a
   fixed cost of 5 for switching it on. What is the most it can earn? -/
example (z : ℤ) (x : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)                 -- z is binary
    (hx0 : 0 ≤ x) (hx1 : x ≤ 10)
    (off : z = 0 → x ≤ 0)                       -- an indicator: no output when off
    (cap : x + 4 * (z : ℝ) ≤ 12) :              -- capacity
    3 * x - 5 * (z : ℝ) ≤ 19 := by
  mip_maximize 3 * x - 5 * (z : ℝ)
  exact hbound

/- The same bound, by plain `mip`: it must fail. Refuting `3x - 5z > 19` over the reals
   relaxes it to `≥ 19`, which the optimum (z = 1, x = 8) satisfies. -/
example (z : ℤ) (x : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 10)
    (off : z = 0 → x ≤ 0) (cap : x + 4 * (z : ℝ) ≤ 12) :
    3 * x - 5 * (z : ℝ) ≤ 19 := by
  fail_if_success mip
  mip_maximize 3 * x - 5 * (z : ℝ)
  exact hbound
