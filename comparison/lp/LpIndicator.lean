import LPTactic
import LPVerify
import LPBackendSoplexJSON
open LP

/-! # `leanprover/lp` on an indicator constraint

The production example of LeanVIPR's `docs/TACTIC.md`: a machine is on (`z = 1`) or off
(`z = 0`); it makes `x ∈ [0, 10]` units, none when off; running it uses 4 of 12 units of
capacity; profit is `3x - 5z`. The optimum is 19, at `z = 1`, `x = 8`, which
`mip_maximize` certifies. `lp` reads linear hypotheses only and certifies by a weighted sum
of them, so the best it can certify is the optimum of a relaxation.

`lake build` here; a green build means every assertion below held. Over `Rat`, since `lp`
has no `ℝ` without Mathlib.
-/

/-! The indicator `z = 0 → x ≤ 0` is not a linear hypothesis, so `lp` ignores it, and the
best it certifies is the optimum without it: 30, at `z = 0`, `x = 10`. -/

/-- error: lp: goal is not entailed; numerical residual is -11, not ≥ 0 -/
#guard_msgs in
example (z x : Rat) (_ : 0 ≤ z) (_ : z ≤ 1) (_ : 0 ≤ x) (_ : x ≤ 10)
    (_ : z = 0 → x ≤ 0) (_ : x + 4 * z ≤ 12) : 3 * x - 5 * z ≤ 19 := by lp

example (z x : Rat) (_ : 0 ≤ z) (_ : z ≤ 1) (_ : 0 ≤ x) (_ : x ≤ 10)
    (_ : z = 0 → x ≤ 0) (_ : x + 4 * z ≤ 12) : 3 * x - 5 * z ≤ 30 := by
  maximize h : 3 * x - 5 * z
  exact h

/-! Written by hand as its big-M row `x ≤ 10z`, the indicator is linear, and the bound
tightens to 150/7, at `z = 6/7`, `x = 60/7`: the LP relaxation, with `z` fractional. -/

example (z x : Rat) (_ : 0 ≤ z) (_ : z ≤ 1) (_ : 0 ≤ x) (_ : x ≤ 10)
    (_ : x ≤ 10 * z) (_ : x + 4 * z ≤ 12) : 3 * x - 5 * z ≤ 150 / 7 := by
  maximize h : 3 * x - 5 * z
  exact h

/-! Typing the variables as `Int` does not change that: a weighted sum of hypotheses
cannot use integrality, so 19 stays out of reach by `150/7 - 19 = 17/7`. -/

/-- error: lp: goal not entailed; residual -17/7 not ≥ 0 -/
#guard_msgs in
example (z x : Int) (_ : 0 ≤ z) (_ : z ≤ 1) (_ : 0 ≤ x) (_ : x ≤ 10)
    (_ : x ≤ 10 * z) (_ : x + 4 * z ≤ 12) : 3 * x - 5 * z ≤ 19 := by lp
