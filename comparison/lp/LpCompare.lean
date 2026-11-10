import LPTactic
import LPVerify
import LPBackendSoplexJSON
open LP

/-! # What `leanprover/lp` can and cannot prove

`lake build` here; a green build means every assertion below held.

Constraints go in as *hypotheses* with goal `False`, which is `lp`'s own idiom for
infeasibility — "when SoPlex returns infeasible, `lp` derives `False` from the dual".
Stating them as `¬ ∃ …` instead gets `lp: goal False is not an atomic comparison or ∃`,
which is a goal-shape complaint rather than a real answer, so the comparison has to use
this form to be fair.

Every `lp` carrier — `Rat`, `Int`, `Nat`, `Dyadic`, field — proves goals through the
shared ordered-ring assembly in `LPTactic/LP/RingCertificate.lean`: a weighted sum of
hypotheses, i.e. a Farkas argument. A Farkas refutation exists exactly when the *linear*
relaxation is infeasible. So `lp` decides LP infeasibility and nothing beyond it, which is
what the two sections below demonstrate.
-/

/-! ## Controls — goals duality can reach, so these must close -/

/-- Their own README example; if this fails, the harness is misconfigured, not `lp`. -/
example (x₀ x₁ : Rat) (_ : x₀ ≤ 4) (_ : 2 * x₁ ≤ 12) (_ : 3 * x₀ + 2 * x₁ ≤ 18)
    (_ : 0 ≤ x₀) (_ : 0 ≤ x₁) : 3 * x₀ + 5 * x₁ ≤ 36 := by lp

/-- LP-infeasible over `Rat`: a Farkas combination exists. -/
example (x : Rat) (_ : 2 * x ≤ 1) (_ : 2 * x ≥ 3) : False := by lp

/-- The same system with `Int`-typed variables. This is the important control: it shows
the `Int` carrier is live and working, so the failures below are about integrality rather
than about an unused code path. -/
example (x : Int) (_ : 2 * x ≤ 1) (_ : 2 * x ≥ 3) : False := by lp

/-! ## Integer goals — true, but not reachable by any weighted sum

Both are asserted *failures*: `#guard_msgs` pins the exact diagnostic, so this file stays
honest if a future `lp` ever closes them. -/

/-! The knapsack LeanVIPR certifies. Its LP relaxation is feasible — exact SCIP reports
optimal at `y = 4/5`, `z = 1`, and `10·(4/5) + 15·1 = 23` — so no Farkas combination
refutes it, and only integrality does. -/

/--
error: lp: goal
  False
is not an atomic comparison, and the hypotheses over [Int] are not inconsistent
-/
#guard_msgs in
example (x y z : Int) (_ : 0 ≤ x) (_ : x ≤ 3) (_ : 0 ≤ y) (_ : y ≤ 2)
    (_ : 0 ≤ z) (_ : z ≤ 1) (_ : 6*x + 10*y + 15*z = 23) (_ : x + y + z ≥ 1) :
    False := by lp

/-! Parity, the smallest witness of the same gap: `omega` closes this instantly, but
`x = 1/2` satisfies the relaxation, so there is no Farkas certificate to find. -/

/--
error: lp: goal
  False
is not an atomic comparison, and the hypotheses over [Int] are not inconsistent
-/
#guard_msgs in
example (x : Int) (_ : 2 * x = 1) : False := by lp
