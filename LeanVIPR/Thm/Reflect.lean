module

public import LeanVIPR.Spec.Mip

@[expose] public section

/-!
# From an infeasible `Mip` to a `Prop` about integers

`Mip.Infeasible` says no *real* valuation with the declared variables integral is
feasible. A user asks something narrower-looking: that no tuple of integers satisfies
their constraints. This file is the bridge, and it is the whole mathematical content of a
`Prop`-level front end — everything else such a front end does is syntax matching, which
belongs in metacode and carries no proof obligation of its own.

The bridge is short because integrality comes for free. A valuation built by casting
integers satisfies `IsIntReal` at *every* index, not merely at the declared integer ones,
so the first component of `Mip.Feasible` is discharged without reference to `intVars`.
What remains for a caller to supply is exactly the interesting part: that the rows hold.

Nothing here mentions MPS or certificates. It is the `Prop`-facing end of `Spec/Mip.lean`,
usable the moment a pipeline theorem produces an `m.Infeasible`.
-/

namespace LeanVIPR.Mip

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Semantics.System

/-! ## Computing a witness valuation

Without these a reflected goal stalls on `valuationOfInts [x, y, z] 0` as an opaque term,
so they are what makes the row obligation mechanical rather than merely finite. -/

@[simp] theorem valuationOfInts_cons_zero (x : ℤ) (xs : List ℤ) :
    valuationOfInts (x :: xs) 0 = (x : ℝ) := rfl

@[simp] theorem valuationOfInts_cons_succ (x : ℤ) (xs : List ℤ) (j : Nat) :
    valuationOfInts (x :: xs) (j + 1) = valuationOfInts xs j := rfl

@[simp] theorem valuationOfInts_nil (j : Nat) : valuationOfInts [] j = 0 := by
  simp [valuationOfInts]

/-- A valuation built from integers is integral at every index. -/
theorem isIntReal_valuationOfInts (xs : List ℤ) (j : Nat) :
    IsIntReal (valuationOfInts xs j) :=
  ⟨xs.getD j 0, rfl⟩

/-- An integer tuple satisfying every row is a feasible point. The integrality half of
`Feasible` needs no hypothesis. -/
theorem feasible_valuationOfInts {m : Mip} {xs : List ℤ}
    (hrows : ∀ c ∈ m.conSLes, satReal c (valuationOfInts xs)) :
    m.Feasible (valuationOfInts xs) :=
  ⟨fun j _ => isIntReal_valuationOfInts xs j, hrows⟩

/-- **The front end's bridge.** An infeasible `Mip` rules out every integer tuple. A
tactic reflecting a goal `¬ ∃ x y z : ℤ, …` into `m` discharges it by this, leaving only
`hrows` — a finite, concrete list of real inequalities over integer casts — to close. -/
theorem absurd_of_infeasible {m : Mip} (h : m.Infeasible) (xs : List ℤ)
    (hrows : ∀ c ∈ m.conSLes, satReal c (valuationOfInts xs)) : False :=
  h _ (feasible_valuationOfInts hrows)

end LeanVIPR.Mip
