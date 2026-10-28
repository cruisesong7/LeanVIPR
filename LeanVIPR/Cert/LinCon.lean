module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Sparse linear constraints over a valuation

VIPR certificates use sparse linear constraints over valuations `ℕ → ℚ`.
This module defines that representation.
-/

namespace LeanVIPR.Cert

/-- A variable valuation (variable id ↦ value). -/
abbrev Valuation := Nat → ℚ

/-- One `coeff · x[idx]` term of a linear form. -/
structure Term where
  idx : Nat
  coeff : ℚ
  deriving Repr, Inhabited, DecidableEq

/-- A sparse linear form `Σ coeff · x[idx]`. -/
abbrev LinForm := List Term

def LinForm.eval (f : LinForm) (a : Valuation) : ℚ :=
  (f.map (fun t => t.coeff * a t.idx)).sum

/-- A `≤` constraint `form ≤ rhs` (ge/eq rows are normalized to this upstream). -/
structure Le where
  form : LinForm
  rhs : ℚ
  deriving Repr, Inhabited, DecidableEq

def Le.sat (c : Le) (a : Valuation) : Prop := c.form.eval a ≤ c.rhs

end LeanVIPR.Cert
