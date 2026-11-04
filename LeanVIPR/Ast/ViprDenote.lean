module

public import LeanVIPR.Ast.Types
public import LeanVIPR.Ast.NumberDenote

@[expose] public section

/-!
# What a VIPR certificate's tokens denote

**This file is the review surface for the grammar.** Each relation `Reads… ts x ts'`
says that reading an `x` off the token list `ts` leaves `ts'`, phrased against the
numeric denotations of `LeanVIPR.Ast.NumberDenote` and never against a parser function.
`LeanVIPR.Ast.ViprSound` proves the reader agrees with each relation in both
directions, so accepting these definitions makes reading the parser unnecessary.

The format is count-prefixed throughout — `VAR n`, `CON m b`, `DER d`, and `p i a …`
inside a row — so each relation is deterministic in its remainder, and the grammar
admits no ambiguity to resolve.
-/

namespace LeanVIPR.Ast

open LeanVIPR.Cert

/-- Any one token. -/
def ReadsTok (ts : Toks) (t : String) (ts' : Toks) : Prop := ts = t :: ts'

/-- A required literal token. -/
def ReadsLit (s : String) (ts ts' : Toks) : Prop := ts = s :: ts'

/-- A natural number: a nonempty run of digits, denoting its base-ten value. -/
def ReadsNat (ts : Toks) (n : Nat) (ts' : Toks) : Prop :=
  ∃ t, ts = t :: ts' ∧ t.toList ≠ [] ∧ AllDigits t.toList ∧ n = digitsValue t.toList

/-- A signed integer. -/
def ReadsInt (ts : Toks) (z : ℤ) (ts' : Toks) : Prop :=
  ∃ t, ts = t :: ts' ∧ IntDenotes t.toList z

/-- An exact rational. -/
def ReadsNum (ts : Toks) (q : ℚ) (ts' : Toks) : Prop :=
  ∃ t, ts = t :: ts' ∧ NumDenotes t.toList q

/-- A constraint sense: the single character `E`, `L`, or `G`. -/
def ReadsSense (ts : Toks) (c : Char) (ts' : Toks) : Prop :=
  ∃ t, ts = t :: ts' ∧ t.toList = [c] ∧ (c = 'E' ∨ c = 'L' ∨ c = 'G')

/-- An `RTP range` bound: the matching infinity spelling, or an exact rational. -/
def ReadsBound (infinity : String) (t : String) (b : Option ℚ) : Prop :=
  (t = infinity ∧ b = none) ∨ (t ≠ infinity ∧ ∃ q, NumDenotes t.toList q ∧ b = some q)

end LeanVIPR.Ast
