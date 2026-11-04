module

public import LeanVIPR.Ast.Types
public import LeanVIPR.Thm.Number.Grammar

@[expose] public section

/-!
# The grammar of a VIPR certificate

**This file is the review surface for the certificate grammar.** It says which token
sequences are well formed and what they denote, and nothing else: no proofs, and no
reference to how the parser works. `LeanVIPR.Thm.Vipr` proves the parser agrees with
it in both directions, so a reader who accepts these definitions need not read the
parser.

Nothing here mentions a remainder, an `Except`, or a split. A terminal is a predicate
on one token; a non-terminal is a *concatenation equation* on token lists whose fields
are supplied existentially. The existential supplies the split, which is what a grammar
says; the parser's left-to-right discipline is its own business, discharged in
`LeanVIPR.Thm.Vipr.Lemmas`.

The format is count-prefixed throughout — `VAR n`, `CON m b`, `DER d`, and `p i a …`
inside a row — so every production is determined by its input and admits no ambiguity
to resolve.
-/

namespace LeanVIPR.Ast

/-! ## Terminals

Each is a predicate on a single token, built from the numeric grammar of
`LeanVIPR.Thm.Number.Grammar`. -/

/-- A natural number: a nonempty run of digits, denoting its base-ten value. -/
def IsNatTok (t : String) (n : Nat) : Prop :=
  IsDigits t.toList ∧ n = digitsValue t.toList

/-- A signed integer. -/
def IsIntTok (t : String) (z : ℤ) : Prop := IsIntValue t.toList z

/-- An exact rational. -/
def IsNumTok (t : String) (q : ℚ) : Prop := IsNumValue t.toList q

/-- A constraint sense: the single character `E`, `L`, or `G`. -/
def IsSenseTok (t : String) (c : Char) : Prop :=
  t.toList = [c] ∧ (c = 'E' ∨ c = 'L' ∨ c = 'G')

/-- An `RTP range` bound: the matching infinity spelling, or an exact rational. -/
def IsBoundTok (infinity t : String) (b : Option ℚ) : Prop :=
  (t = infinity ∧ b = none) ∨ (t ≠ infinity ∧ ∃ q, IsNumTok t q ∧ b = some q)

end LeanVIPR.Ast
