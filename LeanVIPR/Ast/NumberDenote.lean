module

public import LeanVIPR.Ast.Number

@[expose] public section

/-!
# What a VIPR number token denotes

**This file is the review surface for numeric parsing.** It says which rational each
token denotes, and nothing else: no proofs, and no reference to how the parser works.
`LeanVIPR.Ast.NumberSound` proves the reader agrees with it in both directions, so a
reader who accepts these definitions need not read the parser.

A misread number is the one parser fault soundness cannot catch. A structurally damaged
certificate usually fails to replay, but a token read as the wrong value silently
substitutes a different mixed-integer problem, and `checkVipr_sound` would then
establish a true claim about the wrong problem. So the value of a digit run is given
positionally, each digit weighted by a power of ten, rather than as the left-to-right
fold the implementation uses.
-/

namespace LeanVIPR.Ast

/-- Every character is an ASCII digit. -/
def AllDigits (l : List Char) : Prop := ∀ c ∈ l, c.isDigit

instance (l : List Char) : Decidable (AllDigits l) := by
  unfold AllDigits; infer_instance

/-- The value of a digit list read most significant first, each digit weighted by its
positional power of ten. -/
def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - '0'.toNat) * 10 ^ cs.length + digitsValue cs

/-- `UDenotes cs q`: the unsigned token `cs` denotes exactly the rational `q`. -/
inductive UDenotes : List Char → ℚ → Prop
  /-- A nonempty run of digits denotes its base-ten value. -/
  | nat {ds : List Char} (hne : ds ≠ []) (hd : AllDigits ds) :
      UDenotes ds (digitsValue ds)
  /-- `i.f` denotes `i + f / 10 ^ |f|`; at least one side must be present. -/
  | dec {i f : List Char} (hne : i ≠ [] ∨ f ≠ []) (hi : AllDigits i) (hf : AllDigits f) :
      UDenotes (i ++ '.' :: f)
        ((digitsValue i : ℚ) + (digitsValue f : ℚ) / (10 : ℚ) ^ f.length)

/-- `Denotes cs q`: the token `cs`, with at most one leading sign, denotes `q`.

The sign convention is shared with the implementation via `splitSign`: that a token
carries at most one leading sign is part of the format, and `splitSign` is three
pattern-matching lines. Everything that computes a *value* — positional digit weights
and the fraction `f / 10 ^ |f|` — is stated independently above. -/
def Denotes (cs : List Char) (q : ℚ) : Prop :=
  ∃ u, UDenotes (splitSign cs).2 u ∧ q = (if (splitSign cs).1 then -u else u)

/-- `IntDenotes cs z`: the token `cs` denotes exactly the integer `z`. -/
def IntDenotes (cs : List Char) (z : ℤ) : Prop :=
  (splitSign cs).2 ≠ [] ∧ AllDigits (splitSign cs).2 ∧
    z = (if (splitSign cs).1 then -(digitsValue (splitSign cs).2 : ℤ)
         else (digitsValue (splitSign cs).2 : ℤ))

/-- `NumDenotes cs q`: the number token `cs` denotes exactly `q`: either a signed
decimal with no `/`, or a quotient of two signed integers with a nonzero denominator. -/
def NumDenotes (cs : List Char) (q : ℚ) : Prop :=
  ('/' ∉ cs ∧ Denotes cs q) ∨
  (∃ a b za zb, cs = a ++ '/' :: b ∧ '/' ∉ a ∧ '/' ∉ b ∧
    IntDenotes a za ∧ IntDenotes b zb ∧ zb ≠ 0 ∧ q = (za : ℚ) / (zb : ℚ))

end LeanVIPR.Ast
