module

public import LeanVIPR.Parser.Number

@[expose] public section

/-!
# The grammar of a VIPR number token

**This file is the review surface for numeric parsing.** It gives the grammar of a
number token and the value each derivation denotes, and nothing else: no proofs, and
no reference to how the parser works. `LeanVIPR.Thm.Number` proves the reader agrees
with it in both directions, so a reader who accepts these definitions need not read
the parser.

Each production is a *concatenation equation* whose fields are supplied existentially
by `IsWfNum` / `IsNumValue`. The existential supplies the split, so no list surgery
(`splitOnChar`, `splitSign`) and no `Option` appears here: a token is well formed
exactly when it *can* be cut into fields satisfying the field predicates, which is what
a grammar says. Values are then pure functions of the fields.

A misread number is the one parser fault soundness cannot catch. A structurally damaged
certificate usually fails to replay, but a token read as the wrong value silently
substitutes a different mixed-integer problem, and `checkVipr_sound` would then
establish a true claim about the wrong problem. So the value of a digit run is given
positionally, each digit weighted by a power of ten, rather than as the left-to-right
fold the implementation uses.
-/

namespace LeanVIPR.Parser

/-! ## Fields -/

/-- Every character is an ASCII digit. -/
def AllDigits (l : List Char) : Prop := ∀ c ∈ l, c.isDigit

instance (l : List Char) : Decidable (AllDigits l) := by
  unfold AllDigits; infer_instance

/-- `Digits ::= Digit⁺`. -/
def IsDigits (l : List Char) : Prop := l ≠ [] ∧ AllDigits l

/-- `Sign ::= '-' | '+' | ε`. -/
def IsWfSign (s : List Char) : Prop := s = [] ∨ s = ['-'] ∨ s = ['+']

/-! ## Values -/

/-- The value of a digit list read most significant first, each digit weighted by its
positional power of ten. -/
def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - '0'.toNat) * 10 ^ cs.length + digitsValue cs

/-- The multiplier a sign field contributes. -/
def signOf (s : List Char) : ℚ := if s = ['-'] then -1 else 1

/-- `Sign Digits` denotes a signed base-ten integer. -/
def intValue (sign ds : List Char) : ℤ :=
  if sign = ['-'] then -(digitsValue ds : ℤ) else (digitsValue ds : ℤ)

/-- `Sign Digits* '.' Digits*` denotes `± (i + f / 10 ^ |f|)`. -/
def decValue (sign i f : List Char) : ℚ :=
  signOf sign * ((digitsValue i : ℚ) + (digitsValue f : ℚ) / (10 : ℚ) ^ f.length)

/-- A quotient of two signed integers. -/
def quotValue (sn nd sd dd : List Char) : ℚ := (intValue sn nd : ℚ) / (intValue sd dd : ℚ)

/-! ## Productions -/

/-- `Integer ::= Sign Digits`. -/
def IntProduction (cs sign ds : List Char) : Prop :=
  cs = sign ++ ds ∧ IsWfSign sign ∧ IsDigits ds

/-- `Decimal ::= Sign Digit* '.' Digit*`, with at least one digit present. -/
def DecProduction (cs sign i f : List Char) : Prop :=
  cs = sign ++ (i ++ '.' :: f) ∧ IsWfSign sign ∧ AllDigits i ∧ AllDigits f ∧
    (i ≠ [] ∨ f ≠ [])

/-- `Quotient ::= Integer '/' Integer`, with a nonzero denominator. -/
def QuotProduction (cs sn nd sd dd : List Char) : Prop :=
  cs = sn ++ (nd ++ '/' :: (sd ++ dd)) ∧
    IsWfSign sn ∧ IsDigits nd ∧ IsWfSign sd ∧ IsDigits dd ∧ digitsValue dd ≠ 0

/-! ## Well-formedness and denotation -/

/-- `IsWfInt cs`: `cs` is a well-formed integer token. -/
def IsWfInt (cs : List Char) : Prop := ∃ sign ds, IntProduction cs sign ds

/-- `IsIntValue cs z`: the integer token `cs` denotes exactly `z`. -/
def IsIntValue (cs : List Char) (z : ℤ) : Prop :=
  ∃ sign ds, IntProduction cs sign ds ∧ z = intValue sign ds

/-- `Number ::= Integer | Decimal | Quotient`. The three alternatives are disjoint:
a decimal contains `'.'` and a quotient contains `'/'`, neither of which a sign or a
digit run admits, so a token has at most one derivation. -/
def IsWfNum (cs : List Char) : Prop :=
  (∃ sign ds, IntProduction cs sign ds) ∨
  (∃ sign i f, DecProduction cs sign i f) ∨
  (∃ sn nd sd dd, QuotProduction cs sn nd sd dd)

/-- `IsNumValue cs q`: the number token `cs` denotes exactly the rational `q`. -/
def IsNumValue (cs : List Char) (q : ℚ) : Prop :=
  (∃ sign ds, IntProduction cs sign ds ∧ q = (intValue sign ds : ℚ)) ∨
  (∃ sign i f, DecProduction cs sign i f ∧ q = decValue sign i f) ∨
  (∃ sn nd sd dd, QuotProduction cs sn nd sd dd ∧ q = quotValue sn nd sd dd)

end LeanVIPR.Parser
