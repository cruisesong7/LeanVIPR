module

public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# Reader utilities

Character-level helpers the reader is built from: splitting a list on a separator, and
the exact readers for naturals, signed integers, finite decimals and `p/q` rationals.
All total, all returning `Option`.

None of these is a library function in disguise. VIPR's numeric syntax differs from
Lean's at two points, in opposite directions — `String.toNat?` accepts `1_000` and VIPR
does not, `String.toInt?` rejects a leading `+` and VIPR allows it — and the library has
no reader for `ℚ` or for `p/q` at all. `String.splitOn` exists but carries no lemmas,
so `splitOnChar` is what makes `LeanVIPR.Thm.Parser.Number` provable.
-/

namespace LeanVIPR.Parser

/-- Split a character list on a separator, retaining empty segments. -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      let rest := splitOnChar sep cs
      if c == sep then
        [] :: rest
      else
        match rest with
        | [] => [[c]]
        | r :: rs => (c :: r) :: rs

/-- Parse a nonempty digit list into a natural number. An empty list is rejected so
that a lone sign, `.`, or `/` is never read as zero. -/
def natOfDigits? (l : List Char) : Option Nat :=
  if l.isEmpty then none else
  l.foldl (fun acc c =>
    match acc with
    | some n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none
    | none => none) (some 0)

/-- Parse a possibly empty digit list, reading the empty list as zero. Used only for
one side of a decimal point. -/
def natOfDigitsOrZero? (l : List Char) : Option Nat :=
  if l.isEmpty then some 0 else natOfDigits? l

/-- Parse an unsigned finite decimal: a run of digits, or `i.f` with at least one side
present, as the exact rational it denotes. -/
def parseUDec? (cs : List Char) : Option ℚ :=
  match splitOnChar '.' cs with
  | [i] =>
      match natOfDigits? i with
      | some n => some (n : ℚ)
      | none => none
  | [i, f] =>
      if i.isEmpty && f.isEmpty then none else
      match natOfDigitsOrZero? i, natOfDigitsOrZero? f with
      | some ni, some nf =>
          some ((ni : ℚ) + (nf : ℚ) / (10 : ℚ) ^ f.length)
      | _, _ => none
  | _ => none

/-- Split off at most one leading sign, reporting whether the token is negated. -/
def splitSign : List Char → Bool × List Char
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | cs => (false, cs)

/-- Parse a signed finite decimal as the exact rational it denotes. At most one leading
sign is accepted. -/
def parseRatChars? (cs0 : List Char) : Option ℚ :=
  let (neg, cs) := splitSign cs0
  match parseUDec? cs with
  | some q => some (if neg then -q else q)
  | none => none

def parseRat? (s : String) : Option ℚ := parseRatChars? s.toList

/-- Parse a signed integer literal. -/
def parseIntChars? (cs0 : List Char) : Option ℤ :=
  let (neg, cs) := splitSign cs0
  match natOfDigits? cs with
  | some n => some (if neg then -(n : ℤ) else (n : ℤ))
  | none => none

def parseInt? (s : String) : Option ℤ := parseIntChars? s.toList

/-- Parse an exact rational: a signed decimal, or `p/q` with a sign permitted on each
side, as GMP's reader accepts (a negative numerator over a negative denominator is
positive). The value is normalized exactly, so the written signs cannot change it. -/
def parseNumChars? (cs : List Char) : Option ℚ :=
  match splitOnChar '/' cs with
  | [_] => parseRatChars? cs
  | [num, den] =>
      match parseIntChars? num, parseIntChars? den with
      | some p, some q => if q == 0 then none else some ((p : ℚ) / (q : ℚ))
      | _, _ => none
  | _ => none

def parseNum? (s : String) : Option ℚ := parseNumChars? s.toList

end LeanVIPR.Parser
