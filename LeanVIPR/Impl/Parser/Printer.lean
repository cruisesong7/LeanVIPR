module

public import LeanVIPR.Spec.Syntax.Ast
public import LeanVIPR.Spec.Syntax.Grammar

@[expose] public section

/-!
# Printing a certificate back to text

The inverse direction of the reader: turn a `Vipr` back into a `.vipr` file.
`LeanVIPR.Thm.Parser.Printer` proves the round trip, that reading what this writes gives
back what was written.

Nothing in the checker uses this. It exists to make the round trip statable, which is
what rules out a reader and a grammar that agree with each other only on the certificates
a solver happens to emit.

Two choices are forced by the grammar rather than by taste. Rationals are written as
`num/den` rather than as decimals, because every rational has such a form while only
some have a finite decimal one. And a derivation with no scope flag is written with an
explicit `local`, because the flag is matched greedily: emitting nothing would make the
next row's name ambiguous when that name happens to be `global` or `local`.
-/

namespace LeanVIPR.Impl

open LeanVIPR.Parser LeanVIPR.Semantics

/-! ## Numbers -/

/-- The character for a single decimal digit. Written as a lookup into a literal list so
that every fact about it is decidable. -/
def digitChar (r : Nat) : Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'].getD r '0'

/-- Decimal digits of a natural, most significant first, with an explicit `0`. -/
def natDigitsAux : Nat → List Char → List Char
  | 0, acc => acc
  | n + 1, acc => natDigitsAux ((n + 1) / 10) (digitChar ((n + 1) % 10) :: acc)
  decreasing_by omega

def natDigits (n : Nat) : List Char :=
  if n = 0 then ['0'] else natDigitsAux n []

def printNat (n : Nat) : String := String.ofList (natDigits n)

/-- A signed integer: `-` only for negatives, never a redundant `+`. -/
def printInt (z : Int) : String :=
  if z < 0 then String.ofList ('-' :: natDigits z.natAbs) else printNat z.natAbs

/-- An exact rational as `num/den`. Always a quotient, so every rational is expressible
and no finite-decimal assumption is needed. -/
def printRat (q : ℚ) : String :=
  String.ofList ((printInt q.num).toList ++ '/' :: (natDigits q.den))

/-! ## Rows and sections -/

def printPair (p : Nat × ℚ) : Toks := [printNat p.1, printRat p.2]

def printPairs : List (Nat × ℚ) → Toks
  | [] => []
  | p :: ps => printPair p ++ printPairs ps

def printNats : List Nat → Toks
  | [] => []
  | n :: ns => [printNat n] ++ printNats ns

/-- A single-character token: a constraint sense, or a weak-bound kind. -/
def printChar (c : Char) : String := String.ofList [c]

def printBody (form : LinForm) (usesObj : Bool) : Toks :=
  if usesObj then ["OBJ"]
  else printNat form.length :: printPairs (form.map (fun t => (t.idx, t.coeff)))

def printCon (c : ViprCon) : Toks :=
  c.name :: printChar c.sense :: printRat c.rhs :: printBody c.form c.usesObj

def printCons : List ViprCon → Toks
  | [] => []
  | c :: cs => printCon c ++ printCons cs

def printSol (s : String × List (Nat × ℚ)) : Toks :=
  s.1 :: printNat s.2.length :: printPairs s.2

def printSols : List (String × List (Nat × ℚ)) → Toks
  | [] => []
  | s :: ss => printSol s ++ printSols ss

def printWeakBound (b : ViprWeakBound) : Toks :=
  [printChar b.kind, printNat b.varIdx, printNat b.rowIdx, printRat b.value]

def printWeakBounds : List ViprWeakBound → Toks
  | [] => []
  | b :: bs => printWeakBound b ++ printWeakBounds bs

def printWeakBlock : ViprWeakBounds → Toks
  | .global => "{" :: printNat 0 :: ["}"]
  | .local bs => "{" :: printNat bs.length :: (printWeakBounds bs ++ ["}"])

def printReason : ViprReason → Toks
  | .asm => ["{", "asm", "}"]
  | .sol => ["{", "sol", "}"]
  | .lin prs => "{" :: "lin" :: printNat prs.length :: (printPairs prs ++ ["}"])
  | .linWeak wb prs =>
      "{" :: "lin" :: "weak" ::
        (printWeakBlock wb ++ printNat prs.length :: (printPairs prs ++ ["}"]))
  | .rnd prs => "{" :: "rnd" :: printNat prs.length :: (printPairs prs ++ ["}"])
  | .uns i1 l1 i2 l2 =>
      ["{", "uns", printNat i1, printNat l1, printNat i2, printNat l2, "}"]

def printDerCore (d : ViprDer) : Toks :=
  d.name :: printChar d.sense :: printRat d.rhs ::
    (printBody d.form d.usesObj ++ (printReason d.reason ++ [printInt d.idx]))

/-- A row's scope keyword is written back exactly as it was read, and a flagless row
emits nothing. That is safe because `IsDers.bare` excludes a flagless row followed by a
row *named* `global` or `local`, so the omitted keyword can never be mistaken for the
next row's name on the way back in. -/
def printDers : List ViprDer → Toks
  | [] => []
  | d :: ds =>
      printDerCore d ++ (match d.scope with
        | .absent => printDers ds
        | .global => "global" :: printDers ds
        | .local => "local" :: printDers ds)

def printBound (infinity : String) : Option ℚ → String
  | none => infinity
  | some q => printRat q

def printRtp : ViprRtp → Toks
  | .infeas => ["RTP", "infeas"]
  | .range lb ub => ["RTP", "range", printBound "-inf" lb, printBound "inf" ub]

/-- The tokens of a whole certificate, in the eight sections the format prescribes. -/
def printVipr (v : Vipr) : Toks :=
  ["VER", v.version] ++
  (("VAR" :: printNat v.varNames.toList.length :: v.varNames.toList) ++
  (("INT" :: printNat v.intVars.length :: printNats v.intVars) ++
  (("OBJ" :: v.objSense :: printNat v.objTerms.length :: printPairs v.objTerms) ++
  (("CON" :: printNat v.numCon :: printNat v.numBounds :: printCons v.cons.toList) ++
  (printRtp v.rtp ++
  (("SOL" :: printNat v.numSol :: printSols v.sols.toList) ++
  ("DER" :: printNat v.ders.toList.length :: printDers v.ders.toList)))))))

/-! ## Joining tokens -/

/-- Characters of a token list, separated by single spaces. -/
def unwordsChars : Toks → List Char
  | [] => []
  | [t] => t.toList
  | t :: ts => t.toList ++ ' ' :: unwordsChars ts

def unwords (ts : Toks) : String := String.ofList (unwordsChars ts)

/-- What a token list must satisfy to survive being joined and re-split: tokens are
nonempty, contain no whitespace, and do not begin with the comment marker. Each is
forced by the tokenization rules, and each holds of anything the printer emits. -/
def PrintableTok (t : String) : Prop :=
  t.toList ≠ [] ∧ NoWhitespace t.toList ∧ t.toList.head? ≠ some '%'

instance (t : String) : Decidable (PrintableTok t) := by
  unfold PrintableTok; infer_instance

def Printable (ts : Toks) : Prop := ∀ t ∈ ts, PrintableTok t

/-- The strings a certificate carries verbatim: everything the printer copies rather
than generates. These have to be tokens already, which they are whenever the certificate
came from a parse. -/
def verbatimToks (v : Vipr) : Toks :=
  v.version :: v.objSense :: (v.varNames.toList ++ (v.cons.toList.map (·.name) ++
    (v.sols.toList.map (·.1) ++ v.ders.toList.map (·.name))))

/-- A whole certificate as `.vipr` text. -/
def print (v : Vipr) : String := unwords (printVipr v)

/-- So the round trip can be stated as `parseVipr (toString v) = .ok v`. -/
instance : ToString Vipr := ⟨print⟩

end LeanVIPR.Impl
