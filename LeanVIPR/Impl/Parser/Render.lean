module

public import LeanVIPR.Spec.Syntax.Ast
public import LeanVIPR.Spec.Syntax.Grammar

@[expose] public section

/-!
# Rendering a certificate back to text

The inverse direction of the reader: turn a `Vipr` back into a `.vipr` file.
`LeanVIPR.Thm.Parser.Render` proves the round trip, that reading what this writes gives
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

def renderNat (n : Nat) : String := String.ofList (natDigits n)

/-- A signed integer: `-` only for negatives, never a redundant `+`. -/
def renderInt (z : Int) : String :=
  if z < 0 then String.ofList ('-' :: natDigits z.natAbs) else renderNat z.natAbs

/-- An exact rational as `num/den`. Always a quotient, so every rational is expressible
and no finite-decimal assumption is needed. -/
def renderRat (q : ℚ) : String :=
  String.ofList ((renderInt q.num).toList ++ '/' :: (natDigits q.den))

/-! ## Rows and sections -/

def renderPair (p : Nat × ℚ) : Toks := [renderNat p.1, renderRat p.2]

def renderPairs : List (Nat × ℚ) → Toks
  | [] => []
  | p :: ps => renderPair p ++ renderPairs ps

def renderNats : List Nat → Toks
  | [] => []
  | n :: ns => [renderNat n] ++ renderNats ns

/-- A single-character token: a constraint sense, or a weak-bound kind. -/
def renderChar (c : Char) : String := String.ofList [c]

def renderBody (form : LinForm) (usesObj : Bool) : Toks :=
  if usesObj then ["OBJ"]
  else renderNat form.length :: renderPairs (form.map (fun t => (t.idx, t.coeff)))

def renderCon (c : ViprCon) : Toks :=
  c.name :: renderChar c.sense :: renderRat c.rhs :: renderBody c.form c.usesObj

def renderCons : List ViprCon → Toks
  | [] => []
  | c :: cs => renderCon c ++ renderCons cs

def renderSol (s : String × List (Nat × ℚ)) : Toks :=
  s.1 :: renderNat s.2.length :: renderPairs s.2

def renderSols : List (String × List (Nat × ℚ)) → Toks
  | [] => []
  | s :: ss => renderSol s ++ renderSols ss

def renderWeakBound (b : ViprWeakBound) : Toks :=
  [renderChar b.kind, renderNat b.varIdx, renderNat b.rowIdx, renderRat b.value]

def renderWeakBounds : List ViprWeakBound → Toks
  | [] => []
  | b :: bs => renderWeakBound b ++ renderWeakBounds bs

def renderWeakBlock : ViprWeakBounds → Toks
  | .global => "{" :: renderNat 0 :: ["}"]
  | .local bs => "{" :: renderNat bs.length :: (renderWeakBounds bs ++ ["}"])

def renderReason : ViprReason → Toks
  | .asm => ["{", "asm", "}"]
  | .sol => ["{", "sol", "}"]
  | .lin prs => "{" :: "lin" :: renderNat prs.length :: (renderPairs prs ++ ["}"])
  | .linWeak wb prs =>
      "{" :: "lin" :: "weak" ::
        (renderWeakBlock wb ++ renderNat prs.length :: (renderPairs prs ++ ["}"]))
  | .rnd prs => "{" :: "rnd" :: renderNat prs.length :: (renderPairs prs ++ ["}"])
  | .uns i1 l1 i2 l2 =>
      ["{", "uns", renderNat i1, renderNat l1, renderNat i2, renderNat l2, "}"]

def renderDerCore (d : ViprDer) : Toks :=
  d.name :: renderChar d.sense :: renderRat d.rhs ::
    (renderBody d.form d.usesObj ++ (renderReason d.reason ++ [renderInt d.idx]))

/-- A flagless row is written with an explicit `local`. The flag is matched greedily, so
omitting it would make the next row's name ambiguous when that name is `global` or
`local`. -/
def renderDers : List ViprDer → Toks
  | [] => []
  | d :: ds =>
      renderDerCore d ++ (if d.isGlobal then "global" else "local") :: renderDers ds

def renderBound (infinity : String) : Option ℚ → String
  | none => infinity
  | some q => renderRat q

def renderRtp : ViprRtp → Toks
  | .infeas => ["RTP", "infeas"]
  | .range lb ub => ["RTP", "range", renderBound "-inf" lb, renderBound "inf" ub]

/-- The tokens of a whole certificate, in the eight sections the format prescribes. -/
def renderVipr (v : Vipr) : Toks :=
  ["VER", v.version] ++
  (("VAR" :: renderNat v.varNames.toList.length :: v.varNames.toList) ++
  (("INT" :: renderNat v.intVars.length :: renderNats v.intVars) ++
  (("OBJ" :: v.objSense :: renderNat v.objTerms.length :: renderPairs v.objTerms) ++
  (("CON" :: renderNat v.numCon :: renderNat v.numBounds :: renderCons v.cons.toList) ++
  (renderRtp v.rtp ++
  (("SOL" :: renderNat v.numSol :: renderSols v.sols.toList) ++
  ("DER" :: renderNat v.ders.toList.length :: renderDers v.ders.toList)))))))

/-! ## Joining tokens -/

/-- Characters of a token list, separated by single spaces. -/
def unwordsChars : Toks → List Char
  | [] => []
  | [t] => t.toList
  | t :: ts => t.toList ++ ' ' :: unwordsChars ts

def unwords (ts : Toks) : String := String.ofList (unwordsChars ts)

/-- What a token list must satisfy to survive being joined and re-split: tokens are
nonempty, contain no whitespace, and do not begin with the comment marker. Each is
forced by the tokenization rules, and each holds of anything the renderer emits. -/
def RenderableTok (t : String) : Prop :=
  t.toList ≠ [] ∧ NoWhitespace t.toList ∧ t.toList.head? ≠ some '%'

instance (t : String) : Decidable (RenderableTok t) := by
  unfold RenderableTok; infer_instance

def Renderable (ts : Toks) : Prop := ∀ t ∈ ts, RenderableTok t

/-- The strings a certificate carries verbatim: everything the renderer copies rather
than generates. These have to be tokens already, which they are whenever the certificate
came from a parse. -/
def verbatimToks (v : Vipr) : Toks :=
  v.version :: v.objSense :: (v.varNames.toList ++ (v.cons.toList.map (·.name) ++
    (v.sols.toList.map (·.1) ++ v.ders.toList.map (·.name))))

/-- A whole certificate as `.vipr` text. -/
def render (v : Vipr) : String := unwords (renderVipr v)

end LeanVIPR.Impl
