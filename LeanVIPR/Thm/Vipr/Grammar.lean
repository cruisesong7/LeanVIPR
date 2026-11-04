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

open LeanVIPR.Cert

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

/-! ## Repetition

`IsSeq R` renders a list as the concatenation of the renderings of its elements. The
element count is never part of a repetition: where the format writes a count token, the
production that uses it states that the token denotes the list's length, so a count
that disagrees with the body is simply not derivable. -/

/-- `ts` is the concatenation of renderings of `xs`, in order. -/
inductive IsSeq {α : Type} (R : Toks → α → Prop) : Toks → List α → Prop
  | nil : IsSeq R [] []
  | cons {seg rest : Toks} {x : α} {xs : List α}
      (h : R seg x) (hs : IsSeq R rest xs) : IsSeq R (seg ++ rest) (x :: xs)

/-- One `index value` pair. -/
def IsPair (ts : Toks) (p : Nat × ℚ) : Prop :=
  ∃ it vt, ts = [it, vt] ∧ IsNatTok it p.1 ∧ IsNumTok vt p.2

/-- One natural-number item. -/
def IsNatItem (ts : Toks) (n : Nat) : Prop := ∃ t, ts = [t] ∧ IsNatTok t n

/-! ## Rows -/

/-- `Body ::= "OBJ" | p i₁ a₁ … iₚ aₚ`: an explicit sparse form, or the objective row
by reference. -/
def IsBody (ts : Toks) (form : LinForm) (usesObj : Bool) : Prop :=
  (ts = ["OBJ"] ∧ form = [] ∧ usesObj = true) ∨
  (∃ cnt body prs, ts = cnt :: body ∧ IsNatTok cnt prs.length ∧
    IsSeq IsPair body prs ∧ form = prs.map (fun q => (⟨q.1, q.2⟩ : Term)) ∧
    usesObj = false)

/-- A `CON` row: `name sense rhs Body`. -/
def IsCon (ts : Toks) (c : ViprCon) : Prop :=
  ∃ st rt body, ts = c.name :: st :: rt :: body ∧
    IsSenseTok st c.sense ∧ IsNumTok rt c.rhs ∧ IsBody body c.form c.usesObj

/-- One solution: `name p i₁ v₁ … iₚ vₚ`. -/
def IsSol (ts : Toks) (s : String × List (Nat × ℚ)) : Prop :=
  ∃ cnt body, ts = s.1 :: cnt :: body ∧ IsNatTok cnt s.2.length ∧ IsSeq IsPair body s.2

/-! ## Reasons -/

/-- One v1.1 `lin weak` completion bound: `L|U varIdx rowIdx value`. -/
def IsWeakBound (ts : Toks) (b : ViprWeakBound) : Prop :=
  ∃ kt vt rt nt, ts = [kt, vt, rt, nt] ∧ kt.toList = [b.kind] ∧
    (b.kind = 'L' ∨ b.kind = 'U') ∧
    IsNatTok vt b.varIdx ∧ IsNatTok rt b.rowIdx ∧ IsNumTok nt b.value

/-- The inner block of a `lin weak` reason: `{ 0 }` offers the global variable bounds,
`{ n b₁ … bₙ }` lists local ones. -/
def IsWeakBoundsBlock (ts : Toks) (wb : ViprWeakBounds) : Prop :=
  ∃ cnt body bs, ts = "{" :: cnt :: (body ++ ["}"]) ∧ IsNatTok cnt bs.length ∧
    IsSeq IsWeakBound body bs ∧
    ((bs = [] ∧ wb = .global) ∨ (bs ≠ [] ∧ wb = .local bs))

/-- A `{ reason }` block.

`lin incomplete` is absent by design: it supplies no multipliers, and recovering them
needs an exact LP solve, which is a completer's job. It is therefore reported as
unsupported rather than derived, so a `lin incomplete` certificate is outside this
grammar — a stated limit of coverage, not a claim that the file is malformed. -/
def IsReason (ts : Toks) (r : ViprReason) : Prop :=
  (ts = ["{", "asm", "}"] ∧ r = .asm) ∨
  (ts = ["{", "sol", "}"] ∧ r = .sol) ∨
  (∃ cnt body prs, ts = "{" :: "lin" :: cnt :: (body ++ ["}"]) ∧
    IsNatTok cnt prs.length ∧ IsSeq IsPair body prs ∧ r = .lin prs) ∨
  (∃ blk wb cnt body prs, ts = "{" :: "lin" :: "weak" :: (blk ++ cnt :: (body ++ ["}"])) ∧
    IsWeakBoundsBlock blk wb ∧ IsNatTok cnt prs.length ∧ IsSeq IsPair body prs ∧
    r = .linWeak wb prs) ∨
  (∃ cnt body prs, ts = "{" :: "rnd" :: cnt :: (body ++ ["}"]) ∧
    IsNatTok cnt prs.length ∧ IsSeq IsPair body prs ∧ r = .rnd prs) ∨
  (∃ t1 t2 t3 t4 i1 l1 i2 l2, ts = ["{", "uns", t1, t2, t3, t4, "}"] ∧
    IsNatTok t1 i1 ∧ IsNatTok t2 l1 ∧ IsNatTok t3 i2 ∧ IsNatTok t4 l2 ∧
    r = .uns i1 l1 i2 l2)

/-! ## Derivations

A `DER` row ends with a final-use index, optionally followed by the v1.1 scope keyword
`global` or `local`. That keyword is optional *and* unbracketed, so the format is only
unambiguous under maximal munch: a flagless row followed by a row *named* `global` or
`local` would have that name read as its own flag. `IsDers` states the rule the parser
follows — the `bare` case requires that the next token is neither keyword — which makes
the derivation list unambiguous and makes the exclusion visible rather than implicit.
Such a certificate is rejected, not misread: the absorbed name leaves the next row
starting at its sense token. -/

/-- A `DER` row up to and including its final-use index, without the scope keyword. -/
def IsDerCore (ts : Toks) (d : ViprDer) : Prop :=
  ∃ st rt body rsn it, ts = d.name :: st :: rt :: (body ++ (rsn ++ [it])) ∧
    IsSenseTok st d.sense ∧ IsNumTok rt d.rhs ∧ IsBody body d.form d.usesObj ∧
    IsReason rsn d.reason ∧ IsIntTok it d.idx

/-- A list of `DER` rows, under the maximal-munch rule for the scope keyword. -/
inductive IsDers : Toks → List ViprDer → Prop
  | nil : IsDers [] []
  | globalFlag {core rest : Toks} {d : ViprDer} {ds : List ViprDer}
      (h : IsDerCore core d) (hg : d.isGlobal = true) (hs : IsDers rest ds) :
      IsDers (core ++ "global" :: rest) (d :: ds)
  | localFlag {core rest : Toks} {d : ViprDer} {ds : List ViprDer}
      (h : IsDerCore core d) (hg : d.isGlobal = false) (hs : IsDers rest ds) :
      IsDers (core ++ "local" :: rest) (d :: ds)
  | bare {core rest : Toks} {d : ViprDer} {ds : List ViprDer}
      (h : IsDerCore core d) (hg : d.isGlobal = false)
      (hne : rest.head? ≠ some "global" ∧ rest.head? ≠ some "local")
      (hs : IsDers rest ds) : IsDers (core ++ rest) (d :: ds)

/-! ## Sections

Each section names itself, states its own length, and then contains exactly that many
items. The count tokens are the only place where a section's shape depends on a value,
which is why every count is tied to a `List.length` here. -/

/-- `VER version`. -/
def IsVerSection (ts : Toks) (ver : String) : Prop := ts = ["VER", ver]

/-- `VAR n name₁ … nameₙ`. Names are arbitrary tokens, so they are their own rendering. -/
def IsVarSection (ts : Toks) (names : List String) : Prop :=
  ∃ cnt, ts = "VAR" :: cnt :: names ∧ IsNatTok cnt names.length

/-- `INT n i₁ … iₙ`: the indices of the integer-constrained variables. -/
def IsIntSection (ts : Toks) (ints : List Nat) : Prop :=
  ∃ cnt body, ts = "INT" :: cnt :: body ∧ IsNatTok cnt ints.length ∧
    IsSeq IsNatItem body ints

/-- `OBJ (min|max) n i₁ a₁ … iₙ aₙ`. The direction token is kept verbatim. -/
def IsObjSection (ts : Toks) (sense : String) (terms : List (Nat × ℚ)) : Prop :=
  ∃ cnt body, ts = "OBJ" :: sense :: cnt :: body ∧ IsNatTok cnt terms.length ∧
    IsSeq IsPair body terms

/-- `CON m b con₁ … conₘ`. `b` counts the rows that are variable bounds; it is recorded
for the `lin weak` completer and constrains nothing here. -/
def IsConSection (ts : Toks) (ncon nbound : Nat) (cons : List ViprCon) : Prop :=
  ∃ cnt bnd body, ts = "CON" :: cnt :: bnd :: body ∧ IsNatTok cnt ncon ∧
    IsNatTok bnd nbound ∧ ncon = cons.length ∧ IsSeq IsCon body cons

/-- `RTP infeas`, or `RTP range lb ub`. -/
def IsRtpSection (ts : Toks) (rtp : ViprRtp) : Prop :=
  (ts = ["RTP", "infeas"] ∧ rtp = .infeas) ∨
  (∃ lt ut lb ub, ts = ["RTP", "range", lt, ut] ∧
    IsBoundTok "-inf" lt lb ∧ IsBoundTok "inf" ut ub ∧ rtp = .range lb ub)

/-- `SOL n sol₁ … solₙ`. -/
def IsSolSection (ts : Toks) (nsol : Nat)
    (sols : List (String × List (Nat × ℚ))) : Prop :=
  ∃ cnt body, ts = "SOL" :: cnt :: body ∧ IsNatTok cnt nsol ∧ nsol = sols.length ∧
    IsSeq IsSol body sols

/-- `DER n der₁ … derₙ`. -/
def IsDerSection (ts : Toks) (ders : List ViprDer) : Prop :=
  ∃ cnt body, ts = "DER" :: cnt :: body ∧ IsNatTok cnt ders.length ∧ IsDers body ders

/-! ## A whole certificate -/

/-- `ts` renders exactly the certificate `v`: the eight sections in order, and nothing
else. This is the complete syntactic specification of the format LeanVIPR reads. -/
def IsVipr (ts : Toks) (v : Vipr) : Prop :=
  ∃ sVer sVar sInt sObj sCon sRtp sSol sDer,
    ts = sVer ++ sVar ++ sInt ++ sObj ++ sCon ++ sRtp ++ sSol ++ sDer ∧
    IsVerSection sVer v.version ∧
    IsVarSection sVar v.varNames.toList ∧
    IsIntSection sInt v.intVars ∧
    IsObjSection sObj v.objSense v.objTerms ∧
    IsConSection sCon v.numCon v.numBounds v.cons.toList ∧
    IsRtpSection sRtp v.rtp ∧
    IsSolSection sSol v.numSol v.sols.toList ∧
    IsDerSection sDer v.ders.toList

end LeanVIPR.Ast
