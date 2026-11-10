module

public import LeanVIPR.Spec.Syntax.Ast

@[expose] public section

/-!
# What LeanVIPR accepts

**This is the review surface.** It is the whole specification of the format LeanVIPR
reads: which character sequences are certificates, which certificate each one denotes,
and which certificates describe a usable problem. Nothing here mentions a tokenizer, a
parser, or a validator — no splitting function, no `Option`, no `Except`, and no
remainder. A grammar says which renderings exist; the existential quantifiers supply the
split, and values are pure functions of the fields.

`LeanVIPR.Thm.Parser.Certificate` proves the reader agrees with all of this in both directions, so
accepting these definitions makes reading the reader unnecessary. The directions do
different jobs: soundness is what rules out reading a token as the wrong value, which
replay cannot catch, and completeness is what makes a rejection a statement about the
file rather than about the reader.

Four layers, in the order a file passes through them:

| | |
|---|---|
| `IsNumValue` | a numeric token denotes an exact rational |
| `IsTokenization` | characters become tokens |
| `IsVipr`, `IsViprText` | tokens become a certificate |
| `IsValid` | the certificate describes a usable problem |

A misread number is the one reader fault soundness cannot catch. A structurally damaged
certificate usually fails to replay, but a token read as the wrong value silently
substitutes a different mixed-integer problem, and `checkVipr_sound` would then
establish a true claim about the wrong problem. So digit runs are given positional
value here, each digit weighted by a power of ten, rather than as the left-to-right fold
the reader uses.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Semantics

/-! ## Numeric tokens

Which rational a numeric token denotes. It gives the grammar of a
number token and the value each derivation denotes, and nothing else: no proofs, and
no reference to how the parser works. `LeanVIPR.Thm.Parser.Number` proves the reader agrees
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
fold the implementation uses. -/

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

/-! ## Tokenization

Which token list a character list tokenizes to. It says which token lists a
character list may be read as, and nothing else: no proofs, and no reference to how the
tokenizer works. `LeanVIPR.Thm.Parser.Tokens` proves the tokenizer agrees with it in both
directions, so a reader who accepts this definition need not read the tokenizer.

Without this, the parser's correctness theorem would quantify over
`wsTokens content.toList` — an implementation function in its own specification — and
would say nothing about how characters become tokens. A tokenizer that silently dropped
or merged tokens would still satisfy it.

Three rules, in the order the first character decides between them: whitespace
separates, a `%` *beginning* a token runs a comment to the end of the line, and anything
else begins a token that extends to the next whitespace. A `%` inside a token is an
ordinary character, so `x%y` is one token. -/

/-- No character of a token is whitespace. -/
def NoWhitespace (t : List Char) : Prop := ∀ c ∈ t, ¬ c.isWhitespace

instance (t : List Char) : Decidable (NoWhitespace t) := by
  unfold NoWhitespace; infer_instance

/-- A token ending here cannot be extended: the input is exhausted, or what follows is
whitespace. This is what makes tokens maximal, and so the tokenization unique. -/
def AtTokenEnd (cs : List Char) : Prop := ∀ c ∈ cs.head?, c.isWhitespace

/-- `IsTokenization cs ts`: the characters `cs` tokenize to exactly `ts`. -/
inductive IsTokenization : List Char → Toks → Prop
  /-- The empty input has no tokens. -/
  | nil : IsTokenization [] []
  /-- Whitespace separates tokens and contributes none. -/
  | space {c : Char} {cs : List Char} {ts : Toks} (hw : c.isWhitespace)
      (h : IsTokenization cs ts) : IsTokenization (c :: cs) ts
  /-- A `%` beginning a token comments out the rest of its line. -/
  | commentLine {body rest : List Char} {ts : Toks} (hn : '\n' ∉ body)
      (h : IsTokenization rest ts) : IsTokenization ('%' :: (body ++ '\n' :: rest)) ts
  /-- A comment on the last line, with no terminating newline, ends the input. -/
  | commentEnd {body : List Char} (hn : '\n' ∉ body) : IsTokenization ('%' :: body) []
  /-- Any other maximal run of non-whitespace characters is one token. -/
  | token {t rest : List Char} {ts : Toks} (hne : t ≠ []) (hnw : NoWhitespace t)
      (hpct : t.head? ≠ some '%') (hend : AtTokenEnd rest)
      (h : IsTokenization rest ts) :
      IsTokenization (t ++ rest) (String.ofList t :: ts)

/-! ## Certificates

Which certificate a token list derives. It says which token
sequences are well formed and what they denote, and nothing else: no proofs, and no
reference to how the parser works. `LeanVIPR.Thm.Parser.Certificate` proves the parser agrees with
it in both directions, so a reader who accepts these definitions need not read the
parser.

Nothing here mentions a remainder, an `Except`, or a split. A terminal is a predicate
on one token; a non-terminal is a *concatenation equation* on token lists whose fields
are supplied existentially. The existential supplies the split, which is what a grammar
says; the parser's left-to-right discipline is its own business, discharged in
`LeanVIPR.Thm.Parser.CertificateLemmas`.

The format is count-prefixed throughout — `VAR n`, `CON m b`, `DER d`, and `p i a …`
inside a row — so every production is determined by its input and admits no ambiguity
to resolve. -/

/-! ## Terminals

Each is a predicate on a single token, built from the numeric grammar of
`LeanVIPR.Thm.Parser.Grammar`. -/

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

A `DER` row ends with a final-use index, optionally followed by the scope keyword
`global` or `local`, unbracketed. That form is not in the published grammar -- the
specification writes the scope only inside braces -- but exact SCIP emits it, in 17 of
the 26 certificates under `benchmarks/`, so a reader of real certificates has to accept
it.

Unbracketed and optional, it needs a lookahead: a flagless row followed by a row *named*
`global` or `local` would have that name read as its own flag. The `bare` case therefore
requires the next token to be neither keyword, and such a certificate is rejected rather
than misread.

The ambiguity is not in the format. `IsDerSection` fixes the row count, and only one
reading yields that many well-formed rows -- the greedy one leaves a row whose sense
would have to be `0`. A reader that consults the count resolves this without any
exclusion. This one cannot: it consumes a flat token stream, where the count is not
available at the point of lookahead. The exclusion is the price of that strategy, not a
property of VIPR.

It is kept deliberately rather than for want of an alternative. It is also what lets the
printer omit the keyword for `.absent` and still land back in this grammar, which is
what makes printed output reproduce its input -- see
`LeanVIPR.Thm.Parser.Printer.printDers_isDers`, whose `bare` case discharges its
obligation with exactly this hypothesis. Dropping the exclusion would align the accepted
language with a counted reader's at the cost of a printer that pads every flagless row.
The input it refuses needs a constraint named exactly `global` or `local`; no certificate
on hand has one. -/

/-- A `DER` row up to and including its final-use index, without the scope keyword. -/
def IsDerCore (ts : Toks) (d : ViprDer) : Prop :=
  ∃ st rt body rsn it, ts = d.name :: st :: rt :: (body ++ (rsn ++ [it])) ∧
    IsSenseTok st d.sense ∧ IsNumTok rt d.rhs ∧ IsBody body d.form d.usesObj ∧
    IsReason rsn d.reason ∧ IsIntTok it d.idx

/-- A list of `DER` rows, under the maximal-munch rule for the scope keyword. -/
inductive IsDers : Toks → List ViprDer → Prop
  | nil : IsDers [] []
  | globalFlag {core rest : Toks} {d : ViprDer} {ds : List ViprDer}
      (h : IsDerCore core d) (hg : d.scope = .global) (hs : IsDers rest ds) :
      IsDers (core ++ "global" :: rest) (d :: ds)
  | localFlag {core rest : Toks} {d : ViprDer} {ds : List ViprDer}
      (h : IsDerCore core d) (hg : d.scope = .local) (hs : IsDers rest ds) :
      IsDers (core ++ "local" :: rest) (d :: ds)
  | bare {core rest : Toks} {d : ViprDer} {ds : List ViprDer}
      (h : IsDerCore core d) (hg : d.scope = .absent)
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

/-- `cs` is the text of exactly the certificate `v`: it tokenizes to a token list that
derives `v`. Characters in, certificate out, with no parser function in between. -/
def IsViprText (cs : List Char) (v : Vipr) : Prop :=
  ∃ ts, IsTokenization cs ts ∧ IsVipr ts v

/-! ## Usable problems

Which certificates are usable beyond being well formed. It says which certificates are
well formed beyond their syntax, and nothing else: no proofs, and no reference to how
the checks are implemented. `LeanVIPR.Thm.Parser.Valid` proves `validateVipr` decides exactly
this, so a reader who accepts these definitions need not read the validator.

This is deliberately separate from the grammar. `LeanVIPR.Thm.Parser.Grammar` says what a
certificate *is*; these conditions say whether what it denotes is a problem the checker
can replay — every index names a declared variable, no sparse vector mentions a variable
twice, and no derivation uses a constraint the format already allowed a verifier to
discard. Nothing here is required for soundness; the first two keep the denotation
single-valued, and the last is conformance with the specification's `DER` rule.

`reasonRefs`, `reasonMultipliers`, `finalUseHint` and `usedAfterFinal` live in
`LeanVIPR.Parser.Types` because they state what the AST's index fields *mean* — which
constraints a reason cites, and what a `DER` row's trailing field declares. They are
part of the format, used by this specification and by the validator alike, in the same
way `digitsValue` is shared by the number grammar and the number reader. -/

/-- A sparse vector's indices name declared variables, and none is repeated.

Duplicates are rejected rather than resolved: they have no agreed meaning, since the
reference checker keeps the last value while summing them is equally natural. -/
def IndicesOk (nvar : Nat) (idxs : List Nat) : Prop :=
  (∀ i ∈ idxs, i < nvar) ∧ idxs.Nodup

/-- A solution vector names declared variables and assigns each at most one value. A
repeated index is allowed when the values agree, since then the vector still denotes
one point. -/
def SolutionOk (nvar : Nat) (vals : List (Nat × ℚ)) : Prop :=
  (∀ p ∈ vals, p.1 < nvar) ∧ ∀ p ∈ vals, ∀ q ∈ vals, p.1 = q.1 → p.2 = q.2

/-- The `CON` header's second field counts a subset of the first: `b` is "the total
number of bound constraints" and `m` is "the total number of constraints (including
bound constraints)", so `b ≤ m`.

This is all of the specification's bound-constraint rules that can be stated here. The
others -- that bound constraints appear before the nonbound ones -- quantify over a class
the format never defines: the specification says bound constraints "are not treated
specially" and that a generator "is free to choose arbitrary names" for them, so nothing
in `ViprCon` distinguishes one. A placement rule over an undefined class is not
checkable, and guessing a definition would reject valid certificates. -/
def BoundCountOk (v : Vipr) : Prop := v.numBounds ≤ v.numCon

/-- Every constraint a reason cites already exists where it is cited: a base constraint,
or a derivation earlier in the `DER` list. The position of a derivation in that list is
its constraint index, offset by the number of `CON` rows, which is why this is stated
over a split of the list in the same way as `FinalUseOk`.

This is here for the same reason as `IndicesOk`: without it a reason may name a row that
does not exist, and `finalUseHint` resolves such a reference to `default`, so the AST
would denote something the format does not. The checker separately refuses to replay an
out-of-range reference, so soundness does not rest on this condition -- what rests on it
is that an accepted certificate denotes one problem. -/
def ReasonRefsOk (v : Vipr) : Prop :=
  ∀ before d after, v.ders.toList = before ++ d :: after →
    ∀ k ∈ reasonRefs d.reason, k < v.cons.size + before.length

/-- No derivation cites a constraint past that constraint's declared final use. The
position of a derivation in the `DER` list is its constraint index, offset by the number
of `CON` rows, which is why the rule is stated over a split of the list. -/
def FinalUseOk (v : Vipr) : Prop :=
  ∀ before d after, v.ders.toList = before ++ d :: after →
    ∀ k ∈ reasonRefs d.reason, ¬ usedAfterFinal v (v.cons.size + before.length) k

/-! ### Conditions the specification states and this does not

Three are absent deliberately, and the absences are decisions rather than oversights.

*Unique constraint names.* `cert_spec_v1_0.md` says "Constraints have unique constraint
names and are assigned indices starting from 0 according to the order in which they
appear in the certificate file." Exact SCIP does not honour it: of 38 certificates
measured, six violate it, `neos897005` with 17558 duplicate names and `khb05250` with
1804, where `CON` name `1146` appears four times and `DER` name `110` seventeen times.
Enforcing the sentence would reject real solver output, and references are positional
anyway, so a duplicate name makes nothing ambiguous.

*Bound constraints before the nonbound ones.* Normative -- the specification says they
"must appear at the beginning of the section" -- but it quantifies over a class the
format never defines. See `BoundCountOk` for the part that is statable.

*Reasons new in v1.1 under `VER 1.0`.* "New in version 1.1" is a heading, not a
prohibition, and `benchmarks/infeas/alu4_1.vipr` declares `VER 1.0` while using
`lin weak { 0 }`.

The rule behind all three: a conformance condition is safe to enforce only if real
solver output satisfies it. Specification text is necessary but not sufficient, because
the document and its reference implementation disagree, and it is the implementation that
writes the files a checker has to read.

### Which layer refuses an unsupported certificate

`lin incomplete` is refused by the reader, while an unknown `OBJ` sense or `VER` string
is read and refused by the checker. That is not inconsistency: it follows from what the
AST can hold. There is no `ViprReason` constructor for `lin incomplete`, so a reader
cannot carry one even if it wanted to; `objSense` and `version` are plain `String`
fields, so those certificates are representable and `Vipr.ClaimValid` is simply false of
them. The layer is wherever the certificate stops being expressible. -/

/-- `IsValid v`: every sparse vector that contributes to the claimed problem or to a
stated derived row is well formed, and the final-use rule holds. -/
def IsValid (v : Vipr) : Prop :=
  (∀ i ∈ v.intVars, i < v.varNames.size) ∧
  IndicesOk v.varNames.size (v.objTerms.map Prod.fst) ∧
  (∀ c ∈ v.cons.toList, IndicesOk v.varNames.size (c.form.map (·.idx))) ∧
  (∀ s ∈ v.sols.toList, SolutionOk v.varNames.size s.2) ∧
  (∀ d ∈ v.ders.toList,
    IndicesOk v.varNames.size (d.form.map (·.idx)) ∧
      (reasonMultipliers d.reason).Nodup) ∧
  BoundCountOk v ∧
  ReasonRefsOk v ∧
  FinalUseOk v

end LeanVIPR.Parser
