module

public import LeanVIPR.Spec.Syntax.Grammar
public import LeanVIPR.Spec.Mip

@[expose] public section

/-!
# What an MPS file says

The review surface for the *encoder*, as `Spec.Syntax.Grammar` is for the reader: which
character sequences are MPS files in the subset we emit, and which `Mip` each one denotes.
`LeanVIPR.Thm.Encoder.Emit` proves `encodeMps` lands in here, so accepting these
definitions makes reading the emitter unnecessary.

## This describes a subset, and says so

There is no single MPS specification to state a round trip against. The format is IBM's,
by convention rather than by document, and readers disagree about several of its sections
— the default upper bound on marker-delimited integer columns, a negative `UP` on a
variable whose lower bound is still the default, `RANGES` on an `E` row, the sign of an
objective constant. `docs/SCIP-ENCODER.md` records a measurement where two builds of
*the same* SCIP version read one file as two different problems.

So this file is **our formalization of the subset exact SCIP's reader accepts**, and the
round-trip theorem is relative to it. That is the same epistemic status
`Spec.Syntax.Grammar` has for `.vipr`, and it is the honest claim. Every ambiguity listed
above is avoided by construction here: there is no `RANGES` section, no objective
constant, no `LI`/`UI`, and bounds are always stated explicitly rather than defaulted.

## Why a token stream and not lines

Fixed-column MPS is not required — SCIP's reader is free-form — and in the subset we emit
every section is introduced by a keyword and every entry has a token count determined by
its own first or middle token. So line structure carries no information and the grammar is
stated over tokens, reusing `IsTokenization` wholesale. (That tokenizer also honours `%`
comments, which MPS does not use; it is strictly more permissive, which cannot make a
denotation wrong, and `encodeMps` never emits a `%`.)

The price is that names must not collide with the tokens read structurally, which is
`IsNameTok` below. That is the precondition `Impl/Encoder/Mps.lean` already flags as
needed beyond `Mip.WellFormed`, now made precise.

## Column-major in, row-major out

An MPS file lists coefficients by column while a `Mip` carries them inside its rows, so a
denotation has to transpose. `rowForm` does that, and the comparison to `m` is by
`FormEqReal` — equality as a linear function, not as a list — because the transpose
cannot recover a term order and should not have to.
-/

namespace LeanVIPR.Mps

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Semantics.System LeanVIPR.Parser

/-! ## Terminals -/

/-- The keywords this grammar reads as section introducers. -/
def sectionKeywords : List String :=
  ["NAME", "OBJSENSE", "ROWS", "COLUMNS", "RHS", "BOUNDS", "RANGES", "ENDATA"]

/-- The literal marking an integrality marker line. -/
def markerTok : String := "'MARKER'"

/-- A name a file may use for a column or a row: nonempty, whitespace-free, not beginning
with the comment marker, and distinct from every token the grammar reads structurally, so
that no boundary is ambiguous.

The `'%'` clause is not cosmetic. `IsTokenization` reads a `%` that begins a token as
commenting out the rest of its line, so a name starting with `%` could not survive being
written and read back at all — it is the same condition `PrintableTok` imposes, and
`LeanVIPR.Thm.Encoder.Emit.printableTok_of_isNameTok` is where the two meet. -/
def IsNameTok (t : String) : Prop :=
  t.toList ≠ [] ∧ NoWhitespace t.toList ∧ t.toList.head? ≠ some '%' ∧
    t ∉ sectionKeywords ∧ t ≠ markerTok

/-- The objective sense, as `OBJSENSE` spells it. Absent means minimize, which is the
MPS default. -/
def IsSenseWord (t : String) (s : Mip.ObjSense) : Prop :=
  (t = "MIN" ∧ s = .min) ∨ (t = "MAX" ∧ s = .max)

/-! ## `COLUMNS` entries

The one section with two kinds of entry. Both are three tokens; they are told apart by
the middle one, and `IsNameTok` forbids a row called `'MARKER'`, so the alternatives are
disjoint. -/

/-- One `COLUMNS` entry as the grammar reads it. -/
inductive ColEntry where
  /-- A marker line opening (`true`) or closing (`false`) an integer run. -/
  | marker (name : String) (opening : Bool)
  /-- A coefficient of `col` in `row`. -/
  | coeff (col row : String) (q : ℚ)
  deriving Repr, DecidableEq, Inhabited

def IsColEntry (ts : Toks) (e : ColEntry) : Prop :=
  (∃ n tag, ts = [n, markerTok, tag] ∧ IsNameTok n ∧
      ((tag = "'INTORG'" ∧ e = .marker n true) ∨
       (tag = "'INTEND'" ∧ e = .marker n false))) ∨
  (∃ c r t q, ts = [c, r, t] ∧ IsNameTok c ∧ IsNameTok r ∧ IsNumTok t q ∧
      e = .coeff c r q)

/-! ## What `COLUMNS` entries mean

Pure functions of the fields, in the manner of `digitsValue` and `intValue` in
`Spec.Syntax.Grammar`: they say what a derivation denotes, and mention no emitter. -/

/-- The columns appearing inside an open marker run, with repeats. `inInt` is the state
carried across entries, so the recursion is structural. -/
def intColumns : List ColEntry → Bool → List String
  | [], _ => []
  | .marker _ b :: rest, _ => intColumns rest b
  | .coeff c _ _ :: rest, inInt =>
      (if inInt then [c] else []) ++ intColumns rest inInt

/-- The file declares `col` integral: it has a coefficient inside a marker run. -/
def DeclaresInt (es : List ColEntry) (col : String) : Prop :=
  col ∈ intColumns es false

instance (es : List ColEntry) (col : String) : Decidable (DeclaresInt es col) := by
  unfold DeclaresInt; infer_instance

/-- The coefficient the file gives `col` in `row`, summing repeated entries — which is
what makes a repeated `(column, row)` pair unambiguous. -/
def colCoeff (es : List ColEntry) (col row : String) : ℚ :=
  (es.map (fun e =>
    match e with
    | .coeff c r q => if c = col ∧ r = row then q else 0
    | .marker _ _ => 0)).sum

/-- The linear form the file gives `row`, indexing variables by their position in
`names`. This is the transpose from column-major to row-major. -/
def rowForm (es : List ColEntry) (names : List String) (row : String) : LinForm :=
  (names.mapIdx (fun j n =>
    let q := colCoeff es n row
    if q = 0 then ([] : LinForm) else [(⟨j, q⟩ : Term)])).flatten

/-! ## `RHS` and `BOUNDS` entries -/

/-- One `RHS` entry: a vector name, a row name, a value. -/
def IsRhsEntry (ts : Toks) (p : String × ℚ) : Prop :=
  ∃ vec r t, ts = [vec, r, t] ∧ IsNameTok vec ∧ IsNameTok r ∧ IsNumTok t p.2 ∧ r = p.1

/-- The right-hand side the file gives `row`, summing repeats and defaulting to zero, as
MPS does for a row with no `RHS` entry. -/
def rhsOf (ps : List (String × ℚ)) (row : String) : ℚ :=
  (ps.map (fun p => if p.1 = row then p.2 else 0)).sum

/-- One side of one variable's bounds. -/
inductive BndEntry where
  /-- A finite lower (`isLower`) or upper bound. -/
  | fin (isLower : Bool) (var : String) (q : ℚ)
  /-- An infinite lower (`isLower`) or upper bound: `MI` or `PL`. -/
  | inf (isLower : Bool) (var : String)
  deriving Repr, DecidableEq, Inhabited

def IsBndEntry (ts : Toks) (e : BndEntry) : Prop :=
  (∃ ty vec x t q, ts = [ty, vec, x, t] ∧ IsNameTok vec ∧ IsNameTok x ∧
      IsNumTok t q ∧
      ((ty = "LO" ∧ e = .fin true x q) ∨ (ty = "UP" ∧ e = .fin false x q))) ∨
  (∃ ty vec x, ts = [ty, vec, x] ∧ IsNameTok vec ∧ IsNameTok x ∧
      ((ty = "MI" ∧ e = .inf true x) ∨ (ty = "PL" ∧ e = .inf false x)))

/-- The lower bound the file gives `x`: `none` when `MI` is stated. A variable with no
lower-bound entry has none stated, which this reads as `none` too — the emitter always
states one, so the round trip never relies on a default. -/
def loBound (es : List BndEntry) (x : String) : Option ℚ :=
  es.foldl (fun acc e =>
    match e with
    | .fin true y q => if y = x then some q else acc
    | .inf true y => if y = x then none else acc
    | _ => acc) none

/-- The upper bound the file gives `x`. `PL` and absence both read as `none`, since `+∞`
is the MPS default for an upper bound. -/
def hiBound (es : List BndEntry) (x : String) : Option ℚ :=
  es.foldl (fun acc e =>
    match e with
    | .fin false y q => if y = x then some q else acc
    | .inf false y => if y = x then none else acc
    | _ => acc) none

/-! ## Sections -/

def IsNameSection (ts : Toks) : Prop :=
  ∃ n, ts = ["NAME", n] ∧ IsNameTok n

/-- `OBJSENSE` is optional, and absent means minimize. -/
def IsObjSenseSection (ts : Toks) (s : Mip.ObjSense) : Prop :=
  (ts = [] ∧ s = .min) ∨ (∃ w, ts = ["OBJSENSE", w] ∧ IsSenseWord w s)

/-- One `ROWS` entry: a sense and a row name. -/
def IsRowEntry (ts : Toks) (p : Char × String) : Prop :=
  ∃ s n, ts = [s, n] ∧ IsSenseTok s p.1 ∧ IsNameTok n ∧ n = p.2

/-- `ROWS`: the free objective row first, then the constraint rows in order. -/
def IsRowsSection (ts : Toks) (objRow : String) (rows : List (Char × String)) : Prop :=
  ∃ body, ts = ["N", objRow] ++ body ∧ IsNameTok objRow ∧ IsSeq IsRowEntry body rows

def IsColumnsSection (ts : Toks) (es : List ColEntry) : Prop :=
  IsSeq IsColEntry ts es

def IsRhsSection (ts : Toks) (ps : List (String × ℚ)) : Prop :=
  IsSeq IsRhsEntry ts ps

def IsBoundsSection (ts : Toks) (es : List BndEntry) : Prop :=
  IsSeq IsBndEntry ts es

/-! ## The file

The sections are read independently and then required, all together, to describe `m`.
Stating the agreement as a conjunction of per-variable and per-row conditions — rather
than by assembling a `Mip` and comparing — is what keeps this a description of MPS
instead of an inverse of `encodeMps`. -/

/-- `ts` is the token stream of an MPS file denoting exactly `m`. -/
def IsMpsToks (ts : Toks) (m : Mip) : Prop :=
  ∃ (sName sObj sRows sCols sRhs sBnd : Toks) (objRow : String)
    (rows : List (Char × String)) (cols : List ColEntry)
    (rhs : List (String × ℚ)) (bnds : List BndEntry),
    -- the shape of the file
    ts = sName ++ sObj ++ ["ROWS"] ++ sRows ++ ["COLUMNS"] ++ sCols
          ++ ["RHS"] ++ sRhs ++ ["BOUNDS"] ++ sBnd ++ ["ENDATA"] ∧
    IsNameSection sName ∧
    IsObjSenseSection sObj m.objSense ∧
    IsRowsSection sRows objRow rows ∧
    IsColumnsSection sCols cols ∧
    IsRhsSection sRhs rhs ∧
    IsBoundsSection sBnd bnds ∧
    -- the rows the file declares are exactly `m`'s, with the same senses
    rows = m.rows.toList.map (fun r => (r.sense, r.name)) ∧
    -- every variable is declared, with its integrality and both its bounds
    (∀ v ∈ m.vars, (DeclaresInt cols v.name ↔ v.isInt = true) ∧
        loBound bnds v.name = v.lo ∧ hiBound bnds v.name = v.hi) ∧
    -- each constraint row's coefficients and right-hand side
    (∀ r ∈ m.rows,
        FormEqReal (rowForm cols (m.vars.toList.map Mip.Var.name) r.name) r.form ∧
        rhsOf rhs r.name = r.rhs) ∧
    -- and the objective, carried on the free row
    FormEqReal (rowForm cols (m.vars.toList.map Mip.Var.name) objRow) m.obj

/-- `cs` is the text of an MPS file denoting exactly `m`. Characters in, problem out, with
no reader function in between. -/
def IsMpsText (cs : List Char) (m : Mip) : Prop :=
  ∃ ts, IsTokenization cs ts ∧ IsMpsToks ts m

/-! ## The encoder's precondition

`Mip.WellFormed` asks for declared indices and distinct names, which is not enough to
write a file this grammar can read back: a row called `COLUMNS` would end a section, and a
column called `'MARKER'` would be read as a marker line. `Impl/Encoder/Mps.lean` records
this as prose; here it is a predicate, and it is what `mpsRoundTrip` will assume.

`encodeMps` does **not** check it. That is deliberate and harmless — a violation produces
a file SCIP reads as a different problem, and `agreesWith` then rejects the certificate.
As everywhere on this branch, an encoder fault costs completeness, never soundness. -/

/-- Every name the encoder writes is a token this grammar reads as a name, and the free
objective row's name is not also a constraint row's. -/
def EncodableNames (m : Mip) (objRow : String) : Prop :=
  IsNameTok objRow ∧
  (∀ v ∈ m.vars, IsNameTok v.name) ∧
  (∀ r ∈ m.rows, IsNameTok r.name ∧ r.name ≠ objRow)

end LeanVIPR.Mps
