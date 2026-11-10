module

public import LeanVIPR.Spec.Mip
public import LeanVIPR.Impl.Parser.Printer

@[expose] public section

/-!
# Emitting a `Mip` as a free-form MPS file

`encodeMps` is the half of the pipeline that poses the question: it turns the Lean `Mip`
into the file handed to exact SCIP. It is not soundness-critical — `agreesWith` is what
ties the returned certificate back to `m` — but it is what stops the pipeline failing
spuriously, and it is what makes the claim honest, since the file SCIP reads is then the
problem the theorem is about.

Rationals go out through `mpsRat` as exact `num/den`, because `docs/SCIP-SETUP.md`
establishes that the exact MPS reader parses coefficients through `RatSetString`, which
accepts exact fractions. No decimal is emitted anywhere, so nothing is rounded.

## Choices forced by MPS rather than by taste

* **One `column row coefficient` triple per line.** MPS permits two pairs per line and the
  hand-written `examples/uns_knapsack.mps` uses that form, but a uniform one-per-line
  emission is what makes `MpsDenotes` statable without a case split on parity.

* **Columns in `vars` index order, with `INTORG`/`INTEND` around maximal runs of integer
  variables.** Grouping all integer variables together would also be legal, but keeping
  index order means the file's column order is the `Mip`'s own order, so the only
  permutation left to recover in `agreesWith` is the one SCIP itself introduces.

* **`LO`/`UP` for every finite bound, never `LI`/`UI`.** Integrality is already carried by
  the `INTORG` markers, so the integer bound types would be redundant — and `LI` with a
  non-integral value has reader-dependent rounding behaviour, which would make the file
  mean something the `Mip` does not say. Avoiding those types avoids the question.

* **An explicit lower-bound line always comes first for each variable.** A bare negative
  `UP` on a variable whose lower bound is still the reader's default is the classic MPS
  trap: several readers silently take the lower bound to `-∞`. Emitting `LO` or `MI`
  first makes that unreachable.

* **`PL` for an integer variable with no upper bound.** `+∞` is the MPS default, so this
  line is redundant for a well-behaved reader — but the 0/1 default for marker-delimited
  integer columns is a real convention in the wild, and stating the bound costs one line.

* **Duplicate indices in a `LinForm` are summed.** `LinForm` is sparse and the spec does
  not forbid repeats, while a repeated `(column, row)` entry in MPS is read differently by
  different readers. `coeffOf` sums, so the emitted entry is unambiguous.

## Preconditions beyond `Mip.WellFormed`

`WellFormed` asks for declared indices and distinct names, which is not yet enough to
emit a file. The encoder additionally needs every variable and row name to be a single
MPS token — no whitespace, not `MARKER`, not one of the section keywords — and needs the
objective row name `obj` to be distinct from every `Row.name`. These belong in the
encoder's own precondition, and they now are: `LeanVIPR.Mps.EncodableNames`, stated
alongside the grammar in `Spec/Syntax/Mps.lean`. `encodeMps` does not check it, which is
harmless — a violation yields a file SCIP reads as a different problem, and `agreesWith`
rejects the certificate.
-/

namespace LeanVIPR.Impl.Encoder

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Parser LeanVIPR.Impl

/-! ## Pieces of a line -/

/-- The name of the free row carrying the objective. -/
def objRowName : String := "obj"

/-- An exact rational for MPS: `num/den`, but bare `num` when the denominator is one.

Distinct from `printRat`, which always writes the quotient because the VIPR grammar
requires it. Here the bare form is worth the case split: a reader that does not handle
fractions truncates at the `/` *silently* (see `docs/SCIP-SETUP.md`), so emitting `6`
rather than `6/1` means an all-integer problem is read correctly even by such a reader,
instead of being read correctly only by luck. -/
def mpsRat (q : ℚ) : String :=
  if q.den == 1 then printInt q.num else printRat q

/-- The coefficient on variable `j`, summing any repeated terms. -/
def coeffOf (f : LinForm) (j : Nat) : ℚ :=
  f.foldl (fun acc t => if t.idx == j then acc + t.coeff else acc) 0

/-- The nonzero `(row, coefficient)` entries of one column, objective row first. -/
def colEntries (m : Mip) (j : Nat) : List (String × ℚ) :=
  let objEntry : List (String × ℚ) :=
    let c := coeffOf m.obj j
    if c == 0 then [] else [(objRowName, c)]
  let rowEntries : List (String × ℚ) :=
    m.rows.toList.filterMap (fun r =>
      let c := coeffOf r.form j
      if c == 0 then none else some (r.name, c))
  objEntry ++ rowEntries

/-! ## Lines, as indentation plus tokens

Each emitted line is an indentation string followed by whitespace-separated tokens. Keeping
the two apart is what makes `LeanVIPR.Thm.Encoder.Emit` tractable: the indentation is
absorbed by `isTokenization_wsPrefix` and the tokens are exactly what the grammar reads, so
no reasoning about string concatenation is needed. The rendered text is unchanged — every
line below is `indent ++ unwords toks`, which is what the previous string-building
version produced character for character. -/

/-- The only indentations MPS lines use.

A three-valued type rather than a raw `String`, so "every indent is whitespace" holds *by
construction*: `LeanVIPR.Thm.Encoder.Emit.allWhitespace_indent` discharges it once by
cases, and no section of the emitter can introduce a non-whitespace indent for a later
proof to have to rule out. This is the one place Trestle's discipline — put the invariant
in the type instead of proving it afterwards — transfers cleanly to a file emitter. -/
inductive Indent where
  /-- Column one: a section keyword. -/
  | none
  /-- One space: a `ROWS` or `BOUNDS` entry. -/
  | one
  /-- Four spaces: a `COLUMNS` or `RHS` entry. -/
  | four
  deriving Repr, DecidableEq, Inhabited

def Indent.toString : Indent → String
  | .none => ""
  | .one => " "
  | .four => "    "

/-- One emitted line: its indentation, and its tokens. -/
abbrev Line := Indent × Toks

/-- An `INTORG` / `INTEND` marker line. -/
def markerLine (n : Nat) (tag : String) : Line :=
  (.four, ["M" ++ printNat n, "'MARKER'", "'" ++ tag ++ "'"])

/-- The `COLUMNS` lines for one column, one entry per line. -/
def colLines (name : String) (es : List (String × ℚ)) : List Line :=
  es.map (fun e => (.four, [name, e.1, mpsRat e.2]))

/-! ## Sections -/

/-- `OBJSENSE` is emitted only to override the MPS default of minimization. -/
def objSenseLines (m : Mip) : List Line :=
  match m.objSense with
  | .min => []
  | .max => [(.none, ["OBJSENSE"]), (.four, ["MAX"])]

/-- The free objective row, then one line per constraint row. -/
def rowsLines (m : Mip) : List Line :=
  (.one, ["N", objRowName]) ::
    m.rows.toList.map (fun r => (.one, [r.sense.toString, r.name]))

/-- `COLUMNS`, walking the variables in index order and toggling the integrality markers
around maximal runs of integer variables. `inInt` says whether a marker block is open and
`mk` is the next marker's number, so the recursion is structural on the variable list. A
column with no nonzero entry still needs to be declared, or the `BOUNDS` lines below would
refer to a column the reader has never seen; such a column is given an explicit zero
objective entry. -/
def columnsAux (m : Mip) : List (Nat × Mip.Var) → Bool → Nat → List Line
  | [], inInt, mk => if inInt then [markerLine mk "INTEND"] else []
  | (j, v) :: rest, inInt, mk =>
      let opening := v.isInt && !inInt
      let closing := !v.isInt && inInt
      let pre :=
        if opening then [markerLine mk "INTORG"]
        else if closing then [markerLine mk "INTEND"]
        else []
      let mk' := if opening || closing then mk + 1 else mk
      let es := colEntries m j
      let es := if es.isEmpty then [(objRowName, (0 : ℚ))] else es
      pre ++ colLines v.name es ++ columnsAux m rest v.isInt mk'

def columnsLines (m : Mip) : List Line :=
  columnsAux m (m.vars.toList.mapIdx (fun j v => (j, v))) false 1

/-- Every row's right-hand side, including the zeros. The MPS default is zero, so the
zero lines are redundant; emitting them keeps the section in bijection with `rows`. -/
def rhsLines (m : Mip) : List Line :=
  m.rows.toList.map (fun r => (.four, ["rhs", r.name, mpsRat r.rhs]))

/-- The bound lines for one variable: the lower bound first, then the upper. -/
def boundLines (v : Mip.Var) : List Line :=
  let lo :=
    match v.lo with
    | none => [(.one, ["MI", "BND", v.name])]
    | some l => [(.one, ["LO", "BND", v.name, mpsRat l])]
  let hi :=
    match v.hi with
    | none => if v.isInt then [(.one, ["PL", "BND", v.name])] else []
    | some u => [(.one, ["UP", "BND", v.name, mpsRat u])]
  lo ++ hi

/-! ## The file -/

def mpsLines (name : String) (m : Mip) : List Line :=
  (.none, ["NAME", name]) :: objSenseLines m
    ++ (.none, ["ROWS"]) :: rowsLines m
    ++ (.none, ["COLUMNS"]) :: columnsLines m
    ++ (.none, ["RHS"]) :: rhsLines m
    ++ (.none, ["BOUNDS"]) :: (m.vars.toList.map boundLines).flatten
    ++ [(.none, ["ENDATA"])]

/-- Every token the file carries, in order: what the grammar reads once the indentation
and line breaks are absorbed. -/
def mpsToks (name : String) (m : Mip) : Toks :=
  ((mpsLines name m).map Prod.snd).flatten

/-- One line's characters: its indentation, its tokens joined by single spaces, a newline.

Characters rather than a `String`, and `String.ofList` only at the very boundary below,
following `Impl.Parser.Printer`'s `unwords`. It keeps `LeanVIPR.Thm.Encoder.Emit` a list
induction instead of an argument about `String.join`. -/
def renderLineChars (l : Line) : List Char :=
  l.1.toString.toList ++ unwordsChars l.2 ++ ['\n']

/-- Every character of the file, in order. -/
def encodeMpsChars (name : String) (m : Mip) : List Char :=
  ((mpsLines name m).map renderLineChars).flatten

/-- The MPS text for a problem, under a given problem name. -/
def encodeMpsNamed (name : String) (m : Mip) : String :=
  String.ofList (encodeMpsChars name m)

/-- The MPS text for a problem. -/
def encodeMps (m : Mip) : String := encodeMpsNamed "leanvipr" m

end LeanVIPR.Impl.Encoder
