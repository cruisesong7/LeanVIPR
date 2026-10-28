module

public import LeanVIPR.Ast.Number
public import LeanVIPR.Cert.LinCon

@[expose] public section

/-!
# VIPR v1.0 certificate parser

Reads a `.vipr` certificate (ASCII, token-oriented) into a structured
`Vipr` value.  Sections in order: `VER / VAR / INT / OBJ / CON / RTP / SOL / DER`.
Numbers are exact rationals — decimal (`-2.5`, `.5`, using `Ast.parseRat?`) or
`p/q` (handled here by `parseNum?`).

The heart is the `DER` list of derived constraints, each with a *reason*
(`asm`, `lin`, `rnd`, `uns`, `sol`).  The constraint/derived-constraint body is the
same in both `CON` and `DER`: either an explicit sparse form `p i₁ a₁ … iₚ aₚ` or
the keyword `OBJ`.

`LeanVIPR.Pipeline` maps the parsed rows and derivations to the sensed rows (`SLe`)
replayed by the checker.

The `SOL` section is parsed as exact sparse vectors and is checked for `RTP range`.
-/

namespace LeanVIPR.Ast

open LeanVIPR.Cert

/-! ## Number parsing (integers and `p/q` rationals) -/

/-- Parse a signed integer literal. -/
def parseInt? (s : String) : Option ℤ :=
  match s.toList with
  | '-' :: rest => (natOfDigits? rest).map (fun n => -(n : ℤ))
  | '+' :: rest => (natOfDigits? rest).map (fun n => (n : ℤ))
  | cs          => (natOfDigits? cs).map (fun n => (n : ℤ))

/-- Parse an exact rational: either a decimal literal (`Ast.parseRat?`) or `p/q`.
Both `p` and `q` may carry a sign, as GMP's reader accepts (a negative numerator
over a negative denominator is positive); the value is normalized exactly, so the
written signs cannot change its meaning. -/
def parseNum? (s : String) : Option ℚ :=
  match splitOnChar '/' s.toList with
  | [_] => parseRat? s
  | [num, den] =>
      match parseInt? (String.ofList num), parseInt? (String.ofList den) with
      | some p, some q => if q == 0 then none else some ((p : ℚ) / (q : ℚ))
      | _, _ => none
  | _ => none

/-! ## Parsed AST -/

/-- A `CON` constraint: `name sense rhs (form | OBJ)`. -/
structure ViprCon where
  name : String
  sense : Char        -- 'E' (=), 'L' (≤), 'G' (≥)
  rhs : ℚ
  form : LinForm      -- explicit sparse form; empty when `usesObj`
  usesObj : Bool      -- form is the objective row
  deriving Repr, Inhabited

/-- One local variable bound offered for completing a VIPR v1.1 `lin weak` reason. -/
structure ViprWeakBound where
  kind : Char
  varIdx : Nat
  rowIdx : Nat
  value : ℚ
  deriving Repr, Inhabited

/-- Bounds available while completing a VIPR v1.1 `lin weak` reason.

`global` is the `{ 0 }` spelling; `local` records the explicitly listed local bounds
and permits fallback to the global bounds, as in the reference completer. -/
inductive ViprWeakBounds where
  | global
  | local (bounds : List ViprWeakBound)
  deriving Repr, Inhabited

/-- The justification of a derived constraint. `lin`/`linWeak`/`rnd` carry
`(index, multiplier)` pairs referencing earlier constraints; `uns` carries four earlier
indices. -/
inductive ViprReason where
  | asm
  | lin (terms : List (Nat × ℚ))
  | linWeak (bounds : ViprWeakBounds) (terms : List (Nat × ℚ))
  | rnd (terms : List (Nat × ℚ))
  | uns (i1 l1 i2 l2 : Nat)
  | sol
  deriving Repr, Inhabited

/-- A `DER` derived constraint: `name sense rhs (form | OBJ) { reason } finalUseIdx`. -/
structure ViprDer where
  name : String
  sense : Char
  rhs : ℚ
  form : LinForm
  usesObj : Bool
  reason : ViprReason
  idx : Int            -- trailing final-use index (`-1` = unused)
  isGlobal : Bool := false
  deriving Repr, Inhabited

/-- The `RTP` (relation-to-prove) target. -/
inductive ViprRtp where
  | infeas
  | range (lb ub : Option ℚ)   -- `none` = unbounded (`-inf` / `inf`)
  deriving Inhabited, DecidableEq

/-- Render an optional bound with explicit parentheses. The derived instance prints
`some -7`, which Lean reparses as a subtraction when emitting kernel-mode data. -/
def reprOptionRat : Option ℚ → Std.Format
  | none => "none"
  | some q => "(some (" ++ repr q ++ "))"

instance : Repr ViprRtp where
  reprPrec
    | .infeas, _ => "LeanVIPR.Ast.ViprRtp.infeas"
    | .range lb ub, prec =>
        Repr.addAppParen
          ("LeanVIPR.Ast.ViprRtp.range " ++ reprOptionRat lb ++ " " ++ reprOptionRat ub)
          prec

/-- A parsed VIPR certificate. -/
structure Vipr where
  version : String
  varNames : Array String
  intVars : List Nat
  objSense : String              -- "min" / "max"
  objTerms : List (Nat × ℚ)
  numCon : Nat
  numBounds : Nat
  cons : Array ViprCon
  rtp : ViprRtp
  numSol : Nat
  sols : Array (String × List (Nat × ℚ))
  ders : Array ViprDer
  deriving Repr, Inhabited

/-! ## Tokenizer -/

/-- Split into whitespace-separated tokens (drops empty runs). VIPR pads its
structural tokens (`{`, `}`) with whitespace, so a whitespace split is faithful.

A `%` that begins a token starts a comment that runs to the end of the line. This
covers the leading comment lines of the specification as well as the end-of-line and
interleaved comments used by the reference examples and accepted by `viprchk`. A `%`
inside a token is an ordinary character. -/
def wsTokens (input : List Char) : List String := Id.run do
  let mut toks : List String := []
  let mut cur : List Char := []
  let mut inComment := false
  for c in input do
    if inComment then
      if c == '\n' then inComment := false
    else if c.isWhitespace then
      if !cur.isEmpty then toks := String.ofList cur.reverse :: toks; cur := []
    else if cur.isEmpty && c == '%' then
      inComment := true
    else
      cur := c :: cur
  if !cur.isEmpty then toks := String.ofList cur.reverse :: toks
  return toks.reverse

/-! ## Token consumers (Except-monad parser over `List String`) -/

abbrev Toks := List String

def takeTok : Toks → Except String (String × Toks)
  | [] => Except.error "unexpected end of input"
  | t :: ts => Except.ok (t, ts)

def expectTok (s : String) (ts : Toks) : Except String Toks :=
  match ts with
  | [] => Except.error s!"expected '{s}', got end of input"
  | t :: ts' => if t == s then Except.ok ts' else Except.error s!"expected '{s}', got '{t}'"

def takeNat (ts : Toks) : Except String (Nat × Toks) := do
  let (t, ts') ← takeTok ts
  match natOfDigits? t.toList with
  | some n => Except.ok (n, ts')
  | none   => Except.error s!"expected nat, got '{t}'"

def takeInt (ts : Toks) : Except String (Int × Toks) := do
  let (t, ts') ← takeTok ts
  match parseInt? t with
  | some n => Except.ok (n, ts')
  | none   => Except.error s!"expected int, got '{t}'"

def takeNum (ts : Toks) : Except String (ℚ × Toks) := do
  let (t, ts') ← takeTok ts
  match parseNum? t with
  | some q => Except.ok (q, ts')
  | none   => Except.error s!"expected number, got '{t}'"

def takeSense (ts : Toks) : Except String (Char × Toks) := do
  let (t, ts') ← takeTok ts
  match t.toList with
  | ['E'] => Except.ok ('E', ts')
  | ['L'] => Except.ok ('L', ts')
  | ['G'] => Except.ok ('G', ts')
  | _     => Except.error s!"expected sense E/L/G, got '{t}'"

/-- Read `n` `(index value)` pairs. -/
def takePairs : Nat → Toks → Except String (List (Nat × ℚ) × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (i, ts1) ← takeNat ts
      let (c, ts2) ← takeNum ts1
      let (rest, ts3) ← takePairs n ts2
      Except.ok ((i, c) :: rest, ts3)

/-- Read `n` natural-number tokens. -/
def takeNats : Nat → Toks → Except String (List Nat × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (i, ts1) ← takeNat ts
      let (rest, ts2) ← takeNats n ts1
      Except.ok (i :: rest, ts2)

/-- Read `n` raw tokens (variable names). -/
def takeStrings : Nat → Toks → Except String (List String × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (s, ts1) ← takeTok ts
      let (rest, ts2) ← takeStrings n ts1
      Except.ok (s :: rest, ts2)

/-- Read one `L/U variable-index row-index value` weak-completion bound. -/
def takeWeakBound (ts : Toks) : Except String (ViprWeakBound × Toks) := do
  let (kindTok, ts1) ← takeTok ts
  let kind ←
    match kindTok.toList with
    | ['L'] => Except.ok 'L'
    | ['U'] => Except.ok 'U'
    | _ => Except.error s!"expected weak-bound kind L/U, got '{kindTok}'"
  let (varIdx, ts2) ← takeNat ts1
  let (rowIdx, ts3) ← takeNat ts2
  let (value, ts4) ← takeNum ts3
  Except.ok (⟨kind, varIdx, rowIdx, value⟩, ts4)

def takeWeakBoundsN : Nat → Toks → Except String (List ViprWeakBound × Toks)
  | 0, ts => Except.ok ([], ts)
  | n + 1, ts => do
      let (bound, ts1) ← takeWeakBound ts
      let (rest, ts2) ← takeWeakBoundsN n ts1
      Except.ok (bound :: rest, ts2)

/-- Read the inner `{ 0 }` or `{ n ... }` block of a v1.1 `lin weak` reason. -/
def takeWeakBounds (ts : Toks) : Except String (ViprWeakBounds × Toks) := do
  let ts1 ← expectTok "{" ts
  let (n, ts2) ← takeNat ts1
  let (bounds, ts3) ← takeWeakBoundsN n ts2
  let ts4 ← expectTok "}" ts3
  if n = 0 then
    Except.ok (.global, ts4)
  else
    Except.ok (.local bounds, ts4)

/-- Read a constraint body: `p i₁ a₁ … iₚ aₚ` (returns the form) or `OBJ`. -/
def takeBody (ts : Toks) : Except String ((LinForm × Bool) × Toks) := do
  let (t, ts') ← takeTok ts
  if t == "OBJ" then
    Except.ok (([], true), ts')
  else
    match natOfDigits? t.toList with
    | some p => do
        let (pairs, ts2) ← takePairs p ts'
        Except.ok ((pairs.map (fun q => (⟨q.1, q.2⟩ : Term)), false), ts2)
    | none => Except.error s!"expected count or OBJ, got '{t}'"

def takeCon (ts : Toks) : Except String (ViprCon × Toks) := do
  let (name, ts1) ← takeTok ts
  let (sense, ts2) ← takeSense ts1
  let (rhs, ts3) ← takeNum ts2
  let ((form, usesObj), ts4) ← takeBody ts3
  Except.ok ({ name := name, sense := sense, rhs := rhs, form := form,
               usesObj := usesObj }, ts4)

def takeCons : Nat → Toks → Except String (List ViprCon × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (c, ts1) ← takeCon ts
      let (rest, ts2) ← takeCons n ts1
      Except.ok (c :: rest, ts2)

/-- Read a `{ reason }` block. -/
def takeReason (ts : Toks) : Except String (ViprReason × Toks) := do
  let ts1 ← expectTok "{" ts
  let (kw, ts2) ← takeTok ts1
  match kw with
  | "asm" => do let ts3 ← expectTok "}" ts2; Except.ok (ViprReason.asm, ts3)
  | "sol" => do let ts3 ← expectTok "}" ts2; Except.ok (ViprReason.sol, ts3)
  | "lin" => do
      let (next, ts3) ← takeTok ts2
      if next == "weak" then
        let (bounds, ts4) ← takeWeakBounds ts3
        let (p, ts5) ← takeNat ts4
        let (pairs, ts6) ← takePairs p ts5
        let ts7 ← expectTok "}" ts6
        Except.ok (ViprReason.linWeak bounds pairs, ts7)
      else
        match natOfDigits? next.toList with
        | none => Except.error s!"expected lin count or 'weak', got '{next}'"
        | some p => do
            let (pairs, ts4) ← takePairs p ts3
            let ts5 ← expectTok "}" ts4
            Except.ok (ViprReason.lin pairs, ts5)
  | "rnd" => do
      let (p, ts3) ← takeNat ts2
      let (pairs, ts4) ← takePairs p ts3
      let ts5 ← expectTok "}" ts4
      Except.ok (ViprReason.rnd pairs, ts5)
  | "uns" => do
      let (i1, ts3) ← takeNat ts2
      let (l1, ts4) ← takeNat ts3
      let (i2, ts5) ← takeNat ts4
      let (l2, ts6) ← takeNat ts5
      let ts7 ← expectTok "}" ts6
      Except.ok (ViprReason.uns i1 l1 i2 l2, ts7)
  | _ => Except.error s!"unknown reason '{kw}'"

def takeDer (ts : Toks) : Except String (ViprDer × Toks) := do
  let (name, ts1) ← takeTok ts
  let (sense, ts2) ← takeSense ts1
  let (rhs, ts3) ← takeNum ts2
  let ((form, usesObj), ts4) ← takeBody ts3
  let (reason, ts5) ← takeReason ts4
  let (idx, ts6) ← takeInt ts5
  -- A global one-variable derivation may tighten the bounds used by a later
  -- `lin weak { 0 }` completion.
  let (isGlobal, ts7) := match ts6 with
    | "global" :: rest => (true, rest)
    | "local"  :: rest => (false, rest)
    | _ => (false, ts6)
  Except.ok ({ name := name, sense := sense, rhs := rhs, form := form,
               usesObj := usesObj, reason := reason, idx := idx,
               isGlobal := isGlobal }, ts7)

def takeDers : Nat → Toks → Except String (List ViprDer × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (d, ts1) ← takeDer ts
      let (rest, ts2) ← takeDers n ts1
      Except.ok (d :: rest, ts2)

/-- Read one solution: `name p i₁ v₁ … iₚ vₚ` (best-effort). -/
def takeSol (ts : Toks) : Except String ((String × List (Nat × ℚ)) × Toks) := do
  let (name, ts1) ← takeTok ts
  let (p, ts2) ← takeNat ts1
  let (pairs, ts3) ← takePairs p ts2
  Except.ok ((name, pairs), ts3)

def takeSols : Nat → Toks → Except String (List (String × List (Nat × ℚ)) × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (s, ts1) ← takeSol ts
      let (rest, ts2) ← takeSols n ts1
      Except.ok (s :: rest, ts2)

/-- Read one `RTP range` bound. Only the matching infinity spelling (`-inf` for the
lower bound, `inf` for the upper bound) means unbounded; any other token must be an
exact number, so a malformed bound cannot silently weaken the claim. -/
def takeBound (infinity : String) (t : String) : Except String (Option ℚ) :=
  if t == infinity then
    Except.ok none
  else
    match parseNum? t with
    | some q => Except.ok (some q)
    | none => Except.error s!"expected number or '{infinity}' as RTP bound, got '{t}'"

/-- Variable indices must be declared, and a sparse vector may mention each index at
most once. Duplicate indices have no agreed meaning (the reference checker keeps the
last value, while summing them is also natural), so they are rejected. -/
def checkDistinct (what : String) (idxs : List Nat) : Except String Unit := do
  let sorted := idxs.toArray.qsort (· < ·)
  for k in [1:sorted.size] do
    if sorted[k - 1]! == sorted[k]! then
      throw s!"{what}: duplicate index {sorted[k]!}"

def checkIndices (nvar : Nat) (what : String) (idxs : List Nat) : Except String Unit := do
  if let some i := idxs.find? (· ≥ nvar) then
    throw s!"{what}: variable index {i} out of range (VAR {nvar})"
  checkDistinct what idxs

/-- A solution vector may repeat a variable index only with the same value; repeated
indices with different values have no single meaning (the reference checker keeps the
last value). -/
def checkSolution (nvar : Nat) (what : String) (vals : List (Nat × ℚ)) :
    Except String Unit := do
  if let some (i, _) := vals.find? (·.1 ≥ nvar) then
    throw s!"{what}: variable index {i} out of range (VAR {nvar})"
  let sorted := vals.toArray.qsort (fun a b => a.1 < b.1)
  for k in [1:sorted.size] do
    if sorted[k - 1]!.1 == sorted[k]!.1 && sorted[k - 1]!.2 != sorted[k]!.2 then
      throw s!"{what}: conflicting values for variable index {sorted[k]!.1}"

def checkFormIndices (nvar : Nat) (what : String) (f : LinForm) : Except String Unit :=
  checkIndices nvar what (f.map (·.idx))

/-- Well-formedness of every sparse vector that contributes to the claimed problem or
to a stated derived row. -/
def validateVipr (v : Vipr) : Except String Unit := do
  let nvar := v.varNames.size
  if let some i := v.intVars.find? (· ≥ nvar) then
    throw s!"INT: variable index {i} out of range (VAR {nvar})"
  checkIndices nvar "OBJ" (v.objTerms.map Prod.fst)
  for c in v.cons do
    checkFormIndices nvar s!"CON {c.name}" c.form
  for s in v.sols do
    checkSolution nvar s!"SOL {s.1}" s.2
  for d in v.ders do
    checkFormIndices nvar s!"DER {d.name}" d.form
    -- The specification requires the constraint indices of `lin` and `rnd` reasons
    -- to be distinct; the reference checker silently keeps the last multiplier.
    match d.reason with
    | .lin terms | .linWeak _ terms | .rnd terms =>
        checkDistinct s!"DER {d.name} reason" (terms.map Prod.fst)
    | _ => pure ()

/-! ## Top-level parser -/

def parseVipr (content : String) : Except String Vipr := do
  let ts0 := wsTokens content.toList
  let ts1 ← expectTok "VER" ts0
  let (ver, ts2) ← takeTok ts1
  let ts3 ← expectTok "VAR" ts2
  let (nvar, ts4) ← takeNat ts3
  let (names, ts5) ← takeStrings nvar ts4
  let ts6 ← expectTok "INT" ts5
  let (nint, ts7) ← takeNat ts6
  let (ints, ts8) ← takeNats nint ts7
  let ts9 ← expectTok "OBJ" ts8
  let (objsense, ts10) ← takeTok ts9
  let (nobj, ts11) ← takeNat ts10
  let (objterms, ts12) ← takePairs nobj ts11
  let ts13 ← expectTok "CON" ts12
  let (ncon, ts14) ← takeNat ts13
  let (nbound, ts15) ← takeNat ts14
  let (cons, ts16) ← takeCons ncon ts15
  let ts17 ← expectTok "RTP" ts16
  let (rtpkind, ts18) ← takeTok ts17
  let (rtp, ts19) ←
    if rtpkind == "infeas" then
      (Except.ok (ViprRtp.infeas, ts18) : Except String (ViprRtp × Toks))
    else if rtpkind == "range" then do
      let (lb, tsa) ← takeTok ts18
      let (ub, tsb) ← takeTok tsa
      let lower ← takeBound "-inf" lb
      let upper ← takeBound "inf" ub
      Except.ok (ViprRtp.range lower upper, tsb)
    else
      Except.error s!"unknown RTP kind '{rtpkind}'"
  let ts20 ← expectTok "SOL" ts19
  let (nsol, ts21) ← takeNat ts20
  let (sols, ts22) ← takeSols nsol ts21
  let ts23 ← expectTok "DER" ts22
  let (nder, ts24) ← takeNat ts23
  let (ders, ts25) ← takeDers nder ts24
  if let t :: _ := ts25 then
    throw s!"unexpected token after DER section: '{t}'"
  let v : Vipr := {
    version := ver,
    varNames := names.toArray,
    intVars := ints,
    objSense := objsense,
    objTerms := objterms,
    numCon := ncon,
    numBounds := nbound,
    cons := cons.toArray,
    rtp := rtp,
    numSol := nsol,
    sols := sols.toArray,
    ders := ders.toArray }
  validateVipr v
  return v

/-! ## Objective references -/

/-- Resolve a `CON` constraint's linear form, substituting the objective row when the
constraint uses `OBJ`. -/
def ViprCon.resolvedForm (c : ViprCon) (objTerms : List (Nat × ℚ)) : LinForm :=
  if c.usesObj then objTerms.map (fun q => (⟨q.1, q.2⟩ : Term)) else c.form

end LeanVIPR.Ast
