module

public import LeanVIPR.Impl.Parser.Utils
public import LeanVIPR.Spec.Syntax.Ast

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

`LeanVIPR.Semantics.Lower` maps the parsed rows and derivations to the sensed rows (`SLe`)
replayed by the checker.

The `SOL` section is parsed as exact sparse vectors and is checked for `RTP range`.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Semantics

/-! ## Tokenizer -/

/-- Drop the rest of a `%` comment, retaining the terminating newline as a separator. -/
def dropComment : List Char → List Char
  | [] => []
  | c :: cs => if c == '\n' then c :: cs else dropComment cs

theorem dropComment_length_le : ∀ cs : List Char, (dropComment cs).length ≤ cs.length
  | [] => by simp [dropComment]
  | c :: cs => by
      by_cases h : c == '\n'
      · simp [dropComment, h]
      · have ih := dropComment_length_le cs
        simp only [dropComment, h, Bool.false_eq_true, ite_false, List.length_cons]
        omega

/-- Characters of the token that continues here, and the input after it. -/
def takeToken : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c.isWhitespace then ([], c :: cs)
      else
        let (t, r) := takeToken cs
        (c :: t, r)

theorem takeToken_length_lt : ∀ (c : Char) (cs : List Char),
    (takeToken cs).2.length < (c :: cs).length
  | _, [] => by simp [takeToken]
  | _, d :: ds => by
      by_cases h : d.isWhitespace
      · simp [takeToken, h]
      · have := takeToken_length_lt d ds
        simp only [takeToken, h, Bool.false_eq_true, ite_false, List.length_cons] at *
        omega

/-- Split into whitespace-separated tokens: the maximal nonempty runs of
non-whitespace characters, in order.

A `%` that begins a token starts a comment running to the end of the line. This covers
the specification's leading comment lines as well as the end-of-line and interleaved
comments used by the reference examples and accepted by `viprchk`. A `%` inside a token
is an ordinary character, so `x%y` is one token.

Written as a structural recursion rather than a loop over mutable state, so that the
tokenization a certificate receives can be read off the definition. -/
def wsTokens : List Char → List String
  | [] => []
  | c :: cs =>
      if c.isWhitespace then wsTokens cs
      else if c == '%' then wsTokens (dropComment cs)
      else
        match _h : takeToken cs with
        | (t, r) => String.ofList (c :: t) :: wsTokens r
  termination_by cs => cs.length
  decreasing_by
  · simp
  · exact Nat.lt_of_le_of_lt (dropComment_length_le cs) (by simp)
  · have hr : (takeToken cs).2 = r := by rw [_h]
    rw [← hr]
    exact takeToken_length_lt c cs

/-! ## Token consumers (Except-monad parser over `List String`) -/

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

/-- The kind of a weak-completion bound: a lower (`L`) or upper (`U`) variable bound. -/
def weakKind? (t : String) : Option Char :=
  match t.toList with
  | ['L'] => some 'L'
  | ['U'] => some 'U'
  | _ => none

/-- Read one `L/U variable-index row-index value` weak-completion bound. -/
def takeWeakBound (ts : Toks) : Except String (ViprWeakBound × Toks) := do
  let (kindTok, ts1) ← takeTok ts
  match weakKind? kindTok with
  | none => Except.error s!"expected weak-bound kind L/U, got '{kindTok}'"
  | some kind => do
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

/-- Read the inner `{ 0 }` or `{ n ... }` block of a v1.1 `lin weak` reason. The empty
list is the `{ 0 }` spelling, since `takeWeakBoundsN n` returns exactly `n` bounds. -/
def takeWeakBounds (ts : Toks) : Except String (ViprWeakBounds × Toks) := do
  let ts1 ← expectTok "{" ts
  let (n, ts2) ← takeNat ts1
  let (bounds, ts3) ← takeWeakBoundsN n ts2
  let ts4 ← expectTok "}" ts3
  match bounds with
  | [] => Except.ok (.global, ts4)
  | _ => Except.ok (.local bounds, ts4)

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

/-- Read a `{ reason }` block. `name` labels the row in diagnostics.

Every reason this returns maps to a checkable step in `LeanVIPR.Semantics.Lower`, so an
unsupported-but-well-formed reason is rejected here rather than being carried into
the certificate. `lin weak` is supported: it is completed from variable-bound rows
and the completion is rechecked. `lin incomplete` supplies no multipliers at all and
requires solving an exact LP to recover them, which is the job of a completer such as
the reference `viprcomp`; it is therefore reported as unsupported. -/
def takeReason (name : String) (ts : Toks) : Except String (ViprReason × Toks) := do
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
        | none =>
            if next == "incomplete" then
              Except.error
                s!"{name}: 'lin incomplete' is not supported; complete the \
                   certificate first (for example with viprcomp)"
            else
              Except.error s!"{name}: expected lin count or 'weak', got '{next}'"
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
  | _ => Except.error s!"{name}: unknown reason '{kw}'"

/-- Read the optional v1.1 scope keyword that may follow a `DER` row's final-use index.
A global one-variable derivation may tighten the bounds used by a later
`lin weak { 0 }` completion.

The keyword is optional and unbracketed, so it is matched greedily: a row *named*
`global` or `local` immediately after a flagless row would be read as that row's flag.
`LeanVIPR.Thm.Parser.Grammar.IsDers` states this rule, so the exclusion is visible in the
grammar rather than hidden here. -/
def takeScope : Toks → Bool × Toks
  | "global" :: rest => (true, rest)
  | "local" :: rest => (false, rest)
  | ts => (false, ts)

def takeDer (ts : Toks) : Except String (ViprDer × Toks) := do
  let (name, ts1) ← takeTok ts
  let (sense, ts2) ← takeSense ts1
  let (rhs, ts3) ← takeNum ts2
  let ((form, usesObj), ts4) ← takeBody ts3
  let (reason, ts5) ← takeReason name ts4
  let (idx, ts6) ← takeInt ts5
  let scope := takeScope ts6
  Except.ok ({ name := name, sense := sense, rhs := rhs, form := form,
               usesObj := usesObj, reason := reason, idx := idx,
               isGlobal := scope.1 }, scope.2)

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

/-- Run a check on every element, reporting the first failure. -/
def checkAll {α : Type} (f : α → Except String Unit) : List α → Except String Unit
  | [] => Except.ok ()
  | a :: as => do f a; checkAll f as

/-- The first value repeated adjacently, if any. On a sorted list this finds a duplicate
exactly when there is one, which is why the callers sort first. -/
def firstAdjacentDup : List Nat → Option Nat
  | [] => none
  | [_] => none
  | a :: b :: rest => if a = b then some a else firstAdjacentDup (b :: rest)

/-- The first key given two different values adjacently, if any. -/
def firstKeyConflict : List (Nat × ℚ) → Option Nat
  | [] => none
  | [_] => none
  | a :: b :: rest =>
      if a.1 = b.1 ∧ a.2 ≠ b.2 then some a.1 else firstKeyConflict (b :: rest)

/-- Variable indices must be declared, and a sparse vector may mention each index at
most once. Duplicate indices have no agreed meaning (the reference checker keeps the
last value, while summing them is also natural), so they are rejected.

Sorting with `mergeSort` rather than `qsort` keeps this `O(n log n)` while leaving it
provable: `List.pairwise_mergeSort` and `List.mergeSort_perm` are what
`LeanVIPR.Thm.Parser.Valid` needs to show the adjacent-duplicate scan decides `List.Nodup`. -/
def checkDistinct (what : String) (idxs : List Nat) : Except String Unit :=
  match firstAdjacentDup (idxs.mergeSort (fun a b => decide (a ≤ b))) with
  | some i => Except.error s!"{what}: duplicate index {i}"
  | none => Except.ok ()

def checkIndices (nvar : Nat) (what : String) (idxs : List Nat) : Except String Unit :=
  match idxs.find? (fun i => decide (nvar ≤ i)) with
  | some i => Except.error s!"{what}: variable index {i} out of range (VAR {nvar})"
  | none => checkDistinct what idxs

/-- A solution vector may repeat a variable index only with the same value; repeated
indices with different values have no single meaning (the reference checker keeps the
last value). -/
def checkSolution (nvar : Nat) (what : String) (vals : List (Nat × ℚ)) :
    Except String Unit :=
  match vals.find? (fun p => decide (nvar ≤ p.1)) with
  | some p => Except.error s!"{what}: variable index {p.1} out of range (VAR {nvar})"
  | none =>
      match firstKeyConflict (vals.mergeSort (fun a b => decide (a.1 ≤ b.1))) with
      | some i => Except.error s!"{what}: conflicting values for variable index {i}"
      | none => Except.ok ()

def checkFormIndices (nvar : Nat) (what : String) (f : LinForm) : Except String Unit :=
  checkIndices nvar what (f.map (·.idx))

/-- The derivations in `ds`, whose first element has index `pos`, that use a constraint
after that constraint's declared final-use index — paired with the offending
reference. -/
def finalUseViolations (v : Vipr) (pos : Nat) : List ViprDer → List (ViprDer × Nat)
  | [] => []
  | d :: ds =>
      ((reasonRefs d.reason).filterMap fun k =>
        if usedAfterFinal v (v.cons.size + pos) k then some (d, k) else none)
      ++ finalUseViolations v (pos + 1) ds

/-- The `DER` section's trailing field is `-1`, or an index such that no constraint with
a larger index refers to this one (spec, `DER` section). It lets a verifier discard the
constraint from memory once that index has been checked, so a derivation that is used
after its own final-use index is ill-formed; the reference checker reports it as a
trashed constraint. Soundness does not depend on this, but conformance does. -/
def checkFinalUse (v : Vipr) : Except String Unit :=
  match finalUseViolations v 0 v.ders.toList with
  | [] => Except.ok ()
  | (d, k) :: _ =>
      Except.error s!"DER {d.name} refers to constraint {k}, whose final-use index is \
                      {finalUseHint v k}"

/-- Well-formedness of every sparse vector that contributes to the claimed problem or
to a stated derived row. -/
def validateVipr (v : Vipr) : Except String Unit :=
  match v.intVars.find? (fun i => decide (v.varNames.size ≤ i)) with
  | some i =>
      Except.error s!"INT: variable index {i} out of range (VAR {v.varNames.size})"
  | none => do
      checkIndices v.varNames.size "OBJ" (v.objTerms.map Prod.fst)
      checkAll (fun c => checkFormIndices v.varNames.size s!"CON {c.name}" c.form)
        v.cons.toList
      checkAll (fun s => checkSolution v.varNames.size s!"SOL {s.1}" s.2) v.sols.toList
      checkAll (fun d => do
        checkFormIndices v.varNames.size s!"DER {d.name}" d.form
        checkDistinct s!"DER {d.name} reason" (reasonMultipliers d.reason)) v.ders.toList
      checkFinalUse v

/-- Read the `RTP` (relation-to-prove) section: `RTP infeas`, or `RTP range lb ub`. -/
def takeRtp (ts : Toks) : Except String (ViprRtp × Toks) := do
  let ts1 ← expectTok "RTP" ts
  let (rtpkind, ts2) ← takeTok ts1
  if rtpkind == "infeas" then
    Except.ok (ViprRtp.infeas, ts2)
  else if rtpkind == "range" then do
    let (lb, tsa) ← takeTok ts2
    let (ub, tsb) ← takeTok tsa
    let lower ← takeBound "-inf" lb
    let upper ← takeBound "inf" ub
    Except.ok (ViprRtp.range lower upper, tsb)
  else
    Except.error s!"unknown RTP kind '{rtpkind}'"

/-! ## Top-level parser -/

/-- Parse a tokenized certificate. Separated from `parseVipr` so that the grammar
correspondence in `LeanVIPR.Thm.Parser.Certificate` is stated where the grammar lives: on tokens. -/
def parseViprToks (ts0 : Toks) : Except String Vipr := do
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
  let (rtp, ts19) ← takeRtp ts16
  let ts20 ← expectTok "SOL" ts19
  let (nsol, ts21) ← takeNat ts20
  let (sols, ts22) ← takeSols nsol ts21
  let ts23 ← expectTok "DER" ts22
  let (nder, ts24) ← takeNat ts23
  let (ders, ts25) ← takeDers nder ts24
  match ts25 with
  | t :: _ => Except.error s!"unexpected token after DER section: '{t}'"
  | [] =>
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
      Except.ok v

def parseVipr (content : String) : Except String Vipr :=
  parseViprToks (wsTokens content.toList)

end LeanVIPR.Parser
