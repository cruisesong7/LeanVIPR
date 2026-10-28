module

public import LeanVIPR.Ast.Vipr
public import LeanVIPR.Cert.ViprSem

@[expose] public section

/-!
# Parsed VIPR certificates and the executable checker

This module maps the parsed `CON` and `DER` records directly to the sensed
constraint representation used by the verified checker. VIPR indices match the
pool indices because equality rows remain single sensed rows.
-/

namespace LeanVIPR.Pipeline

open LeanVIPR.Cert LeanVIPR.Ast

/-- Resolve one parsed constraint to the sensed representation used by the checker. -/
def conToSLe (v : Vipr) (c : ViprCon) : SLe :=
  ⟨c.sense, c.resolvedForm v.objTerms, c.rhs⟩

/-- The sensed constraint rows of the certificate, with objective references resolved. -/
def conSLes (v : Vipr) : List SLe :=
  v.cons.toList.map (conToSLe v)

/-- Resolve a derivation's stated form, substituting the objective when requested. -/
def derForm (v : Vipr) (d : ViprDer) : LinForm :=
  if d.usesObj then v.objTerms.map (fun q => (⟨q.1, q.2⟩ : Term)) else d.form

/-- Resolve one parsed derivation's stated row. -/
def derStated (v : Vipr) (d : ViprDer) : SLe :=
  ⟨d.sense, derForm v d, d.rhs⟩

/-- Lookup a certificate row by its VIPR index. References to malformed indices use the
same harmless default row as the replay pool and are subsequently rejected by the
references-past check. -/
def viprRow (v : Vipr) (idx : Nat) : SLe :=
  if h : idx < v.cons.size then
    conToSLe v v.cons[idx]
  else
    let derIdx := idx - v.cons.size
    if hder : derIdx < v.ders.size then derStated v v.ders[derIdx] else sdflt.1

/-- Coefficient of one variable after combining duplicate sparse terms. -/
def formCoeff (form : LinForm) (idx : Nat) : ℚ :=
  form.foldl (fun coeff term => if term.idx = idx then coeff + term.coeff else coeff) 0

/-- The normalized row contains no nonzero coefficient except possibly at `idx`. -/
def onlyVarB (form : LinForm) (idx : Nat) : Bool :=
  (normForm form).all (fun term => decide (term.1 = idx ∨ term.2 = 0))

/-- Does a one-variable row with sense `sense` and nonzero coefficient `coeff` express a
lower (`L`) or upper (`U`) bound on its variable? -/
def boundKindB (sense : Char) (coeff : ℚ) (kind : Char) : Bool :=
  if kind = 'L' then
    (sense = 'G' && 0 < coeff) || (sense = 'L' && coeff < 0)
  else if kind = 'U' then
    (sense = 'L' && 0 < coeff) || (sense = 'G' && coeff < 0)
  else
    false

/-- Does `row` express a lower (`L`) or upper (`U`) bound on variable `idx`? -/
def boundRowB (row : SLe) (kind : Char) (idx : Nat) : Bool :=
  let coeff := formCoeff row.form idx
  onlyVarB row.form idx && decide (coeff ≠ 0) && boundKindB row.sense coeff kind

/-- The variable and coefficient of a row with exactly one nonzero normalized term. -/
def singleVar? (form : LinForm) : Option (Nat × ℚ) :=
  match (normForm form).filter (fun term => term.2 ≠ 0) with
  | [term] => some term
  | _ => none

/-- Candidate rows for SCIP's global-bound table, indexed by variable: every original
one-variable constraint and every one-variable derived row marked `global`, each with its
row index and coefficient, in increasing row order. Built once per certificate. -/
def boundTable (v : Vipr) : Array (Array (Nat × ℚ)) := Id.run do
  let mut table := Array.replicate v.varNames.size #[]
  for rowIdx in [:v.cons.size + v.ders.size] do
    let eligible :=
      rowIdx < v.cons.size || (v.ders.getD (rowIdx - v.cons.size) default).isGlobal
    if eligible then
      if let some (idx, coeff) := singleVar? (viprRow v rowIdx).form then
        table := table.modify idx (·.push (rowIdx, coeff))
  return table

/-- Find the tightest matching global bound available before derivation `derIdx`: an
original row, or a `global` derived row that precedes the derivation. Ties keep the
earliest row. -/
def globalBoundRef? (v : Vipr) (table : Array (Array (Nat × ℚ))) (derIdx : Nat)
    (kind : Char) (idx : Nat) : Option Nat :=
  let best := (table.getD idx #[]).foldl (fun best (rowIdx, coeff) =>
    let row := viprRow v rowIdx
    if rowIdx < v.cons.size + derIdx && boundKindB row.sense coeff kind then
      let value := row.rhs / coeff
      match best with
      | none => some (rowIdx, value)
      | some current =>
          if (kind = 'L' && current.2 < value) || (kind = 'U' && value < current.2) then
            some (rowIdx, value)
          else
            best
    else
      best) none
  best.map Prod.fst

/-- Find the explicitly listed local bound for a variable, checking that the referenced
row really expresses the declared bound value. If no local bound is listed, fall back to
the current global bound table as prescribed by the v1.1 completion algorithm. -/
def weakBoundRef? (v : Vipr) (table : Array (Array (Nat × ℚ))) (derIdx : Nat)
    (bounds : ViprWeakBounds) (kind : Char) (idx : Nat) : Option Nat :=
  match bounds with
  | .global => globalBoundRef? v table derIdx kind idx
  | .local localBounds =>
      match localBounds.find? (fun bound => bound.kind = kind && bound.varIdx = idx) with
      | some bound =>
          let row := viprRow v bound.rowIdx
          let coeff := formCoeff row.form idx
          if boundRowB row kind idx && decide (row.rhs = coeff * bound.value) then
            some bound.rowIdx
          else
            none
      | none => globalBoundRef? v table derIdx kind idx

/-- Which variable-bound direction repairs coefficient `delta` while preserving the
sense of the stated row? -/
def correctionKind? (sense : Char) (delta : ℚ) : Option Char :=
  if delta = 0 then
    none
  else if sense = 'L' then
    some (if delta < 0 then 'L' else 'U')
  else if sense = 'G' then
    some (if 0 < delta then 'L' else 'U')
  else
    none

/-- Complete a VIPR v1.1 `lin weak` reason with variable-bound rows.

Corrections are proposed only for the variables whose coefficient differs between the
stated row and the listed combination, in increasing variable order.

This function only proposes an ordinary `lin` combination. The existing `linCheck`
recomputes that combination from the actual referenced rows and rejects any malformed
or insufficient completion, so checker soundness does not trust this algorithm. -/
def completeWeakComb (v : Vipr) (table : Array (Array (Nat × ℚ))) (derIdx : Nat)
    (stated : SLe) (bounds : ViprWeakBounds) (terms : List (Nat × ℚ)) : List (ℚ × Nat) :=
  let baseComb := terms.map (fun term => (term.2, term.1))
  let combined := scomb (baseComb.map (fun term => (term.1, viprRow v term.2)))
  let deltas := ((normForm (stated.form ++ sNegForm combined.form)).filter
    (fun term => term.1 < v.varNames.size)).mergeSort (fun a b => a.1 ≤ b.1)
  let corrections := deltas.filterMap fun (idx, delta) =>
    match correctionKind? stated.sense delta with
    | none => none
    | some kind =>
        match weakBoundRef? v table derIdx bounds kind idx with
        | none => none
        | some rowIdx =>
            let coeff := formCoeff (viprRow v rowIdx).form idx
            if coeff = 0 then none else some (delta / coeff, rowIdx)
  baseComb ++ corrections

/-- Interpret one parsed derivation as a sensed checker step. -/
def derToSStep (v : Vipr) (table : Array (Array (Nat × ℚ))) (derIdx : Nat)
    (d : ViprDer) : SStep :=
  { stated := derStated v d
    reason := match d.reason with
      | .asm => .asm
      | .lin terms => .lin (terms.map (fun p => (p.2, p.1)))
      | .linWeak bounds terms =>
          .lin (completeWeakComb v table derIdx (derStated v d) bounds terms)
      | .rnd terms => .rnd (terms.map (fun p => (p.2, p.1)))
      | .uns i1 l1 i2 l2 => .uns i1 l1 i2 l2
      | .sol => .sol }

/-- The replayed steps. The bound table is only consulted by `lin weak` reasons. -/
def viprSteps (v : Vipr) : List SStep :=
  let table := boundTable v
  v.ders.toList.mapIdx (derToSStep v table)

end LeanVIPR.Pipeline
