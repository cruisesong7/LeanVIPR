module

public meta import LeanVIPRTactic.Certify
public meta import LeanVIPRTactic.Config
public meta import Lean.Meta.Tactic.TryThis
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.Rify

@[expose] public section

/-!
# `mip`: close a linear-arithmetic goal with a solver certificate

Stages 4 and 5 of `docs/TACTIC-TODO.md`. The goal shapes are catalogued, with a proof of
each, in `examples/mip_prop_goals.lean`, and exercised in `examples/mip_tactic_tests.lean`.

```
⊢ goal                                       (a comparison, False, ¬ ∃ …, ∀ … → False)
  │ negate the goal, split ∨ and ≠           (metacode)
  │ read each hypothesis as a linear row     (metacode, untrusted)
  ▼
m : Mip  ─ certify ─▶  m.Infeasible          (kernel-checked; Certify.lean)
  │ Mip.absurd_of_infeasible_mixed
  ▼ False
```

**Why none of this needs trusting.** The reflector builds a `Mip` and *claims* it is the
user's problem. That claim is never assumed: `Mip.absurd_of_infeasible_mixed` demands a proof that the
user's own variables, cast to `ℝ`, satisfy every row of `m.conSLes`, discharged against the
hypotheses actually in context; integrality holds by construction, since the integer
variables are passed as integers. A misread hypothesis gives a `Mip` whose rows cannot be proved, and the tactic
fails. The only thing it can cost is a failure — the same contract the solver has.

**The fragment.** Variables of type `ℕ`, `ℤ`, `ℚ` or `ℝ`, mixed freely: an integer
variable may appear, cast, in a rational or real hypothesis. Hypotheses are linear
comparisons (`≤ < = ≥ >` and their negations) with rational literal coefficients,
including `1/2`, `0.25` and division by a literal over `ℚ` and `ℝ`. Anything else in the
context is ignored. Strict comparisons are exact over `ℕ` and `ℤ` (tightened by one) and
*relaxed* to non-strict ones over `ℚ` and `ℝ`: sound, since a relaxed problem with no
solution means the original has none, but a goal that depends on strictness fails. A `∨`
of two bounded comparisons, or a `≠` over `ℕ` or `ℤ`, is encoded with a fresh binary; any
other `∨` or `≠` is split into cases, each solved separately.
-/

namespace LeanVIPR.Tactic

open Lean Elab Tactic Meta
open LeanVIPR LeanVIPR.Parser

/-! ## Variables

A variable of the problem is one of the user's locals. Its type fixes whether the problem
declares it integral and how it is cast to `ℝ` for the bridge theorem. -/

inductive Carrier where
  | nat | int | rat | real

meta def carrierOf? (ty : Expr) : Option Carrier :=
  if ty.isConstOf ``Nat then some .nat
  else if ty.isConstOf ``Int then some .int
  else if ty.isConstOf ``Rat then some .rat
  else if ty.isConstOf ``Real then some .real
  else none

meta def Carrier.isInt : Carrier → Bool
  | .nat | .int => true
  | .rat | .real => false

meta def Carrier.isNat : Carrier → Bool
  | .nat => true
  | _ => false

/-- A variable of the problem: one of the user's locals, or an *opaque* term — a product,
an application, a truncated subtraction — that the problem treats as a variable of its
own. `expr` is its value, which the bridge theorem is instantiated at. -/
structure Atom where
  expr : Expr
  name : Name
  carrier : Carrier

/-! ## Reading a linear expression

Hand-rolled rather than borrowed from `linarith`'s preprocessing, because what is needed is
small and a reader that silently accepted more than a `Mip` can express would turn a clear
failure into a confusing one. Two things are refused on purpose: subtraction over `ℕ`,
which truncates, and division over `ℕ` or `ℤ`, which rounds. -/

/-- Whether an arithmetic operation's type argument is `ℕ` or `ℤ`. -/
meta def isDiscrete (α : Expr) : Bool := α.isConstOf ``Nat || α.isConstOf ``Int

/-- A rational literal: numerals, casts of numerals, negation, `+ - * /`, `⁻¹` and decimal
notation, so `(1/2 : ℚ)`, `0.25` and `((3 : ℤ) : ℝ)` all read as numbers. -/
meta partial def ratLit? (e : Expr) : Option ℚ :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?.map (fun k => (k : ℚ))
  | (``Neg.neg, #[_, _, a]) => (ratLit? a).map (- ·)
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do return (← ratLit? a) + (← ratLit? b)
  | (``HSub.hSub, #[α, _, _, _, a, b]) => do
      guard (!α.isConstOf ``Nat)
      return (← ratLit? a) - (← ratLit? b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do return (← ratLit? a) * (← ratLit? b)
  | (``HDiv.hDiv, #[α, _, _, _, a, b]) => do
      guard (!isDiscrete α)
      let qb ← ratLit? b
      guard (qb != 0)
      return (← ratLit? a) / qb
  | (``Inv.inv, #[α, _, a]) => do
      guard (!isDiscrete α)
      let qa ← ratLit? a
      guard (qa != 0)
      return qa⁻¹
  | (``OfScientific.ofScientific, #[_, _, m, s, x]) => do
      let mv ← m.rawNatLit?
      let xv ← x.rawNatLit?
      if s.isConstOf ``Bool.true then return (mv : ℚ) / ((10 ^ xv : ℕ) : ℚ)
      else return (mv : ℚ) * ((10 ^ xv : ℕ) : ℚ)
  | (``Nat.cast, #[_, _, a]) | (``NatCast.natCast, #[_, _, a])
  | (``Int.cast, #[_, _, a]) | (``IntCast.intCast, #[_, _, a])
  | (``Rat.cast, #[_, _, a]) | (``RatCast.ratCast, #[_, _, a]) => ratLit? a
  | (``Int.negOfNat, #[n]) => n.rawNatLit?.map (fun k => -(k : ℚ))
  | (``Int.ofNat, #[n]) => ratLit? n
  | _ => e.rawNatLit?.map (fun k => (k : ℚ))

/-- `e` without the casts around it. -/
meta partial def stripCasts (e : Expr) : Expr :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, a]) | (``NatCast.natCast, #[_, _, a])
  | (``Int.cast, #[_, _, a]) | (``IntCast.intCast, #[_, _, a])
  | (``Rat.cast, #[_, _, a]) | (``RatCast.ratCast, #[_, _, a]) => stripCasts a
  | _ => e

/-- The variable `e` stands for, seeing through casts: `x`, `(x : ℚ)` and `((x : ℤ) : ℝ)`
are all the variable `x`. -/
meta def atomOf? (atoms : Array Atom) (e : Expr) : Option Nat :=
  let e := stripCasts e
  atoms.findIdx? (·.expr == e)

/-- The linear form of `e` over `atoms`, as coefficients and a constant, or `none` if `e`
is not linear in them. Casts distribute: they are ring homomorphisms, and the one that is
not — `ℕ` to anything, over subtraction — is refused where the subtraction occurs. -/
meta partial def linearOf (atoms : Array Atom) (e : Expr) : Option (Array ℚ × ℚ) := do
  let zero := atoms.map (fun _ => (0 : ℚ))
  if let some q := ratLit? e then return (zero, q)
  if let some i := atomOf? atoms e then return (zero.set! i 1, 0)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (ca, ka) ← linearOf atoms a
      let (cb, kb) ← linearOf atoms b
      return (ca.zipWith (· + ·) cb, ka + kb)
  | (``HSub.hSub, #[α, _, _, _, a, b]) => do
      guard (!α.isConstOf ``Nat)
      let (ca, ka) ← linearOf atoms a
      let (cb, kb) ← linearOf atoms b
      return (ca.zipWith (· - ·) cb, ka - kb)
  | (``Neg.neg, #[_, _, a]) => do
      let (ca, ka) ← linearOf atoms a
      return (ca.map (- ·), -ka)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      if let some q := ratLit? a then do
        let (cb, kb) ← linearOf atoms b
        return (cb.map (q * ·), q * kb)
      else if let some q := ratLit? b then do
        let (ca, ka) ← linearOf atoms a
        return (ca.map (· * q), ka * q)
      else none
  | (``HDiv.hDiv, #[α, _, _, _, a, b]) => do
      guard (!isDiscrete α)
      let q ← ratLit? b
      guard (q != 0)
      let (ca, ka) ← linearOf atoms a
      return (ca.map (· / q), ka / q)
  | (``Nat.cast, #[_, _, a]) | (``NatCast.natCast, #[_, _, a])
  | (``Int.cast, #[_, _, a]) | (``IntCast.intCast, #[_, _, a])
  | (``Rat.cast, #[_, _, a]) | (``RatCast.ratCast, #[_, _, a]) => linearOf atoms a
  | _ => none

/-- Register the non-linear leaves of `e` as opaque atoms, the way `lp` atomizes: a
product of two terms, an application, a subtraction over `ℕ` and a division over `ℕ` or
`ℤ` each become a variable of the problem. That is a relaxation — the problem forgets how
the atom depends on the rest — so it can only make a provable goal unprovable, never the
reverse. An atom of type `ℕ` or `ℤ` stays integral, and one of type `ℕ` nonnegative. -/
meta partial def collectOpaque (atoms : Array Atom) (e : Expr) : MetaM (Array Atom) := do
  if (linearOf atoms e).isSome then return atoms
  let add : MetaM (Array Atom) := do
    if atoms.any (·.expr == e) then return atoms
    let some c := carrierOf? (← instantiateMVars (← inferType e)) | return atoms
    return atoms.push { expr := e, name := `t, carrier := c }
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => collectOpaque (← collectOpaque atoms a) b
  | (``HSub.hSub, #[α, _, _, _, a, b]) =>
      if α.isConstOf ``Nat then add else collectOpaque (← collectOpaque atoms a) b
  | (``Neg.neg, #[_, _, a]) => collectOpaque atoms a
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      if (ratLit? a).isSome then collectOpaque atoms b
      else if (ratLit? b).isSome then collectOpaque atoms a
      else add
  | (``HDiv.hDiv, #[α, _, _, _, a, b]) =>
      if !isDiscrete α && (ratLit? b).isSome then collectOpaque atoms a else add
  | (``Nat.cast, #[_, _, a]) | (``NatCast.natCast, #[_, _, a])
  | (``Int.cast, #[_, _, a]) | (``IntCast.intCast, #[_, _, a])
  | (``Rat.cast, #[_, _, a]) | (``RatCast.ratCast, #[_, _, a]) => collectOpaque atoms a
  | _ => add

/-- The type and two sides of a comparison, or of the negation of one. -/
meta def cmpSides? (ty : Expr) : Option (Expr × Expr × Expr) :=
  let body := match ty.getAppFnArgs with
    | (``Not, #[p]) => p
    | _ => ty
  match body.getAppFnArgs with
  | (``LE.le, #[t, _, a, b]) | (``LT.lt, #[t, _, a, b])
  | (``GE.ge, #[t, _, a, b]) | (``GT.gt, #[t, _, a, b]) => some (t, a, b)
  | (``Eq, #[t, a, b]) => some (t, a, b)
  | _ => none

/-! ## Reading a hypothesis -/

/-- A hypothesis read as `coeffs · x  sense  rhs`, with `sense` one of `'L'`, `'G'`, `'E'`.
`relaxed` records a strict comparison over `ℚ` or `ℝ` read as a non-strict one. -/
structure LinRow where
  coeffs : Array ℚ
  sense : Char
  rhs : ℚ
  relaxed : Bool := false

inductive Cmp where
  | le | lt | ge | gt | eq

/-- `a ⋈ b` over the type `t`, as a row. Over `ℕ` and `ℤ` both sides are integers, so a
strict comparison is tightened by one; over a field it is relaxed. -/
meta def cmpRow (atoms : Array Atom) (k : Cmp) (t a b : Expr) : Option LinRow := do
  let c ← carrierOf? t
  let (ca, ka) ← linearOf atoms a
  let (cb, kb) ← linearOf atoms b
  let coeffs := ca.zipWith (· - ·) cb
  let rhs := kb - ka
  match k with
  | .le => return { coeffs, sense := 'L', rhs }
  | .ge => return { coeffs, sense := 'G', rhs }
  | .eq => return { coeffs, sense := 'E', rhs }
  | .lt => return if c.isInt then { coeffs, sense := 'L', rhs := rhs - 1 }
                  else { coeffs, sense := 'L', rhs, relaxed := true }
  | .gt => return if c.isInt then { coeffs, sense := 'G', rhs := rhs + 1 }
                  else { coeffs, sense := 'G', rhs, relaxed := true }

/-- Read a hypothesis type as a row: a comparison, or the negation of one. -/
meta def rowOf (atoms : Array Atom) (ty : Expr) : Option LinRow :=
  match ty.getAppFnArgs with
  | (``LE.le, #[t, _, a, b]) => cmpRow atoms .le t a b
  | (``LT.lt, #[t, _, a, b]) => cmpRow atoms .lt t a b
  | (``GE.ge, #[t, _, a, b]) => cmpRow atoms .ge t a b
  | (``GT.gt, #[t, _, a, b]) => cmpRow atoms .gt t a b
  | (``Eq, #[t, a, b]) => cmpRow atoms .eq t a b
  | (``Not, #[p]) =>
      match p.getAppFnArgs with
      | (``LE.le, #[t, _, a, b]) => cmpRow atoms .gt t a b
      | (``LT.lt, #[t, _, a, b]) => cmpRow atoms .ge t a b
      | (``GE.ge, #[t, _, a, b]) => cmpRow atoms .lt t a b
      | (``GT.gt, #[t, _, a, b]) => cmpRow atoms .le t a b
      | _ => none
  | _ => none

/-! ## Building the problem

Rows with a single `±1` coefficient become variable *bounds*, which is what MPS wants; any
other row stays a row. A natural-number variable gets the lower bound `0`. Variables that
occur in no row are dropped, so they cost the solver nothing. -/

structure VarBounds where
  lo : Option ℚ := none
  hi : Option ℚ := none

meta def VarBounds.withLo (b : VarBounds) (l : ℚ) : VarBounds :=
  { b with lo := some (match b.lo with | none => l | some l' => max l l') }

meta def VarBounds.withHi (b : VarBounds) (u : ℚ) : VarBounds :=
  { b with hi := some (match b.hi with | none => u | some u' => min u u') }

/-- Split rows into bounds and constraint rows. -/
meta def classify (n : Nat) (rows : Array LinRow) : Array VarBounds × Array LinRow :=
  Id.run do
  let mut bounds : Array VarBounds := .replicate n {}
  let mut rest : Array LinRow := #[]
  for r in rows do
    match (r.coeffs.zipIdx.filter (fun p => p.1 != 0)).toList with
    | [(c, j)] =>
      if c == 1 then
        match r.sense with
        | 'L' => bounds := bounds.modify j (·.withHi r.rhs)
        | 'G' => bounds := bounds.modify j (·.withLo r.rhs)
        | _ => bounds := bounds.modify j (fun b => (b.withLo r.rhs).withHi r.rhs)
      else if c == -1 then
        match r.sense with
        | 'L' => bounds := bounds.modify j (·.withLo (-r.rhs))
        | 'G' => bounds := bounds.modify j (·.withHi (-r.rhs))
        | _ => bounds := bounds.modify j (fun b => (b.withLo (-r.rhs)).withHi (-r.rhs))
      else
        rest := rest.push r
    | _ => rest := rest.push r
  return (bounds, rest)

/-- An MPS-safe name for a variable: the user's own if it is a plain identifier and
unique, else positional. -/
meta def varNames (names : Array Name) : Array String :=
  let raw := names.map (·.toString)
  let ok := raw.all (fun s =>
    s.length > 0 && s.length ≤ 8 && s.all (fun c => c.isAlphanum || c == '_')) &&
    raw.toList.Nodup
  if ok then raw else raw.mapIdx (fun i _ => s!"v{i}")

/-- The `Mip` a list of read hypotheses stands for, over the atoms they and the objective
use. Returns the used atoms, in order, with the problem. Infeasibility passes no objective. -/
meta def buildMip (atoms : Array Atom) (rows : Array LinRow) (obj : Array ℚ := #[])
    (maximize : Bool := false) : Array Atom × Mip := Id.run do
  let occurs := (List.range atoms.size).filter
    (fun j => rows.any (fun r => r.coeffs.getD j 0 != 0) || obj.getD j 0 != 0)
  -- integer variables first: the bridge theorem takes their values as a `List ℤ`
  let isIntAt := fun j => (atoms[j]?.map (·.carrier.isInt)).getD false
  let used := occurs.filter isIntAt ++ occurs.filter (!isIntAt ·)
  let usedAtoms := used.toArray.filterMap (fun j => atoms[j]?)
  let rows := rows.map
    (fun r => { r with coeffs := used.toArray.map (fun j => r.coeffs.getD j 0) })
  let (bounds, rest) := classify usedAtoms.size rows
  -- Contradictory bounds (`lo > hi`) are left as rows: exact SCIP then declares the problem
  -- infeasible without deriving anything (scipopt/scip#305), while as rows it proves it.
  let conflict := bounds.any fun b => match b.lo, b.hi with
    | some l, some u => u < l
    | _, _ => false
  let (bounds, rest) := if conflict then (.replicate usedAtoms.size {}, rows) else (bounds, rest)
  let names := varNames (usedAtoms.map (·.name))
  let vars := usedAtoms.zipIdx.map fun (a, j) =>
    let b := bounds.getD j {}
    let b := if a.carrier.isNat then b.withLo 0 else b
    ({ name := names[j]!, isInt := a.carrier.isInt, lo := b.lo, hi := b.hi } : Mip.Var)
  let objForm := (used.zipIdx.filterMap fun (j, k) =>
    let c := obj.getD j 0
    if c != 0 then some (⟨k, c⟩ : LeanVIPR.Semantics.Term) else none)
  let mip : Mip :=
    { vars, objSense := if maximize then .max else .min, obj := objForm
      rows := rest.zipIdx.map (fun (r, i) =>
        { name := s!"r{i}", sense := r.sense, rhs := r.rhs,
          form := (r.coeffs.zipIdx.filter (fun p => p.1 != 0)).toList.map
            (fun (c, j) => ⟨j, c⟩) }) }
  return (usedAtoms, mip)

/-! ## Getting to `False`

`¬ P`, `a ≠ b` and `∀ x, … → False` become `False` by introduction; `∃` and `∧`
hypotheses are split; and a goal that is still not `False` — a comparison — is replaced by
`False` with its negation assumed. -/

/-- Introduce every binder, then split every `∃` and `∧` hypothesis. -/
meta partial def toFalse (goal : MVarId) : MetaM MVarId := do
  -- `¬ P` and `a ≠ b` are implications only after unfolding, and neither `whnfR` nor
  -- `intros` unfolds them: `Not` is a plain definition, not reducible.
  let goal ← goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    match ty.getAppFnArgs with
    | (``Not, #[p]) => goal.change (.forallE `h p (.const ``False []) .default)
    | (``Ne, #[_, a, b]) =>
        let eq ← mkEq a b
        goal.change (.forallE `h eq (.const ``False []) .default)
    | _ => pure goal
  let (introduced, goal) ← goal.intros
  if !introduced.isEmpty then
    return ← toFalse goal
  let hyps ← goal.withContext goal.getNondepPropHyps
  for d in hyps do
    let shaped ← goal.withContext do
      let t ← whnfR (← instantiateMVars (← d.getType))
      return t.isAppOf ``Exists || t.isAppOf ``And
    if shaped then
      let sub ← goal.cases d
      if let some s := sub[0]? then
        return ← toFalse s.mvarId
  return goal

/-- Make the goal `False`, assuming the negation of a goal that is a comparison. -/
meta def negateGoal (goal : MVarId) : MetaM MVarId := do
  let goal ← toFalse goal
  let ty ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  if ty.isConstOf ``False then return goal
  let [g] ← goal.apply (mkConst ``Classical.byContradiction)
    | throwError "internal: by contradiction did not leave one goal"
  let (_, g) ← g.intro `hmip
  toFalse g

/-! ## Case splits -/

/-- `a ≠ b` or `¬ a = b`, with the type. -/
meta def neq? (ty : Expr) : Option (Expr × Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Ne, #[t, a, b]) => some (t, a, b)
  | (``Not, #[p]) =>
      match p.getAppFnArgs with
      | (``Eq, #[t, a, b]) => some (t, a, b)
      | _ => none
  | _ => none

/-- Split one `∨` hypothesis, or one `≠` between numbers into `<` and `>`. `none` when there
is nothing to split. -/
meta def splitOnce? (goal : MVarId) : MetaM (Option (Array MVarId)) := goal.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Or then
      let subs ← goal.cases d.fvarId
      return some (subs.map (·.mvarId))
    if let some (t, _, _) := neq? ty then
      if (carrierOf? t).isSome then
        let orProof ← mkAppM ``lt_or_gt_of_ne #[.fvar d.fvarId]
        let g ← goal.assert `hmip_split (← inferType orProof) orProof
        let (orFv, g) ← g.intro1
        let g ← g.clear d.fvarId
        let subs ← g.cases orFv
        return some (subs.map (·.mvarId))
  return none

/-! ## Discharging the bridge's obligations -/

/-- The row obligation: one real (in)equality per row of `conSLes`, over the user's
variables cast to `ℝ`. Integer rows go back to `ℤ` for `omega`, which also knows the
tightening of strict comparisons; the others are lifted to `ℝ` with the hypotheses and
closed by `linarith`. -/
meta def rowScript : TacticM Unit := do
  evalTactic (← `(tactic|
    intro c hc <;>
    fin_cases hc <;>
      simp (config := { decide := true }) only [LeanVIPR.Semantics.System.satReal,
        LeanVIPR.Semantics.System.evalReal, List.map, List.sum_cons, List.sum_nil,
        LeanVIPR.Mip.valuationOfReals_cons_zero, LeanVIPR.Mip.valuationOfReals_cons_succ,
        LeanVIPR.Mip.valuationOfReals_cons_one, LeanVIPR.Mip.valuationOfReals_cons_ofNat,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        Array.size_push, Array.size_empty, ↓reduceIte, ite_true, ite_false] <;>
      first
        | (norm_cast; omega)
        | (push_cast; linarith)
        | (rify at *; (try push_cast at *); linarith)
        | (norm_num at *; linarith)))

/-! ## The tactic -/

/-- Close a linear-arithmetic goal over `ℕ`, `ℤ`, `ℚ` and `ℝ`, or a goal `m.Infeasible`
for a closed `m : Mip`, with an exact SCIP certificate checked in the kernel. Options:
`(timeout := n)` seconds, `(dir := "…")` to keep the `.mps` and `.vipr`, and
`(cert := "…")` to read the certificates `mip?` saved instead of running the solver. -/
syntax (name := mipTac) "mip" Lean.Parser.Tactic.optConfig : tactic

/-- `mip`, saving the certificates next to the Lean file and suggesting the
`mip (cert := "…")` call that reads them back, so the file then builds without SCIP. -/
syntax (name := mipTrace) "mip?" Lean.Parser.Tactic.optConfig : tactic

/-- A rational as a term that parses back unambiguously in any position. `ℚ`'s `Repr`
ignores precedence (`some (1/4)` prints as `some 1 / 4`), so the problem is printed here
rather than through `repr`. -/
meta def ratStx (q : ℚ) : TacticM Term := do
  let n := Syntax.mkNumLit (toString q.num.natAbs)
  let d := Syntax.mkNumLit (toString q.den)
  let base ← if q.den == 1 then `(($n : ℚ)) else `((($n : ℚ) / $d))
  if q.num < 0 then `((-$base)) else pure base

/-- A rational as a literal of type `T`. -/
meta def typedLit (q : ℚ) (T : Term) : TacticM Term := do
  let n := Syntax.mkNumLit (toString q.num.natAbs)
  let d := Syntax.mkNumLit (toString q.den)
  let base ← if q.den == 1 then `(($n : $T)) else `((($n : $T) / $d))
  if q.num < 0 then `((-$base)) else pure base

/-- The built `Mip` as a term. -/
meta def mipSyntax (m : Mip) : TacticM Term := do
  let optStx (o : Option ℚ) : TacticM Term := do
    match o with
    | none => `(none)
    | some q => do let t ← ratStx q; `(some $t)
  let vars ← m.vars.mapM fun v => do
    let lo ← optStx v.lo
    let hi ← optStx v.hi
    let nm := Syntax.mkStrLit v.name
    if v.isInt then `(({ name := $nm, isInt := true, lo := $lo, hi := $hi } : LeanVIPR.Mip.Var))
    else `(({ name := $nm, isInt := false, lo := $lo, hi := $hi } : LeanVIPR.Mip.Var))
  let rows ← m.rows.mapM fun r => do
    let terms ← r.form.toArray.mapM fun t => do
      let i := Syntax.mkNumLit (toString t.idx)
      let c ← ratStx t.coeff
      `(({ idx := $i, coeff := $c } : LeanVIPR.Semantics.Term))
    let nm := Syntax.mkStrLit r.name
    let sense := Syntax.mkCharLit r.sense
    let rhs ← ratStx r.rhs
    `(({ name := $nm, sense := $sense, rhs := $rhs, form := [$terms,*] } : LeanVIPR.Mip.Row))
  let obj ← m.obj.toArray.mapM fun t => do
    let i := Syntax.mkNumLit (toString t.idx)
    let c ← ratStx t.coeff
    `(({ idx := $i, coeff := $c } : LeanVIPR.Semantics.Term))
  let sense ← match m.objSense with
    | .max => `(LeanVIPR.Mip.ObjSense.max)
    | .min => `(LeanVIPR.Mip.ObjSense.min)
  `(({ vars := #[$vars,*], objSense := $sense, obj := [$obj,*], rows := #[$rows,*] } :
      LeanVIPR.Mip))

/-- What `mip` made of the context: the atoms, the rows, and which hypotheses it read and
which it could not. -/
structure Reading where
  atoms : Array Atom
  rows : Array LinRow
  used : Array Name
  ignored : Array Name

/-- Read the hypotheses into rows over the numeric variables in context. -/
meta def readContext : TacticM Reading := withMainContext do
  let decls := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  let mut atoms : Array Atom := decls.toArray.filterMap fun d =>
    (carrierOf? d.type).map (fun c => { expr := .fvar d.fvarId, name := d.userName, carrier := c })
  for d in decls do
    if ← isProp d.type then
      if let some (t, a, b) := cmpSides? (← instantiateMVars d.type) then
        if (carrierOf? t).isSome then
          atoms ← collectOpaque (← collectOpaque atoms a) b
  let mut rows := #[]
  let mut used := #[]
  let mut ignored := #[]
  for d in decls do
    if ← isProp d.type then
      match rowOf atoms (← instantiateMVars d.type) with
      | some r =>
          rows := rows.push r
          used := used.push d.userName
      | none => ignored := ignored.push d.userName
  return { atoms, rows, used, ignored }

/-- One sentence on what was read, for failure messages. -/
meta def Reading.describe (r : Reading) : MessageData :=
  let relaxed := r.rows.any (·.relaxed)
  m!"`mip` read {r.used.size} hypotheses {r.used.toList} over {r.atoms.size} variables" ++
  (if r.ignored.isEmpty then m!"" else m!", and ignored {r.ignored.toList}") ++
  (if relaxed then m!". Strict comparisons over ℚ or ℝ were read as non-strict, so a goal \
    that depends on strictness cannot be proved this way" else m!"") ++ m!"."

/-! ## Encodings: indicators and products with a binary

An indicator `δ = 1 → a ≤ b` and a product `δ * x` with `δ ∈ {0, 1}` are not linear, but
each implies linear facts once bounds are known: the big-M inequality `a - b ≤ M (1 - δ)`,
and McCormick's four inequalities around `δ * x`. Those facts are added as hypotheses,
each proved by splitting `δ = 0 ∨ δ = 1`, and then read like any other. So an encoding is
checked for the values at hand rather than trusted, and a fact whose proof fails is just
not added. The product itself is already an opaque variable of the problem. -/

/-- Bounds on each atom from the single-variable rows, rounded inward for integers. -/
meta def atomBounds (atoms : Array Atom) (rows : Array LinRow) : Array VarBounds := Id.run do
  let mut b : Array VarBounds := .replicate atoms.size {}
  for r in rows do
    match (r.coeffs.zipIdx.filter (fun p => p.1 != 0)).toList with
    | [(c, j)] =>
      let v := r.rhs / c
      let upper := (r.sense == 'L' && c > 0) || (r.sense == 'G' && c < 0)
      let lower := (r.sense == 'G' && c > 0) || (r.sense == 'L' && c < 0)
      if upper || r.sense == 'E' then b := b.modify j (·.withHi v)
      if lower || r.sense == 'E' then b := b.modify j (·.withLo v)
    | _ => pure ()
  return atoms.zipIdx.map fun (a, j) =>
    let bj := b.getD j {}
    let bj := if a.carrier.isNat then bj.withLo 0 else bj
    if a.carrier.isInt then
      { lo := bj.lo.map (fun q => (q.ceil : ℚ)), hi := bj.hi.map (fun q => (q.floor : ℚ)) }
    else bj

meta def isBinary (atoms : Array Atom) (bounds : Array VarBounds) (j : Nat) : Bool :=
  match atoms[j]?, bounds[j]? with
  | some a, some { lo := some l, hi := some u } => a.carrier.isInt && 0 ≤ l && u ≤ 1
  | _, _ => false

/-- The largest value of `coeffs · x + k` over the bounds, if every needed bound is known. -/
meta def boxMax (bounds : Array VarBounds) (coeffs : Array ℚ) (k : ℚ) : Option ℚ := do
  let mut total := k
  for (c, j) in coeffs.zipIdx do
    if c == 0 then continue
    let b := bounds.getD j {}
    let l ← b.lo
    let u ← b.hi
    total := total + max (c * l) (c * u)
  return total

/-- `δ = k` with `δ` a binary atom and `k` zero or one, either way round. -/
meta def indicatorPremise? (atoms : Array Atom) (bounds : Array VarBounds) (p : Expr) :
    Option (Nat × Bool) := do
  let (``Eq, #[_, l, r]) := p.getAppFnArgs | none
  let (i, k) ← match atomOf? atoms l, ratLit? r with
    | some i, some k => some (i, k)
    | _, _ => match atomOf? atoms r, ratLit? l with
      | some i, some k => some (i, k)
      | _, _ => none
  guard (isBinary atoms bounds i && (k == 0 || k == 1))
  return (i, k == 1)

/-- The `a ≤ b` pairs a comparison asserts. -/
meta def lePairs? (q : Expr) : Option (List (Expr × Expr)) :=
  match q.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) | (``LT.lt, #[_, _, a, b]) => some [(a, b)]
  | (``GE.ge, #[_, _, a, b]) | (``GT.gt, #[_, _, a, b]) => some [(b, a)]
  | (``Eq, #[_, a, b]) => some [(a, b), (b, a)]
  | _ => none

/-- Add the linear facts the indicators and binary products in context imply. `extra`
are terms outside the hypotheses — an objective — whose products should count too. -/
meta def addEncodings (extra : Array Expr := #[]) : TacticM Unit := withMainContext do
  let reading ← readContext
  let atoms ← extra.foldlM (init := reading.atoms) fun as e => collectOpaque as e
  let bounds := atomBounds atoms reading.rows
  let real ← `(ℝ)
  let mut facts : Array (Term × TSyntax `tactic) := #[]
  -- indicators: `h : δ = k → Q`
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isArrow && (← isProp ty) do continue
    let .forallE _ p q _ := ty | continue
    let some (i, one) := indicatorPremise? atoms bounds p | continue
    let some pairs := lePairs? q | continue
    let some δ := atoms[i]? | continue
    let δStx ← Term.exprToSyntax δ.expr
    let h ← Term.exprToSyntax (.fvar d.fvarId)
    for (a, b) in pairs do
      let some (ca, ka) := linearOf atoms a | continue
      let some (cb, kb) := linearOf atoms b | continue
      let some big := boxMax bounds (ca.zipWith (· - ·) cb) (ka - kb) | continue
      if big ≤ 0 then continue
      let aStx ← Term.exprToSyntax a
      let bStx ← Term.exprToSyntax b
      let m ← typedLit big real
      let ty ← if one then `((($aStx : ℝ)) - (($bStx : ℝ)) ≤ $m * (1 - (($δStx : ℝ))))
        else `((($aStx : ℝ)) - (($bStx : ℝ)) ≤ $m * (($δStx : ℝ)))
      let pf ← `(tactic|
        rcases (show $δStx = 0 ∨ $δStx = 1 by omega) with hδ | hδ <;>
          first
            | (have hq := $h (by omega); rw [hδ]; push_cast; (try rify at *);
                (try push_cast at *); linarith)
            | (rw [hδ]; push_cast; (try rify at *); (try push_cast at *); linarith))
      facts := facts.push (ty, pf)
  -- products with a binary: McCormick around `δ * x`
  for w in atoms do
    let (``HMul.hMul, #[_, _, _, _, f, g]) := w.expr.getAppFnArgs | continue
    let pick : Option (Nat × Expr) := match atomOf? atoms f, atomOf? atoms g with
      | some i, _ => if isBinary atoms bounds i then some (i, g) else
          match atomOf? atoms g with
          | some j => if isBinary atoms bounds j then some (j, f) else none
          | none => none
      | none, some j => if isBinary atoms bounds j then some (j, f) else none
      | none, none => none
    let some (i, x) := pick | continue
    let some xi := atomOf? atoms x | continue
    let some { lo := some l, hi := some u } := bounds[xi]? | continue
    let some δ := atoms[i]? | continue
    let δStx ← Term.exprToSyntax δ.expr
    let pStx ← Term.exprToSyntax w.expr
    let xStx ← Term.exprToSyntax x
    let lS ← typedLit l real
    let uS ← typedLit u real
    let tys ← [
      `((($pStx : ℝ)) ≤ $uS * (($δStx : ℝ))),
      `($lS * (($δStx : ℝ)) ≤ (($pStx : ℝ))),
      `((($pStx : ℝ)) ≤ (($xStx : ℝ)) - $lS * (1 - (($δStx : ℝ)))),
      `((($xStx : ℝ)) - $uS * (1 - (($δStx : ℝ))) ≤ (($pStx : ℝ)))].mapM id
    for ty in tys do
      let pf ← `(tactic|
        rcases (show $δStx = 0 ∨ $δStx = 1 by omega) with hδ | hδ <;>
          (rw [hδ]; push_cast; (try rify at *); (try push_cast at *);
            first | linarith | simp | (simp; linarith)))
      facts := facts.push (ty, pf)
  -- add each fact whose proof goes through
  for (ty, pf) in facts do
    let n := mkIdent (← mkFreshUserName `hmip_enc)
    let seq ← `(Lean.Parser.Tactic.tacticSeq| $pf:tactic)
    try evalTactic (← `(tactic| have $n : $ty := by $seq))
    catch _ => pure ()

/-! ## Disjunctions as binaries

`P ∨ Q`, for comparisons `P` and `Q`, becomes a fresh `δ : ℤ` with `0 ≤ δ ≤ 1`,
`δ = 0 → P` and `δ = 1 → Q`, obtained by cases on the disjunction; the indicator encoding
above then gives the big-M rows. So `k` disjunctions cost one solver call rather than
`2^k`. A strict comparison over `ℕ` or `ℤ` is restated as `a + 1 ≤ b` first, and `a ≠ b`
over `ℕ` or `ℤ` is read as `a < b ∨ a > b`, so neither loses its strength. A disjunction
with a side that has no finite big-M over the bounds in context is left to be split. -/

/-- The kind, type and sides of a comparison. -/
meta def cmpKind? (p : Expr) : Option (Cmp × Expr × Expr × Expr) :=
  match p.getAppFnArgs with
  | (``LE.le, #[t, _, a, b]) => some (.le, t, a, b)
  | (``LT.lt, #[t, _, a, b]) => some (.lt, t, a, b)
  | (``GE.ge, #[t, _, a, b]) => some (.ge, t, a, b)
  | (``GT.gt, #[t, _, a, b]) => some (.gt, t, a, b)
  | (``Eq, #[t, a, b]) => some (.eq, t, a, b)
  | _ => none

/-- One side of a disjunction, restated for an indicator: the statement, a tactic proving
it from the side itself (in context as `hside`), and the `a - b` forms it bounds above by
zero, each of which needs a finite big-M. -/
structure IndSide where
  stmt : Term
  proof : TSyntax `tactic
  forms : List (Array ℚ × ℚ)

meta def indSide? (atoms : Array Atom) (hside : Ident) (p : Expr) :
    TacticM (Option IndSide) := do
  let some (k, t, a, b) := cmpKind? p | return none
  let some c := carrierOf? t | return none
  let some (ca, ka) := linearOf atoms a | return none
  let some (cb, kb) := linearOf atoms b | return none
  let minus (x y : Array ℚ × ℚ) : Array ℚ × ℚ := (x.1.zipWith (· - ·) y.1, x.2 - y.2)
  let aS ← Term.exprToSyntax a
  let bS ← Term.exprToSyntax b
  let pS ← Term.exprToSyntax p
  let same ← `(tactic| exact $hside)
  let relax ← `(tactic| exact le_of_lt $hside)
  return some <| ← match k with
    | .le => pure ⟨pS, same, [minus (ca, ka) (cb, kb)]⟩
    | .ge => pure ⟨pS, same, [minus (cb, kb) (ca, ka)]⟩
    | .eq => pure ⟨pS, same, [minus (ca, ka) (cb, kb), minus (cb, kb) (ca, ka)]⟩
    | .lt => if c.isInt then do pure ⟨← `($aS + 1 ≤ $bS), ← `(tactic| omega),
                                        [minus (ca, ka + 1) (cb, kb)]⟩
             else do pure ⟨← `($aS ≤ $bS), relax, [minus (ca, ka) (cb, kb)]⟩
    | .gt => if c.isInt then do pure ⟨← `($bS + 1 ≤ $aS), ← `(tactic| omega),
                                        [minus (cb, kb + 1) (ca, ka)]⟩
             else do pure ⟨← `($bS ≤ $aS), relax, [minus (cb, kb) (ca, ka)]⟩

/-- Replace every `∨` of two comparisons, and every `≠` over `ℕ` or `ℤ`, by a binary, where
both sides have a finite big-M. -/
meta def encodeDisjunctions : TacticM Unit := withMainContext do
  let reading ← readContext
  let bounds := atomBounds reading.atoms reading.rows
  let finite (s : IndSide) := s.forms.all fun (c, k) => (boxMax bounds c k).isSome
  let hside := mkIdent (← mkFreshUserName `hside)
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let h ← Term.exprToSyntax (.fvar d.fvarId)
    -- the two sides, and the disjunction as a term
    let pair? : Option (Expr × Expr × Term) ← match ty.getAppFnArgs, neq? ty with
      | (``Or, #[p, q]), _ => pure (some (p, q, h))
      | _, some (t, a, b) =>
          if (carrierOf? t).any (·.isInt) then
            pure (some (← mkAppM ``LT.lt #[a, b], ← mkAppM ``GT.gt #[a, b],
              ← `(lt_or_gt_of_ne $h)))
          else pure none
      | _, _ => pure none
    let some (p, q, orStx) := pair? | continue
    let some sp ← indSide? reading.atoms hside p | continue
    let some sq ← indSide? reading.atoms hside q | continue
    unless finite sp && finite sq do continue
    let δ := mkIdent (← mkFreshUserName `δ)
    try
      evalTactic (← `(tactic|
        obtain ⟨$δ, _, _, _, _⟩ : ∃ δ : ℤ, 0 ≤ δ ∧ δ ≤ 1 ∧ (δ = 0 → $(sp.stmt)) ∧
            (δ = 1 → $(sq.stmt)) := by
          rcases $orStx:term with $hside:ident | $hside:ident
          · exact ⟨0, le_refl 0, zero_le_one, fun _ => by $(sp.proof):tactic,
              fun e => absurd e (by decide)⟩
          · exact ⟨1, zero_le_one, le_refl 1, fun e => absurd e (by decide),
              fun _ => by $(sq.proof):tactic⟩))
      replaceMainGoal [← (← getMainGoal).clear d.fvarId]
    catch _ => pure ()

/-- Solve one goal that is already `False` and has nothing left to split. -/
meta def solveLeaf (cfg : ScipConfig) : TacticM Unit := do
  addEncodings
  withMainContext do
  let reading ← readContext
  if reading.rows.isEmpty then
    throwError "`mip` could not read any hypothesis as a linear comparison. \
      {reading.describe}"
  let (atoms, m) := buildMip reading.atoms reading.rows
  let mStx ← mipSyntax m
  let zs ← (atoms.filter (·.carrier.isInt)).mapM fun a => do
    let x ← Term.exprToSyntax a.expr
    if a.carrier.isNat then `(($x : ℤ)) else pure x
  let rs ← (atoms.filter (!·.carrier.isInt)).mapM fun a => do
    let x ← Term.exprToSyntax a.expr
    match a.carrier with
    | .real => pure x
    | _ => `(($x : ℝ))
  let n := Syntax.mkNumLit (toString zs.size)
  evalTactic (← `(tactic|
    refine LeanVIPR.Mip.absurd_of_infeasible_mixed (m := $mStx) ?_ $n ?_ [$zs,*] rfl
      [$rs,*] ?_))
  -- identify the goals by type, not by position or tag
  let mut infGoal? := none
  let mut hintGoal? := none
  let mut rowsGoal? := none
  for g in ← getUnsolvedGoals do
    let ty ← instantiateMVars (← g.getType)
    if (infeasibleGoal? ty).isSome then infGoal? := some g
    else if ty.getUsedConstants.contains ``LeanVIPR.Semantics.System.satReal then
      rowsGoal? := some g
    else hintGoal? := some g
  let some infGoal := infGoal? | throwError "internal: no infeasibility goal after refine"
  let some hintGoal := hintGoal? | throwError "internal: no integrality goal after refine"
  let some rowsGoal := rowsGoal? | throwError "internal: no row goal after refine"
  -- integrality: a fact about the problem alone, so `decide` settles it
  setGoals [hintGoal]
  evalTactic (← `(tactic| decide))
  -- the solver half, kernel-checked
  setGoals [infGoal]
  try certifyMainGoal cfg
  catch e => throwError "{e.toMessageData}\n{reading.describe}"
  -- the arithmetic half, against the user's own hypotheses
  setGoals [rowsGoal]
  rowScript
  unless (← getUnsolvedGoals).isEmpty do
    throwError "the problem was certified infeasible, but its rows could not be matched \
      back to your hypotheses — an unsupported hypothesis shape, or a reflection bug. \
      The problem solved was:{indentD (repr m).pretty}"
  setGoals []

/-- At most this many cases are split before `mip` gives up: every `∨` and `≠` doubles
the number of problems sent to the solver. -/
meta def maxLeaves : Nat := 64

/-- How many hypotheses `splitOnce?` would split. Each one left doubles the cases. -/
meta def splittable (goal : MVarId) : MetaM Nat := goal.withContext do
  let mut k := 0
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Or then k := k + 1
    else if let some (t, _, _) := neq? ty then
      if (carrierOf? t).isSome then k := k + 1
  return k

/-- Close the main goal: make it `False`, split cases, and solve each leaf. -/
meta partial def solveGoal (cfg : ScipConfig) (leaves : IO.Ref Nat) : TacticM Unit := do
  setGoals [← negateGoal (← getMainGoal)]
  if cfg.encodeDisjunctions then encodeDisjunctions
  let g ← getMainGoal
  -- fail before solving any case, not after the first `maxLeaves`
  let k ← splittable g
  let tooMany (n : Nat) : MessageData :=
    m!"`mip` would need {n} cases, more than {maxLeaves}, to split the `∨` and `≠` in the \
      context that it does not encode with a binary: those with a side that has no finite \
      bound over the bounds in context, or all of them under `-encodeDisjunctions`"
  if (← leaves.get) - 1 + 2 ^ k > maxLeaves then throwError (tooMany (2 ^ k))
  match ← splitOnce? g with
  | some subs =>
      leaves.modify (· + subs.size - 1)
      if (← leaves.get) > maxLeaves then throwError (tooMany (← leaves.get))
      for s in subs do
        setGoals [s]
        solveGoal cfg leaves
        let left ← getUnsolvedGoals
        unless left.isEmpty do
          throwError "internal: a case split left {left.length} goals open"
  | none =>
      setGoals [g]
      solveLeaf cfg

/-- Close the main goal by asking exact SCIP, or the saved certificates, for an
infeasibility certificate and checking it in the kernel. A goal that is already
`m.Infeasible` goes to the certify step directly. -/
meta def runMipOn (cfg : ScipConfig) : TacticM Unit := do
  let leaves ← IO.mkRef 1
  match ← getGoals with
  | [] => throwError "no goals"
  | g :: rest =>
      setGoals [g]
      if (infeasibleGoal? (← instantiateMVars (← g.getType))).isSome then
        certifyMainGoal cfg
      else
        solveGoal cfg leaves
      let left ← getUnsolvedGoals
      unless left.isEmpty do
        throwError "internal: `mip` left {left.length} goals open"
      setGoals rest

/-- **The tactic.** -/
@[tactic mipTac]
meta def evalMipTac : Tactic := fun stx => do
  runMipOn (← (← elabMipConfig stx[1]).resolve)

@[tactic mipTrace]
meta def evalMipTrace : Tactic := fun stx => do
  let file ← savedFileName
  let (cfg, r) ← (← elabMipConfig stx[1]).recording
  runMipOn cfg
  saveRecorded r file
  -- `cert` as a plain identifier: quoted, hygiene would print it `cert✝`
  let sugg ← `(tactic| mip ($(mkIdent `cert):ident := $(quote file)))
  Meta.Tactic.TryThis.addSuggestion stx[0] sugg (origSpan? := stx)

end LeanVIPR.Tactic
