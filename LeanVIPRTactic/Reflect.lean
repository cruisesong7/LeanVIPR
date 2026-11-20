module

public meta import LeanVIPRTactic.Certify
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `mip`: close a `Prop` about integers with a solver certificate

Stages 4 and 5 of `docs/TACTIC-TODO.md`. The goal shapes are catalogued, with a proof of
each, in `examples/mip_prop_goals.lean`.

```
⊢ ¬ ∃ x y z : ℤ, 0 ≤ x ∧ … ∧ 6*x + 10*y + 15*z = 23
  │ intro, destructure                       (metacode)
  │ read each hypothesis as a linear row     (metacode, untrusted)
  ▼
m : Mip  ─ mip_certify ─▶  m.Infeasible      (kernel-checked)
  │ Mip.absurd_of_infeasible
  ▼ False
```

**Why none of this needs trusting.** The reflector builds a `Mip` and *claims* it is the
user's problem. That claim is never assumed: `Mip.absurd_of_infeasible` demands a proof
that the integer tuple satisfies every row of `m.conSLes`, which is discharged against the
hypotheses actually in context. A misread hypothesis gives a `Mip` whose rows cannot be
proved, and the tactic fails. The only thing it can cost is a failure — the same contract
the solver has.

Supported today: hypotheses that are linear relations over the bound integer variables
with integer literal coefficients. Rational-coefficient goals stated over `ℝ` are
`mip_certify` plus a hand-written bridge for now; see `examples/mip_prop_goals.lean` §2.
-/

namespace LeanVIPR.Tactic

open Lean Elab Tactic Meta
open LeanVIPR LeanVIPR.Parser

/-! ## Reading an integer linear expression

A hand-rolled reader rather than `linear_combination`-style machinery, because what is
needed is tiny — literals, `+`, `-`, unary minus, and multiplication by a literal — and a
reader that silently accepts more than the `Mip` can express would turn a clear failure
into a confusing one. -/

/-- An integer literal, including negated and `OfNat` forms. -/
meta partial def intLit? (e : Expr) : Option Int :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?.map Int.ofNat
  | (``Neg.neg, #[_, _, a]) => (intLit? a).map (- ·)
  | (``Int.negOfNat, #[n]) => n.rawNatLit?.map (fun k => -Int.ofNat k)
  | (``Int.ofNat, #[n]) => n.rawNatLit?.map Int.ofNat
  | _ => e.rawNatLit?.map Int.ofNat

/-- The linear form of `e` over `vars`, as coefficients and a constant, or `none` if `e`
is not linear in them. -/
meta partial def linearOf (vars : Array FVarId) (e : Expr) :
    Option (Array Int × Int) := do
  let zero := vars.map (fun _ => (0 : Int))
  if let some n := intLit? e then
    return (zero, n)
  match e with
  | .fvar fv =>
      let some i := vars.idxOf? fv | none
      return (zero.set! i 1, 0)
  | _ =>
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
        let (ca, ka) ← linearOf vars a
        let (cb, kb) ← linearOf vars b
        return (ca.zipWith (· + ·) cb, ka + kb)
    | (``HSub.hSub, #[_, _, _, _, a, b]) => do
        let (ca, ka) ← linearOf vars a
        let (cb, kb) ← linearOf vars b
        return (ca.zipWith (· - ·) cb, ka - kb)
    | (``Neg.neg, #[_, _, a]) => do
        let (ca, ka) ← linearOf vars a
        return (ca.map (- ·), -ka)
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
        if let some n := intLit? a then do
          let (cb, kb) ← linearOf vars b
          return (cb.map (n * ·), n * kb)
        else if let some n := intLit? b then do
          let (ca, ka) ← linearOf vars a
          return (ca.map (· * n), ka * n)
        else none
    | _ => none

/-- A hypothesis read as `coeffs · x  sense  rhs`, with `sense` one of `'L'`, `'G'`,
`'E'`. Strict inequalities over `ℤ` are tightened by one, which is why they can become
bounds rather than rows. -/
structure IntRow where
  coeffs : Array Int
  sense : Char
  rhs : Int

/-- Read a hypothesis type as a row. `≤`, `<`, `≥`, `>` and `=` over `ℤ`, with the
variables on either side. -/
meta def rowOf (vars : Array FVarId) (ty : Expr) : Option IntRow := do
  let intTy := Expr.const ``Int []
  let side (a b : Expr) : Option (Array Int × Int) := do
    let (ca, ka) ← linearOf vars a
    let (cb, kb) ← linearOf vars b
    return (ca.zipWith (· - ·) cb, kb - ka)
  match ty.getAppFnArgs with
  | (``LE.le, #[t, _, a, b]) =>
      if t != intTy then none else do
        let (c, k) ← side a b; return ⟨c, 'L', k⟩
  | (``LT.lt, #[t, _, a, b]) =>
      if t != intTy then none else do
        let (c, k) ← side a b; return ⟨c, 'L', k - 1⟩
  | (``GE.ge, #[t, _, a, b]) =>
      if t != intTy then none else do
        let (c, k) ← side a b; return ⟨c, 'G', k⟩
  | (``GT.gt, #[t, _, a, b]) =>
      if t != intTy then none else do
        let (c, k) ← side a b; return ⟨c, 'G', k + 1⟩
  | (``Eq, #[t, a, b]) =>
      if t != intTy then none else do
        let (c, k) ← side a b; return ⟨c, 'E', k⟩
  | _ => none

/-! ## Building the problem

Rows with a single `±1` coefficient become variable *bounds* rather than constraint rows,
which is both what MPS wants and what keeps the emitted file close to what a person would
write. Anything else — including `2*x ≤ 5` — stays a row: dividing it out would be sound
but would put a non-integer bound on an integer variable for no gain. -/

/-- A variable's accumulated bounds. -/
structure VarBounds where
  lo : Option Int := none
  hi : Option Int := none

meta def VarBounds.withLo (b : VarBounds) (l : Int) : VarBounds :=
  { b with lo := some (match b.lo with | none => l | some l' => max l l') }

meta def VarBounds.withHi (b : VarBounds) (u : Int) : VarBounds :=
  { b with hi := some (match b.hi with | none => u | some u' => min u u') }

/-- Split rows into bounds and constraint rows. -/
meta def classify (n : Nat) (rows : Array IntRow) :
    Array VarBounds × Array IntRow := Id.run do
  let mut bounds : Array VarBounds := .replicate n {}
  let mut rest : Array IntRow := #[]
  for r in rows do
    let nz := (r.coeffs.zipIdx.filter (fun p => p.1 != 0))
    match nz.toList with
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
unique, else positional. Names only have to be tokens a reader gives back, and
`Mip.WellFormed` additionally wants them distinct. -/
meta def varNames (vars : Array (FVarId × Name)) : Array String :=
  let raw := vars.map (fun p => p.2.toString)
  let ok := raw.all (fun s =>
    s.length > 0 && s.length ≤ 8 && s.all (fun c => c.isAlphanum || c == '_')) &&
    raw.toList.Nodup
  if ok then raw else raw.mapIdx (fun i _ => s!"v{i}")

/-- The `Mip` a list of read hypotheses stands for: every variable integral, bounds
folded in, everything else a row, and no objective — infeasibility does not use one. -/
meta def buildMip (names : Array String) (rows : Array IntRow) : Mip :=
  let (bounds, rest) := classify names.size rows
  { vars := names.zipIdx.map (fun (nm, j) =>
      { name := nm, isInt := true,
        lo := (bounds.getD j {}).lo.map (fun k => (k : ℚ)),
        hi := (bounds.getD j {}).hi.map (fun k => (k : ℚ)) })
    objSense := .min
    obj := []
    rows := rest.zipIdx.map (fun (r, i) =>
      { name := s!"r{i}", sense := r.sense, rhs := (r.rhs : ℚ),
        form := (r.coeffs.zipIdx.filter (fun p => p.1 != 0)).toList.map
          (fun (c, j) => ⟨j, (c : ℚ)⟩) }) }

/-! ## The tactic -/

/-- Reduce the goal to `False` with the user's data in context: introduce every binder,
then split every `∃` and `∧` hypothesis. This is `rintro ⟨…⟩` done in `MetaM`, so the
arity does not have to be guessed. -/
meta partial def toFalse (goal : MVarId) : MetaM MVarId := do
  -- `¬ P` and `a ≠ b` are implications only after unfolding, and neither `whnfR` nor
  -- `intros` unfolds them: `Not` is a plain definition, not reducible.
  let goal ← goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    match ty.getAppFnArgs with
    | (``Not, #[p]) => goal.change (.forallE `h p (.const ``False []) .default)
    | (``Ne, #[t, a, b]) =>
        let eq ← mkEq a b
        let _ := t
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

/-- The row obligation `Mip.absurd_of_infeasible` leaves: one real (in)equality per row of
`conSLes`, with the hypotheses in context. `fin_cases` enumerates the rows — `conSLes`
computes — and the alternatives cover the integer case (`norm_cast` back to `ℤ`, then
`omega`) and the rational-coefficient one (stay in `ℝ` and use `linarith`). -/
meta def rowScript : TacticM Unit := do
  evalTactic (← `(tactic|
    intro c hc <;>
    fin_cases hc <;>
      simp only [LeanVIPR.Semantics.System.satReal, LeanVIPR.Semantics.System.evalReal,
        List.map, List.sum_cons, List.sum_nil,
        LeanVIPR.Mip.valuationOfInts_cons_zero,
        LeanVIPR.Mip.valuationOfInts_cons_succ] <;>
      first
        | (norm_cast; omega)
        | (push_cast; linarith)
        | (norm_num; linarith)))

syntax (name := mipTac) "mip"
  (" (" &"dir" " := " str ")")? (" (" &"timeout" " := " num ")")? : tactic

/-- The built `Mip` as a term. Uses the derived `Repr`, which round-trips for the same
reason the certificate's does. -/
meta def mipSyntax (m : Mip) : TacticM Term := do
  match Parser.runParserCategory (← getEnv) `term (repr m).pretty "<mip>" with
  | .error err => throwError "internal: could not print the reflected problem\n{err}"
  | .ok stx => return ⟨stx⟩

/-- Read the goal and its hypotheses into a problem: the integer variables in the order
they were introduced, every hypothesis that parses as a linear relation over them. -/
meta def reflectGoal : TacticM (Array FVarId × Mip) := withMainContext do
  let goal ← getMainGoal
  unless (← whnfR (← goal.getType)).isConstOf ``False do
    throwError "`mip` expects a goal that reduces to `False` once the binders are \
      introduced — `¬ ∃ x … : ℤ, …`, `∀ x … : ℤ, … → False`, or `… ≠ …`.\n\
      Goal:{indentExpr (← goal.getType)}"
  let decls := (← getLCtx).decls.toList.filterMap id
  let intVars := decls.filterMap (fun d =>
    if d.type.isConstOf ``Int && !d.isImplementationDetail then
      some (d.fvarId, d.userName) else none)
  if intVars.isEmpty then
    throwError "`mip` found no integer variables to build a problem from"
  let fvars := (intVars.map Prod.fst).toArray
  let mut rows : Array IntRow := #[]
  for d in decls do
    unless d.isImplementationDetail do
      if ← isProp d.type then
        if let some r := rowOf fvars (← instantiateMVars d.type) then
          rows := rows.push r
  if rows.isEmpty then
    throwError "`mip` could not read any hypothesis as a linear relation over the \
      {fvars.size} integer variables in context"
  return (fvars, buildMip (varNames intVars.toArray) rows)

/-- **The bundled tactic.** Reflect the goal into a `Mip`, certify its infeasibility with
exact SCIP, and close the goal. -/
@[tactic mipTac]
meta def evalMipTac : Tactic := fun stx => withMainContext do
  let cfg := scipConfigOf stx[1] stx[2]
  replaceMainGoal [← toFalse (← getMainGoal)]
  let (fvars, m) ← reflectGoal
  withMainContext do
    let mStx ← mipSyntax m
    let xs ← fvars.mapM (fun fv => Term.exprToSyntax (.fvar fv))
    evalTactic (← `(tactic|
      refine LeanVIPR.Mip.absurd_of_infeasible (m := $mStx) ?inf [$xs,*] ?rows))
    -- `?inf` and `?rows` come back in order, but identify them by type rather than by
    -- position or tag: one is an infeasibility claim, the other the row obligation.
    let gs ← getUnsolvedGoals
    let mut infGoal? : Option MVarId := none
    let mut rowsGoal? : Option MVarId := none
    for g in gs do
      if (infeasibleGoal? (← instantiateMVars (← g.getType))).isSome then
        infGoal? := some g
      else
        rowsGoal? := some g
    let some infGoal := infGoal? | throwError "internal: no infeasibility goal after refine"
    let some rowsGoal := rowsGoal? | throwError "internal: no row goal after refine"
    -- the solver half, kernel-checked
    setGoals [infGoal]
    certifyMainGoal cfg
    -- the arithmetic half, against the user's own hypotheses
    setGoals [rowsGoal]
    rowScript
    let remaining ← getUnsolvedGoals
    unless remaining.isEmpty do
      throwError "the problem was certified infeasible, but its rows could not be matched \
        back to your hypotheses — an unsupported hypothesis shape, or a reflection bug. \
        The problem solved was:{indentD (repr m).pretty}"
    setGoals []

end LeanVIPR.Tactic
