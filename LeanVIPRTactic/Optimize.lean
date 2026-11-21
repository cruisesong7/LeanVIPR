module

public meta import LeanVIPRTactic.Reflect

@[expose] public section

/-!
# `mip_maximize`, `mip_minimize`: a certified bound on an objective

Stage 6 of `docs/TACTIC-TODO.md`. `mip_maximize e` reads the hypotheses as `mip` does,
asks exact SCIP to maximize `e` subject to them, checks the returned `RTP range`
certificate in the kernel, and adds `hbound : e ≤ N` with `N` the certified maximum.
`mip_minimize e` adds `hbound : N ≤ e`. `mip_maximize h : e` names the hypothesis `h`.

```lean
example (x y : ℤ) (h1 : x + y ≤ 4) (h2 : x - y ≤ 1) (h3 : 0 ≤ y) : 2*x + y ≤ 7 := by
  mip_maximize 2*x + y
  exact hbound
```

The bound is what the certificate's *dual* side proves — it holds at every point
satisfying the hypotheses, which is why a `range` certificate rather than an
infeasibility one is needed: for a rational objective, `e > N` cannot be refuted, since
it relaxes to `e ≥ N`, which the optimum satisfies. For an integer-valued objective the
bound is rounded to the nearest integer that still holds.

If the hypotheses are inconsistent, the goal is closed outright, as `lp`'s `maximize`
does. If SCIP finds no finite bound, the tactic fails and says so.

Nothing here is trusted beyond what `mip` trusts: `pipeline_upper_bound_of_min` and
`pipeline_lower_bound` carry the certificate to the `Mip`, and the rows are proved back
from the hypotheses in context.
-/

namespace LeanVIPR.Tactic

open Lean Elab Tactic Meta
open LeanVIPR LeanVIPR.Parser

syntax (name := mipMaximizeTac) "mip_maximize"
  (atomic(" (" &"dir" " := " str ")"))? (atomic(" (" &"timeout" " := " num ")"))?
  (atomic(ppSpace ident " : "))? term : tactic

syntax (name := mipMinimizeTac) "mip_minimize"
  (atomic(" (" &"dir" " := " str ")"))? (atomic(" (" &"timeout" " := " num ")"))?
  (atomic(ppSpace ident " : "))? term : tactic

/-- A rational as a literal of type `T`. -/
meta def boundStx (q : ℚ) (T : Term) : TacticM Term := do
  let n := Syntax.mkNumLit (toString q.num.natAbs)
  let d := Syntax.mkNumLit (toString q.den)
  let base ← if q.den == 1 then `(($n : $T)) else `((($n : $T) / $d))
  if q.num < 0 then `((-$base)) else pure base

/-- Turn the certificate's bound into one on `e`, in `e`'s own type. Rounded inward for an
integer-valued objective, where that is still a valid bound. -/
meta def userBound (maximize : Bool) (carrier : Carrier) (q : ℚ) : ℚ :=
  if carrier.isInt then
    let k : ℚ := if maximize then (q.floor : ℚ) else (q.ceil : ℚ)
    if carrier.isNat && k < 0 then 0 else k
  else q

/-- Close `e ≤ N` (or `N ≤ e`) from `hR`, the certificate's bound on the objective over the
user's values cast to `ℝ`. Over a field the two are the same inequality; over `ℕ` or `ℤ`
the bound was rounded, so the step back is `x < k → x + 1 ≤ k` before lifting. -/
meta def closeBound : TacticM Unit := do
  evalTactic (← `(tactic|
    first
      | (push_cast at hR ⊢; linarith)
      | (rify; push_cast at hR ⊢; linarith)
      | (by_contra hc; push_neg at hc; have hc' := Int.add_one_le_iff.mpr hc
         rify at hc'; push_cast at hR hc'; linarith)
      | (by_contra hc; push_neg at hc; have hc' := Nat.succ_le_of_lt hc
         rify at hc'; push_cast at hR hc'; linarith)
      | omega))

meta def evalOptimize (maximize : Bool) : Tactic := fun stx => withMainContext do
  let name := if maximize then "mip_maximize" else "mip_minimize"
  let cfg := scipConfigOf stx[1] stx[2]
  let hName : Name := if stx[3].isNone then `hbound else stx[3][0].getId
  let eStx : Term := ⟨stx[4]⟩
  let e ← instantiateMVars (← Term.elabTermAndSynthesize eStx none)
  let T ← instantiateMVars (← inferType e)
  let some carrier := carrierOf? T
    | throwError "`{name}` needs an objective of type ℕ, ℤ, ℚ or ℝ, not{indentExpr T}"
  let reading ← readContext
  let reading := { reading with atoms := ← collectOpaque reading.atoms e }
  let some (oc, ok) := linearOf reading.atoms e
    | throwError "`{name}`: the objective is not linear in the variables in context:\
        {indentExpr e}"
  let (atoms, m) := buildMip reading.atoms reading.rows oc maximize
  let r ← runScipForGoal m cfg
  -- inconsistent hypotheses: nothing to bound, so close the goal outright
  if let .infeas := r.cert.rtp then
    if r.provesInfeasible then
      evalTactic (← `(tactic| exfalso))
      solveLeaf cfg
      return
  -- SCIP minimizes: its lower bound bounds our objective from below, or its negation
  -- from above when maximizing
  let candidate? : Option ℚ := match r.cert.rtp with
    | .range (some lower) _ => some (if maximize then -lower else lower)
    | _ => none
  let why? : Option MessageData :=
    if !r.agrees then some m!"the certificate is not about this problem (`agreesWith`)"
    else if !r.accepted then some m!"the certificate does not check out (`checkVipr`)"
    else if r.cert.objSense != "min" then some m!"the certificate's objective sense is not `min`"
    else if maximize && !r.objAgreesNeg then some m!"the certificate's objective is not ours negated"
    else if !maximize && !r.objAgrees then some m!"the certificate's objective is not ours"
    else if candidate?.isNone then
      some m!"the certificate proves no finite bound, so the objective may be unbounded"
    else none
  let Tstx ← Term.exprToSyntax T
  if let some why := why? then
    -- An integer-valued objective has a second route: take SCIP's optimum as an untrusted
    -- guess and prove the bound with `mip`, refuting `e ≥ N + 1` (exact over ℕ and ℤ).
    -- This is what rescues certificates without an objective-bound row (scipopt/scip#305).
    if let some fb := candidate? then
      if carrier.isInt then
        let bStx ← boundStx (userBound maximize carrier (fb + ok)) Tstx
        let tyStx ← if maximize then `($eStx ≤ $bStx) else `($bStx ≤ $eStx)
        try
          evalTactic (← `(tactic| have $(mkIdent hName) : $tyStx := by mip))
          return
        catch _ => pure ()
    throwError "`{name}` could not certify a bound: {why}\n{r.summary}\n{reading.describe}"
  let some formBound := candidate? | throwError "internal: no bound"
  let thm := if maximize then ``LeanVIPR.Mip.pipeline_upper_bound_of_min
    else ``LeanVIPR.Mip.pipeline_lower_bound
  let bound := userBound maximize carrier (formBound + ok)
  -- the hypothesis to add, in the objective's own type
  let bStx ← boundStx bound Tstx
  let tyStx ← if maximize then `($eStx ≤ $bStx) else `($bStx ≤ $eStx)
  let boundTy ← instantiateMVars (← Term.elabTermAndSynthesize tyStx (some (mkSort .zero)))
  let pf ← mkFreshExprSyntheticOpaqueMVar boundTy
  let (_, main) ← (← (← getMainGoal).assert hName boundTy pf).intro1P
  -- prove it: the certificate's bound, at the user's values
  let mStx ← mipSyntax m
  let cert ← certSyntax r.cert
  let zs ← (atoms.filter (·.carrier.isInt)).mapM fun a => do
    let x ← Term.exprToSyntax a.expr
    if a.carrier.isNat then `(($x : ℤ)) else pure x
  let rs ← (atoms.filter (!·.carrier.isInt)).mapM fun a => do
    let x ← Term.exprToSyntax a.expr
    match a.carrier with
    | .real => pure x
    | _ => `(($x : ℝ))
  let n := Syntax.mkNumLit (toString zs.size)
  let thmId := mkIdent thm
  setGoals [pf.mvarId!]
  evalTactic (← `(tactic|
    have hR := $thmId (m := $mStx) (v := $cert) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl rfl rfl _
      (LeanVIPR.Mip.feasible_mixed $n (by decide) [$zs,*] rfl [$rs,*] ?_)))
  let mut boundGoal? := none
  let mut rowsGoal? := none
  for g in ← getUnsolvedGoals do
    if (← instantiateMVars (← g.getType)).getUsedConstants.contains
        ``LeanVIPR.Semantics.System.satReal then rowsGoal? := some g
    else boundGoal? := some g
  let some rowsGoal := rowsGoal? | throwError "internal: no row goal"
  let some boundGoal := boundGoal? | throwError "internal: no bound goal"
  setGoals [rowsGoal]
  rowScript
  setGoals [boundGoal]
  evalTactic (← `(tactic|
    simp only [LeanVIPR.Mip.objectiveReal, LeanVIPR.Semantics.System.evalReal, List.map,
      List.sum_cons, List.sum_nil, LeanVIPR.Mip.valuationOfReals_cons_zero,
      LeanVIPR.Mip.valuationOfReals_cons_succ, LeanVIPR.Mip.valuationOfReals_cons_one,
      LeanVIPR.Mip.valuationOfReals_cons_ofNat, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append] at hR))
  closeBound
  unless (← getUnsolvedGoals).isEmpty do
    throwError "internal: the certified bound could not be restated in the objective's terms"
  setGoals [main]

@[tactic mipMaximizeTac] meta def evalMipMaximize : Tactic := evalOptimize true
@[tactic mipMinimizeTac] meta def evalMipMinimize : Tactic := evalOptimize false

end LeanVIPR.Tactic
