module

public meta import LeanVIPRTactic.Eval
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

/-!
# Closing a `Mip.Infeasible` goal with a solver certificate

Stage 3 of `docs/TACTIC-TODO.md`: what `mip` does on a goal `m.Infeasible` for a closed
`m`, and on every problem it builds from a goal of its own. It runs exact SCIP, elaborates
the returned certificate as a literal, and applies `Mip.pipeline_infeasible` with its two
`Bool` hypotheses decided by the **kernel**.

What enters the proof term is the certificate and two `decide +kernel` checks of it. What
does not: the emitter, the file, the solver, the parser, and the renaming guess. Each can
make this step fail; none can make it close a goal that is false.

```
⊢ m.Infeasible
  │ evaluate the goal's `m`          (compiled code, elaboration time, no axiom)
  │ encodeMps → SCIP → parse          (untrusted transport)
  │ agreesWith m v, checkVipr v       (decided by the kernel — this is the proof)
  ▼ Mip.pipeline_infeasible
```

The untrusted compiled check runs first, inside `runScip`, so a certificate that will not
check out is reported in a readable message rather than as minutes of kernel reduction.

Under `+native` the two `Bool`s are decided by `decide +native` instead: compiled code,
much faster on a large certificate, at the cost of trusting the compiler. Each such check
adds an axiom of its own to the proof (`thm._native.decide.ax_…`), asserting what the
compiled code computed, as `native_decide` does.
-/

namespace LeanVIPR.Tactic

open Lean Elab Tactic Meta
open LeanVIPR LeanVIPR.Parser

/-- The `Mip` a goal `Mip.Infeasible m` is about, or `none`. -/
meta def infeasibleGoal? (ty : Expr) : Option Expr :=
  match ty.getAppFnArgs with
  | (``LeanVIPR.Mip.Infeasible, #[m]) => some m
  | _ => none

/-- The first solution in a certificate, as `name = value` over its nonzero entries. SCIP
prefixes transformed variables with `t_`, which is dropped. Untrusted: this only feeds a
message. -/
meta def solutionText? (v : Vipr) : Option String := do
  let (_, entries) ← v.sols[0]?
  let shown := entries.map fun (j, q) =>
    let nm := v.varNames[j]?.getD s!"x{j}"
    s!"{if nm.startsWith "t_" then nm.drop 2 else nm} = {q}"
  return if shown.isEmpty then "every variable 0"
    else ", ".intercalate shown ++ ", every other variable 0"

/-- Report a run that cannot discharge infeasibility, saying which of the three
hypotheses failed. A `range` answer is called out separately: the solver found the problem
*feasible*, and its solution is shown as a counterexample. -/
meta def throwUnusableRun {α : Type} (r : ScipRun) : MetaM α := do
  if r.cert.rtp != .infeas then
    let cex := match solutionText? r.cert with
      | some s => m!" A solution: {s}."
      | none => m!""
    throwError "exact SCIP found the problem feasible (`RTP {rtpSummary r.cert.rtp}`), so it \
      has no infeasibility certificate.{cex} Either the goal is false, or it depends on \
      something that was not read into the problem.\n{r.summary}"
  else if !r.agrees then
    throwError "the certificate exact SCIP returned is not about this problem: \
      `agreesWith` rejected it. Compare `m.conSLes` against the certificate's `CON` \
      section; `#mip_scip (dir := \"…\") m` keeps both files.\n{r.summary}"
  else
    throwError "the certificate exact SCIP returned does not check out: `checkVipr` \
      rejected it.\n{r.summary}"

/-- How a certificate's checks are decided: by the kernel, or under `+native` by compiled
code. -/
meta def checkTactic (cfg : ScipConfig) : TacticM (TSyntax `tactic) :=
  -- the certificate is a deeply nested literal, past the default recursion depth
  if cfg.native then `(tactic| set_option maxRecDepth 100000 in decide +native)
  else `(tactic| set_option maxRecDepth 100000 in decide +kernel)

/-- Past this many derivations, the kernel check can take minutes. -/
meta def largeCertificate : Nat := 1000

/-- Say how to avoid a long kernel check, before it starts: the kernel gives no progress
report, so otherwise the editor just waits. -/
meta def adviseNative (cfg : ScipConfig) (v : Vipr) : MetaM Unit := do
  if !cfg.native && v.ders.size > largeCertificate then
    logInfo m!"the certificate has {v.ders.size} derivations, which the kernel may take \
      minutes to check; `+native` checks them with compiled code instead"

/-- The certify step. Closes the main goal, which must be `m.Infeasible`. -/
meta def certifyMainGoal (cfg : ScipConfig := {}) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some mExpr := infeasibleGoal? ty
    | throwError "internal: expected a goal of the form `m.Infeasible`, not{indentExpr ty}"
  let m ← evalMipExpr mExpr
  let r ← runScipForGoal m cfg
  unless r.provesInfeasible do throwUnusableRun r
  let cert ← certSyntax r.cert
  -- `decide +kernel`: the two `Bool`s and the claim are reduced by the kernel, not by the
  -- compiler, so nothing in this file is trusted and no axiom is added
  adviseNative cfg r.cert
  let dec ← checkTactic cfg
  evalTactic (← `(tactic|
    exact LeanVIPR.Mip.pipeline_infeasible (v := $cert)
      (by $dec:tactic) (by $dec:tactic) (by $dec:tactic)))

end LeanVIPR.Tactic
