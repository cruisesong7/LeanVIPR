module

public meta import LeanVIPRTactic.Eval
public meta import LeanVIPRTactic.Config

@[expose] public section

/-!
# `#mip_scip`: run the pipeline on a `Mip` and report

Stage 2 of `docs/TACTIC-TODO.md`: the first piece of metaprogramming, and deliberately the
one that proves nothing. `#mip_scip m` elaborates `m` to a `Mip`, evaluates it, sends it
through `runScip`, and logs what came back — the certificate's shape, and each of the
`Bool`s a pipeline theorem takes as a hypothesis.

Two reasons it exists rather than being folded straight into a tactic:

* it is how a problem gets diagnosed. A tactic can only say "the certificate did not
  agree"; this says which checks passed, what the solver claimed, and with
  `(dir := "…")` leaves the `.mps` and `.vipr` on disk to look at.
* it separates the two failure modes that will otherwise be reported together. Getting a
  certificate at all is Stage 1's business; turning one into a proof term is Stage 3's.
  When the bundled tactic fails, the first question is which half failed, and this answers
  it without touching the goal.

Nothing here enters a proof. `#mip_scip` only logs.
-/

namespace LeanVIPR.Tactic

open Lean Elab Command Meta
open LeanVIPR LeanVIPR.Parser

/-! ## The command -/

/-- Run exact SCIP on a `Mip` and report what came back, without proving anything. Options
as for `mip`, in the `(opt := v)` form only.

```
#mip_scip knapsack
#mip_scip (dir := "/tmp/run") knapsack   -- keep the .mps and .vipr there
```
-/
syntax (name := mipScipCmd) "#mip_scip" mipTermConfig ppSpace term : command

@[command_elab mipScipCmd]
meta def elabMipScip : CommandElab := fun stx => do
  match stx with
  | `(#mip_scip $_cfg:mipTermConfig $t:term) => do
    let cfg := (← elabMipCommandConfig stx[1]).toScipConfig
    let m ← liftTermElabM (elabMip t)
    match ← liftM (m := IO) (runScip m cfg) with
    | .error e => logError e.message
    | .ok r =>
      logInfo m!"{r.binary}\n{r.summary}\n\
        pipeline_infeasible applies: {r.provesInfeasible}"
  | _ => throwUnsupportedSyntax

end LeanVIPR.Tactic
