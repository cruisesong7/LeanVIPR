module

public meta import LeanVIPRTactic.Scip
public meta import Lean.Elab.Command

@[expose] public section

/-!
# Elaboration-time plumbing shared by the command and the tactics

Three things the metacode needs and nothing else does: evaluating an elaborated `Mip`,
turning a solver run into a tactic-level error when it fails, and turning a returned
certificate back into syntax so it can be elaborated as a literal term.

All of it is untrusted. The certificate it produces is checked against the `Mip` the user
wrote, by `agreesWith`, inside the kernel — see `LeanVIPRTactic.Certify`.
-/

namespace LeanVIPR.Tactic

open Lean Elab Meta
open LeanVIPR LeanVIPR.Parser

/-! ## Evaluating an elaborated `Mip`

`Lean.Meta.evalExpr` is `unsafe` — it compiles and runs the term — so it is wrapped the
standard way, with the `opaque` declaration carrying the interface and
`@[implemented_by]` supplying the implementation. Running compiled code at elaboration
time costs no axiom: the value is used to *ask* the solver a question, and the answer is
checked against the elaborated term rather than against this value. -/

meta unsafe def evalMipUnsafe (e : Expr) : MetaM Mip :=
  Meta.evalExpr Mip (.const ``Mip []) e

@[implemented_by evalMipUnsafe]
meta opaque evalMip (e : Expr) : MetaM Mip

/-- Evaluate an `Expr` of type `Mip`, refusing anything with holes or free variables —
compiled code cannot be run on an open term, and the error is clearer here than inside
`evalExpr`. -/
meta def evalMipExpr (e : Expr) : MetaM Mip := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasFVar then
    throwError "the problem must be a closed term; this one still has holes or refers to \
      local variables:{indentExpr e}"
  evalMip e

/-- Elaborate a term as a `Mip` and evaluate it. -/
meta def elabMip (stx : Term) : TermElabM Mip := do
  let e ← Term.elabTerm stx (some (.const ``Mip []))
  Term.synthesizeSyntheticMVars
  evalMipExpr e

/-! ## Running the solver from elaboration -/

/-- Run exact SCIP, turning a `ScipError` into a tactic error. The message names the stage
that failed, since the remedies are unrelated — see `docs/TACTIC.md`. -/
meta def runScipForGoal (m : Mip) (cfg : ScipConfig := {}) : MetaM ScipRun := do
  match ← runScip m cfg with
  | .error e => throwError "{e.message}"
  | .ok r => return r

/-! ## A certificate as syntax

The `Repr` instances in `LeanVIPR.Spec.Syntax.Ast` are written to produce re-readable
output — that is what `reprOptionRat` is for — and `LeanVIPRMain`'s kernel mode already
depends on it when it writes a generated module. Parsing that text back here keeps the two
paths on one mechanism instead of adding a second `ToExpr` surface to drift from it.

Cost is a parse of a few hundred lines per invocation, which is nothing beside the kernel
reduction that follows. -/

meta def certSyntax (v : Vipr) : MetaM Term := do
  let text := (repr v).pretty
  match Parser.runParserCategory (← getEnv) `term text "<vipr-certificate>" with
  | .error err =>
      throwError "could not read the certificate back as a Lean term. This is a bug in \
        LeanVIPR's `Repr` instances, not in your problem.\n{err}"
  | .ok stx => return ⟨stx⟩

end LeanVIPR.Tactic
