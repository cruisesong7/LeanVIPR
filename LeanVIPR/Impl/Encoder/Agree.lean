module

public import LeanVIPR.Spec.Mip
public import LeanVIPR.Spec.Semantics.Lower
public import LeanVIPR.Impl.Checker.Rules
public import LeanVIPR.Spec.Semantics.Claim

@[expose] public section

/-!
# Deciding that a certificate is about our problem

This is the soundness-critical half of the encoder. `viprcheck` can only ever conclude
something about the problem a certificate carries in its own `VAR`/`CON` sections; this
file decides whether that problem is ours.

It is needed because exact SCIP does not hand back a certificate in our numbering. On the
knapsack it declares `t_y t_x t_z` where we wrote `x y z` — renamed *and* permuted — so
any argument of the form "we encoded `m`, therefore the certificate is about `m`" would
have to pass through the solver's own bookkeeping, which is exactly what we refuse to
trust. Instead the connection is re-derived here from the certificate text.

## The split between guessing and checking

`recoverSigma` guesses the renaming and is **completely untrusted**: it may return
anything at all, including indices past the end of `m.vars`. `relaxesB` then checks the
guess, and `LeanVIPR.Thm.Encoder.Agree` proves that a passing check implies the transfer
of infeasibility. Nothing about `σ` is assumed — see `Mip.Relaxes` for why a valuation
`a ∘ σ` is well defined for an arbitrary `σ`, so a bad guess can only cause a rejection,
never a wrong acceptance.

That split is what makes the undocumented `t_` naming convention safe to rely on. If SCIP
changes it, or presolve mangles names further, this rejects rather than misbehaves, and
the fix is to improve the guess.
-/

namespace LeanVIPR.Impl.Encoder

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Parser LeanVIPR.Parser.Vipr LeanVIPR.Semantics.Lower

/-! ## Guessing the renaming (untrusted) -/

/-- The name exact SCIP gives a variable is the original with a `t_` prefix, so strip one
if present. Purely a heuristic; nothing is proved about it. -/
def bareName (n : String) : String :=
  if "t_".isPrefixOf n then String.ofList (n.toList.drop 2) else n

/-- Guess the map from the certificate's variable indices to ours, by name. An index with
no matching variable is sent to `m.vars.size`, which is out of range and so will fail the
row check rather than silently matching something. -/
def recoverSigma (m : Mip) (varNames : Array String) : Array Nat :=
  varNames.map (fun n =>
    match m.vars.findIdx? (fun w => w.name == bareName n) with
    | some j => j
    | none => m.vars.size)

/-- Guess the map in the other direction, from our variable indices to the
certificate's, again by name. An unmatched variable is sent past the end of the
certificate's variable list, so it fails the check rather than matching something. -/
def recoverTau (m : Mip) (varNames : Array String) : Array Nat :=
  m.vars.map (fun w =>
    match varNames.findIdx? (fun n => bareName n == w.name) with
    | some i => i
    | none => varNames.size)

/-- Read a guessed renaming as a total function, so it can be applied to any index. -/
def sigmaFn (σ : Array Nat) : Nat → Nat := fun i => σ.getD i 0

/-! ## Checking the guess (this is what soundness rests on) -/

/-- The `Bool`-valued decision for `Mip.RelaxesRows`, reusing the checker's own `dominates`
rather than list equality on `SLe`. See `Mip.Relaxes` for why: a renamed row carries its
terms in the certificate's index order, so the lists differ even when the rows are the
same linear constraint.

Generic in both problems, so the two directions below are the same function with its
arguments swapped. -/
def relaxesRowsB (rows₁ : List SLe) (ints₁ : List Nat) (σ : Array Nat)
    (rows₂ : List SLe) (ints₂ : List Nat) : Bool :=
  ints₂.all (fun i => decide (sigmaFn σ i ∈ ints₁)) &&
    rows₂.all (fun c => rows₁.any (fun d => dominates d (Mip.renameSLe (sigmaFn σ) c)))

def relaxesB (m : Mip) (σ : Array Nat) (rows : List SLe) (ints : List Nat) : Bool :=
  relaxesRowsB m.conSLes m.intVars σ rows ints

def relaxedB (m : Mip) (τ : Array Nat) (rows : List SLe) (ints : List Nat) : Bool :=
  relaxesRowsB rows ints τ m.conSLes m.intVars

/-- Decide whether `v` is a certificate about a problem `m` relaxes to. Enough for
`RTP infeas`, where only an emptiness claim travels. -/
def agreesWith (m : Mip) (v : Vipr) : Bool :=
  relaxesB m (recoverSigma m v.varNames) (conSLes v) v.intVars

/-- Decide the converse direction, which is what a *positive* answer needs. -/
def relaxedByWith (m : Mip) (v : Vipr) : Bool :=
  relaxedB m (recoverTau m v.varNames) (conSLes v) v.intVars

/-- Decide that the certificate's problem and ours are the *same* problem, each read
through its own recovered renaming. The LeanVIPR analogue of the guarantee Trestle's
`VEncCNF` carries in its type. -/
def sameProblemAs (m : Mip) (v : Vipr) : Bool :=
  agreesWith m v && relaxedByWith m v

/-- The `Bool`-valued decision for `Mip.ObjAgrees`, via the checker's `formEq`, which
compares two forms as linear functions rather than as lists.

Only the objective *form* is checked here. The objective *sense* is a separate hypothesis
on the theorems that need it, because the bound a `RTP range` certificate establishes is
a lower bound when minimizing and an upper bound when maximizing — so the sense belongs
with the claim, not with the agreement. -/
def objAgreesWith (m : Mip) (v : Vipr) : Bool :=
  formEq (Mip.renameForm (sigmaFn (recoverSigma m v.varNames)) (objectiveForm v)) m.obj

/-- The `Bool` for `Mip.ObjAgreesNeg`: the certificate's objective is ours negated, which
is what exact SCIP emits for a maximization. -/
def objAgreesNegWith (m : Mip) (v : Vipr) : Bool :=
  formEq (Mip.renameForm (sigmaFn (recoverSigma m v.varNames)) (objectiveForm v))
    (LinForm.scale (-1) m.obj)

end LeanVIPR.Impl.Encoder
