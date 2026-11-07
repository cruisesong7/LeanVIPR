module

public import LeanVIPR.Spec.Semantics.Claim
public import LeanVIPR.Impl.Checker.Rules

@[expose] public section

/-!
# Executable checks on the `SOL` section

The `Bool`-valued decisions behind the solution-related notions of
`LeanVIPR.Spec.Semantics.Claim`: that a listed solution is feasible, that the section as a whole
is, and that a `{ sol }` row is justified by one. Proved to agree with those notions in
`LeanVIPR.Thm.System.Claim`.
-/

namespace LeanVIPR.Parser.Vipr

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.System
open LeanVIPR.Semantics.Lower


/-! ## Executable predicates used by the checker -/

/-- Exact rational satisfaction test used for `SOL` vectors. -/
def satQ (c : SLe) (a : Valuation) : Bool :=
  if c.sense = 'L' then decide (c.form.eval a ≤ c.rhs)
  else if c.sense = 'G' then decide (c.rhs ≤ c.form.eval a)
  else if c.sense = 'E' then decide (c.form.eval a = c.rhs)
  else false

def solutionFeasible (v : Vipr) (s : NamedSolution) : Bool :=
  v.intVars.all (fun j => isIntVal (sparseValuation s.2 j)) &&
  (conSLes v).all (fun c => satQ c (sparseValuation s.2))

def allSolutions (v : Vipr) : Bool :=
  v.sols.toList.all (solutionFeasible v)

def solSection (v : Vipr) : Bool :=
  match v.rtp with
  | .infeas => v.sols.toList.isEmpty
  | .range lb ub =>
      allSolutions v &&
      if v.objSense = "min" then
        match ub with
        | none => true
        | some upper =>
            v.sols.toList.any (fun s => decide (objectiveQ v s ≤ upper))
      else if v.objSense = "max" then
        match lb with
        | none => true
        | some lower =>
            v.sols.toList.any (fun s => decide (lower ≤ objectiveQ v s))
      else false

def solReason (v : Vipr) (stated : SLe) : Bool :=
  if v.objSense = "min" then
    v.sols.toList.any (fun s =>
      domSLe ⟨'L', objectiveForm v, objectiveQ v s⟩ stated)
  else if v.objSense = "max" then
    v.sols.toList.any (fun s =>
      domSLe ⟨'G', objectiveForm v, objectiveQ v s⟩ stated)
  else false

end LeanVIPR.Parser.Vipr
