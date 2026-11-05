module

public import LeanVIPR.Spec.Semantics.System
public import LeanVIPR.Spec.Semantics.Lower

@[expose] public section

/-!
# What a certificate claims

**This is the claim.** It says what it means for a parsed certificate to be valid, which
is the statement `viprcheck` prints `ACCEPT` for. Definitions only.

Two things here that the infeasibility-only development does not need. `RTP range`
asserts bounds on the optimal value, so the claim has to quantify over *optimal*
valuations and not merely feasible ones. And a `{ sol }` derivation row is justified by
an exhibited solution, so unlike every other rule it is guaranteed at an optimum rather
than at every feasible point — `SolReasonValid` is where that asymmetry lives.

`ClaimValid` is the top-level statement: every listed solution is feasible, the primal
witness bound holds, and the derived objective bound holds at every feasible point. The
textbook reading — that every optimal value lies within the claimed range — is the
corollary `ClaimValid.optimal_within` in `LeanVIPR.Thm.System.Claim`.
-/

namespace LeanVIPR.Parser.Vipr

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.System
open LeanVIPR.Semantics.Lower


abbrev NamedSolution := String × List (Nat × ℚ)

def objectiveForm (v : Vipr) : LinForm :=
  v.objTerms.map (fun p => (⟨p.1, p.2⟩ : Term))

def sparseValuation : List (Nat × ℚ) → Valuation
  | [], _ => 0
  | (j, q) :: rest, i => if i = j then q else sparseValuation rest i

def solutionValuation (s : NamedSolution) : RealValuation :=
  fun i => (sparseValuation s.2 i : ℝ)

def objectiveQ (v : Vipr) (s : NamedSolution) : ℚ :=
  (objectiveForm v).eval (sparseValuation s.2)

def objectiveReal (v : Vipr) (a : RealValuation) : ℝ :=
  evalReal (objectiveForm v) a

@[simp] theorem evalReal_solution (f : LinForm) (s : NamedSolution) :
    evalReal f (solutionValuation s) = (f.eval (sparseValuation s.2) : ℝ) := by
  induction f with
  | nil => simp [evalReal, LinForm.eval]
  | cons t ts ih =>
      change
        (t.coeff : ℝ) * (sparseValuation s.2 t.idx : ℝ) +
            evalReal ts (solutionValuation s) =
          ((t.coeff * sparseValuation s.2 t.idx +
            LinForm.eval ts (sparseValuation s.2) : ℚ) : ℝ)
      rw [ih]
      push_cast
      ring

@[simp] theorem objectiveReal_solution (v : Vipr) (s : NamedSolution) :
    objectiveReal v (solutionValuation s) = (objectiveQ v s : ℝ) :=
  evalReal_solution _ _

def Feasible (v : Vipr) (a : RealValuation) : Prop :=
  (∀ j ∈ v.intVars, IsIntReal (a j)) ∧
  (∀ c ∈ conSLes v, satReal c a)

def IsOptimal (v : Vipr) (a : RealValuation) : Prop :=
  Feasible v a ∧
  if v.objSense = "min" then
    ∀ b, Feasible v b → objectiveReal v a ≤ objectiveReal v b
  else if v.objSense = "max" then
    ∀ b, Feasible v b → objectiveReal v b ≤ objectiveReal v a
  else False

def AllSolutionsValid (v : Vipr) : Prop :=
  ∀ s ∈ v.sols.toList, Feasible v (solutionValuation s)

def SolSectionValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => v.sols.toList = []
  | .range lb ub =>
      AllSolutionsValid v ∧
      if v.objSense = "min" then
        match ub with
        | none => True
        | some upper => ∃ s ∈ v.sols.toList, objectiveQ v s ≤ upper
      else if v.objSense = "max" then
        match lb with
        | none => True
        | some lower => ∃ s ∈ v.sols.toList, lower ≤ objectiveQ v s
      else False

def SolReasonValid (v : Vipr) (stated : SLe) : Prop :=
  if v.objSense = "min" then
    ∃ s ∈ v.sols.toList,
      Dominates ⟨'L', objectiveForm v, objectiveQ v s⟩ stated
  else if v.objSense = "max" then
    ∃ s ∈ v.sols.toList,
      Dominates ⟨'G', objectiveForm v, objectiveQ v s⟩ stated
  else False

/-- The objective at `a` is at least as good as at every listed solution.  Every
`{ sol }` row holds at such a valuation. -/
def SolBounded (v : Vipr) (a : RealValuation) : Prop :=
  if v.objSense = "min" then
    ∀ s ∈ v.sols.toList, objectiveReal v a ≤ (objectiveQ v s : ℝ)
  else if v.objSense = "max" then
    ∀ s ∈ v.sols.toList, (objectiveQ v s : ℝ) ≤ objectiveReal v a
  else False

/-- Valuations at which every derived row is guaranteed: feasible valuations for
infeasibility results; for range results, feasible valuations that are no worse
than every listed solution (in particular, every optimal valuation). -/
def Candidate (v : Vipr) (a : RealValuation) : Prop :=
  match v.rtp with
  | .infeas => Feasible v a
  | .range _ _ => Feasible v a ∧ SolBounded v a

/-! ## Declarative VIPR proof system -/

def objectiveLowerRow (v : Vipr) (lower : ℚ) : SLe :=
  ⟨'G', objectiveForm v, lower⟩

def objectiveUpperRow (v : Vipr) (upper : ℚ) : SLe :=
  ⟨'L', objectiveForm v, upper⟩

/-- Declarative validity of one VIPR step, including objective rows justified
by `{ sol }`. -/
def StepValid (v : Vipr) (pool : SPool) (s : SStep) : Prop :=
  ReferencesPast pool s.reason ∧
  match s.reason with
  | .asm => True
  | .lin comb => LinValid s.stated (resolve pool comb)
  | .rnd comb => RndValid v.intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      Dominates (spoolRow pool i1) s.stated ∧
      Dominates (spoolRow pool i2) s.stated ∧
      ComplementaryBounds v.intVars (spoolRow pool l1) (spoolRow pool l2)
  | .sol => SolReasonValid v s.stated

def DerivationValid (v : Vipr) (pool : SPool) : List SStep → Prop
  | [] => True
  | s :: ss =>
      StepValid v pool s ∧
      DerivationValid v (pool ++ [sentryOf pool s]) ss

def EndsInClosedAbsurdity (v : Vipr) : Prop :=
  ∃ e,
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e ∧
    e.2 = ∅ ∧ Absurd e.1

def EndsInClosedDominatingRow (v : Vipr) (target : SLe) : Prop :=
  ∃ e,
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e ∧
    e.2 = ∅ ∧ Dominates e.1 target

/-- The final-row condition depends on the relation to prove and objective
direction.  A minimization lower bound and a maximization upper bound need a
closed derived row; the opposite bound is witnessed by `SOL`. -/
def FinalValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => EndsInClosedAbsurdity v
  | .range lb ub =>
      if v.objSense = "min" then
        match lb with
        | none => True
        | some lower => EndsInClosedDominatingRow v (objectiveLowerRow v lower)
      else if v.objSense = "max" then
        match ub with
        | none => True
        | some upper => EndsInClosedDominatingRow v (objectiveUpperRow v upper)
      else False

def ProofValid (v : Vipr) : Prop :=
  SolSectionValid v ∧
  DerivationValid v (sinitPool (conSLes v)) (viprSteps v) ∧
  FinalValid v

def WithinRange (lb ub : Option ℚ) (q : ℝ) : Prop :=
  (match lb with
   | none => True
   | some lower => (lower : ℝ) ≤ q) ∧
  (match ub with
   | none => True
   | some upper => q ≤ (upper : ℝ))

/-- The derived objective bound of a range claim holds at **every feasible
valuation**, not only at optimal ones: for minimization the lower bound, for
maximization the upper bound.  This also bounds the infimum (supremum) when no
optimum is attained. -/
def RangeBoundValid (v : Vipr) (lb ub : Option ℚ) : Prop :=
  if v.objSense = "min" then
    match lb with
    | none => True
    | some lower => ∀ a, Feasible v a → (lower : ℝ) ≤ objectiveReal v a
  else if v.objSense = "max" then
    match ub with
    | none => True
    | some upper => ∀ a, Feasible v a → objectiveReal v a ≤ (upper : ℝ)
  else False

/-- Semantic validity of the result claimed by a VIPR certificate. For `RTP infeas`,
no feasible mixed-integer valuation exists.  For `RTP range`, every listed solution is
feasible, the required primal witness exists, and the derived objective bound holds at
every feasible valuation.  `ClaimValid.optimal_within` recovers the statement that
every optimal valuation lies in the reported interval. -/
def ClaimValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => ∀ a, Feasible v a → False
  | .range lb ub => SolSectionValid v ∧ RangeBoundValid v lb ub

end LeanVIPR.Parser.Vipr
