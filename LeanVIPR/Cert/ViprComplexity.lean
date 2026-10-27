module

public import LeanVIPR.Cert.ViprTermination
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Structural complexity of the array-backed VIPR checker

This source-level cost model follows the production implementation. It counts
one rule check and one array write per derivation record, sparse referenced-row
input, finite-set assumption work, and solution-vector input. Array allocation,
arbitrary-precision bit complexity, and compiler/runtime constants are outside
the model.
-/

namespace LeanVIPR.Cert.ViprComplexity

open LeanVIPR.Ast LeanVIPR.Pipeline
open LeanVIPR.Cert LeanVIPR.Cert.ViprChecker LeanVIPR.Ast.Vipr
open LeanVIPR.Cert.ViprSystem

def reasonReferenceCount : SReason → Nat
  | .asm | .sol => 0
  | .lin comb | .rnd comb => comb.length
  | .uns _ _ _ _ => 4

def totalReferenceCount (steps : List SStep) : Nat :=
  (steps.map fun s => reasonReferenceCount s.reason).sum

/-- Sparse cells read by one rule check, resolving references in the parsed
certificate's global row numbering. -/
def reasonInputCells (v : Vipr) : SReason → Nat
  | .asm | .sol => 0
  | .lin comb | .rnd comb =>
      (comb.map fun p => 1 + (viprRow v p.2).form.length).sum
  | .uns i1 l1 i2 l2 =>
      4 + (viprRow v i1).form.length + (viprRow v l1).form.length +
        (viprRow v i2).form.length + (viprRow v l2).form.length

def replayRuleInputCells (v : Vipr) : Nat :=
  ((viprSteps v).map fun s =>
    1 + s.stated.form.length + reasonInputCells v s.reason).sum

def stepRuleInputCells (v : Vipr) (step : SStep) : Nat :=
  1 + step.stated.form.length + reasonInputCells v step.reason

def stepRowCells (step : SStep) : Nat :=
  1 + step.stated.form.length

def stepsRowCells (steps : List SStep) : Nat :=
  (steps.map stepRowCells).sum

def poolRowCellCount (pool : CheckerPool) : Nat :=
  (pool.toList.map fun entry => 1 + entry.1.form.length).sum

theorem entryOf_row (pool : CheckerPool) (step : SStep) :
    (entryOf pool step).1 = step.stated := by
  cases step with
  | mk stated reason =>
      cases reason <;> rfl

def solReasonCount : List SStep → Nat
  | [] => 0
  | s :: ss =>
      (match s.reason with | .sol => 1 | _ => 0) + solReasonCount ss

def constraintTermCells (v : Vipr) : Nat :=
  ((conSLes v).map fun c => 1 + c.form.length).sum

def oneSolutionInputCells (v : Vipr) (s : NamedSolution) : Nat :=
  (1 + v.intVars.length + constraintTermCells v + (objectiveForm v).length) *
    (s.2.length + 1)

def solutionVectorInputCells (v : Vipr) : Nat :=
  (v.sols.toList.map fun s => oneSolutionInputCells v s).sum

def stepSolutionInputCells (v : Vipr) (step : SStep) : Nat :=
  match step.reason with
  | .sol => solutionVectorInputCells v
  | _ => 0

def solutionInputCells (v : Vipr) : Nat :=
  (2 + solReasonCount (viprSteps v)) *
    solutionVectorInputCells v

/-- Distinct rows introduced by `asm` records in a derivation list. -/
def asmRows : List SStep → SAsm
  | [] => ∅
  | step :: steps =>
      match step.reason with
      | .asm => insert step.stated (asmRows steps)
      | _ => asmRows steps

/-- Number of `asm` records, counting duplicate stated rows separately. -/
def asmCount : List SStep → Nat
  | [] => 0
  | step :: steps =>
      (match step.reason with
       | .asm => 1
       | _ => 0) + asmCount steps

theorem mem_asmRows_of_mem
    {step : SStep} {steps : List SStep}
    (hstep : step ∈ steps) (hasm : step.reason = .asm) :
    step.stated ∈ asmRows steps := by
  induction steps with
  | nil =>
      simp at hstep
  | cons head tail ih =>
      rcases List.mem_cons.mp hstep with rfl | htail
      · simp [asmRows, hasm]
      · cases hreason : head.reason <;>
          simp [asmRows, hreason, ih htail]

theorem asmRows_card_le_asmCount (steps : List SStep) :
    (asmRows steps).card ≤ asmCount steps := by
  induction steps with
  | nil =>
      simp [asmRows, asmCount]
  | cons step steps ih =>
      cases hreason : step.reason with
      | asm =>
          have hinsert :=
            Finset.card_insert_le step.stated (asmRows steps)
          simp only [asmRows, asmCount, hreason]
          omega
      | lin comb =>
          simpa [asmRows, asmCount, hreason] using ih
      | rnd comb =>
          simpa [asmRows, asmCount, hreason] using ih
      | uns i1 l1 i2 l2 =>
          simpa [asmRows, asmCount, hreason] using ih
      | sol =>
          simpa [asmRows, asmCount, hreason] using ih

theorem asmCount_le_length (steps : List SStep) :
    asmCount steps ≤ steps.length := by
  induction steps with
  | nil =>
      simp [asmCount]
  | cons step steps ih =>
      cases hreason : step.reason <;>
        simp [asmCount, hreason] <;> omega

/-- Every assumption set currently stored in a checker pool is contained in
one fixed finite family of permitted assumption rows. -/
def PoolAssumptionsWithin (allowed : SAsm) (pool : CheckerPool) : Prop :=
  ∀ entry ∈ pool.toList, entry.2 ⊆ allowed

theorem poolAsm_subset_of_assumptionsWithin
    {allowed : SAsm} {pool : CheckerPool}
    (hpool : PoolAssumptionsWithin allowed pool)
    {idx : Nat} (hidx : idx < pool.toList.length) :
    poolAsm pool idx ⊆ allowed := by
  rw [poolAsm_eq]
  unfold spoolAsm
  rw [List.getD_eq_getElem pool.toList sdflt hidx]
  exact hpool _ (List.getElem_mem hidx)

theorem collectReferencedAsms_subset
    {allowed : SAsm} {pool : CheckerPool}
    (hpool : PoolAssumptionsWithin allowed pool) :
    ∀ (comb : List (ℚ × Nat)),
      (∀ p ∈ comb, p.2 < pool.toList.length) →
      collectReferencedAsms pool comb ⊆ allowed := by
  intro comb hrefs
  induction comb with
  | nil =>
      simp [collectReferencedAsms]
  | cons p ps ih =>
      intro assumption hassumption
      simp only [collectReferencedAsms, Finset.mem_union] at hassumption
      rcases hassumption with hp | hps
      · exact
          poolAsm_subset_of_assumptionsWithin hpool
            (hrefs p (by simp)) hp
      · exact
          ih
            (fun candidate hcandidate =>
              hrefs candidate (by simp [hcandidate]))
            hps

theorem entryOf_assumptions_subset
    {allowed : SAsm} {pool : CheckerPool} {step : SStep}
    (hpool : PoolAssumptionsWithin allowed pool)
    (hrefs : ReferencesPast pool.toList step.reason)
    (hasm : step.reason = .asm → step.stated ∈ allowed) :
    (entryOf pool step).2 ⊆ allowed := by
  cases hreason : step.reason with
  | asm =>
      simpa [entryOf, hreason] using hasm hreason
  | lin comb =>
      simp only [hreason] at hrefs
      simpa [entryOf, hreason] using
        collectReferencedAsms_subset hpool comb hrefs
  | rnd comb =>
      simp only [hreason] at hrefs
      simpa [entryOf, hreason] using
        collectReferencedAsms_subset hpool comb hrefs
  | uns i1 l1 i2 l2 =>
      simp only [hreason] at hrefs
      intro assumption hassumption
      simp only [entryOf, hreason, Finset.mem_union, Finset.mem_erase] at hassumption
      rcases hassumption with hleft | hright
      · exact
          poolAsm_subset_of_assumptionsWithin hpool hrefs.1
            hleft.2
      · exact
          poolAsm_subset_of_assumptionsWithin hpool hrefs.2.2.1
            hright.2
  | sol =>
      simp [entryOf, hreason]

theorem assumptionsWithin_push
    {allowed : SAsm} {pool : CheckerPool} {entry : CheckerEntry}
    (hpool : PoolAssumptionsWithin allowed pool)
    (hentry : entry.2 ⊆ allowed) :
    PoolAssumptionsWithin allowed (pool.push entry) := by
  intro candidate hcandidate
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hcandidate
  rcases hcandidate with hcandidate | rfl
  · exact hpool candidate hcandidate
  · exact hentry

/-- Sum of the cardinalities of all open-assumption sets resident in a pool. -/
def assumptionCellCount (pool : CheckerPool) : Nat :=
  (pool.toList.map fun entry => entry.2.card).sum

theorem assumptionCellCount_push (pool : CheckerPool) (entry : CheckerEntry) :
    assumptionCellCount (pool.push entry) =
      assumptionCellCount pool + entry.2.card := by
  simp [assumptionCellCount]

/-- A successful replay preserves assumption provenance and adds at most
`allowed.card` resident assumption cells per derivation record. -/
theorem replaySteps_assumption_bound
    (v : Vipr) (allowed : SAsm) :
    ∀ (pool : CheckerPool) (steps : List SStep) (final : CheckerPool),
      PoolAssumptionsWithin allowed pool →
      (∀ step ∈ steps, step.reason = .asm → step.stated ∈ allowed) →
      replaySteps? v pool steps = some final →
      PoolAssumptionsWithin allowed final ∧
        assumptionCellCount final ≤
          assumptionCellCount pool + steps.length * allowed.card := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro final hpool _ hreplay
      simp only [replaySteps?] at hreplay
      cases hreplay
      exact ⟨hpool, by simp⟩
  | cons step steps ih =>
      intro final hpool hasm hreplay
      simp only [replaySteps?] at hreplay
      by_cases hvalid : stepValidB v pool step = true
      · simp only [hvalid, ite_true] at hreplay
        have hvalidParts := hvalid
        rw [stepValidB, Bool.and_eq_true] at hvalidParts
        have hrefs : ReferencesPast pool.toList step.reason :=
          referencesPastB_sound hvalidParts.1
        have hentrySubset :
            (entryOf pool step).2 ⊆ allowed :=
          entryOf_assumptions_subset hpool hrefs
            (hasm step (by simp) ·)
        have hpush :
            PoolAssumptionsWithin allowed
              (pool.push (entryOf pool step)) :=
          assumptionsWithin_push hpool hentrySubset
        obtain ⟨hfinal, hcost⟩ :=
          ih (pool.push (entryOf pool step)) final hpush
            (fun candidate hcandidate =>
              hasm candidate (by simp [hcandidate]))
            hreplay
        refine ⟨hfinal, ?_⟩
        rw [assumptionCellCount_push] at hcost
        have hentryCard :
            (entryOf pool step).2.card ≤ allowed.card :=
          Finset.card_le_card hentrySubset
        calc
          assumptionCellCount final ≤
              (assumptionCellCount pool + (entryOf pool step).2.card) +
                steps.length * allowed.card := hcost
          _ ≤ (assumptionCellCount pool + allowed.card) +
                steps.length * allowed.card :=
            Nat.add_le_add_right
              (Nat.add_le_add_left hentryCard _)
              (steps.length * allowed.card)
          _ = assumptionCellCount pool +
                (step :: steps).length * allowed.card := by
            simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [hvalid] at hreplay

theorem initialPool_assumptionsWithin (v : Vipr) (allowed : SAsm) :
    PoolAssumptionsWithin allowed (initialPool v) := by
  intro entry hentry
  simp [initialPool] at hentry
  obtain ⟨constraint, _, rfl⟩ := hentry
  simp

theorem initialPool_assumptionCellCount (v : Vipr) :
    assumptionCellCount (initialPool v) = 0 := by
  simp [assumptionCellCount, initialPool, Function.comp_def]

/-- Actual successful replay stores at most one assumption cell per
derivation record and `asm` record. -/
theorem successfulReplay_assumptionCells_le
    {v : Vipr} {final : CheckerPool}
    (hreplay :
      replaySteps? v (initialPool v) (viprSteps v) = some final) :
    assumptionCellCount final ≤
      (viprSteps v).length * asmCount (viprSteps v) := by
  let allowed := asmRows (viprSteps v)
  have hasm :
      ∀ step ∈ viprSteps v,
        step.reason = .asm → step.stated ∈ allowed := by
    intro step hstep hreason
    exact mem_asmRows_of_mem hstep hreason
  obtain ⟨_, hbound⟩ :=
    replaySteps_assumption_bound v allowed
      (initialPool v) (viprSteps v) final
      (initialPool_assumptionsWithin v allowed) hasm hreplay
  rw [initialPool_assumptionCellCount, Nat.zero_add] at hbound
  exact
    hbound.trans
      (by
        simpa [allowed] using
          Nat.mul_le_mul_left (viprSteps v).length
            (asmRows_card_le_asmCount (viprSteps v)))

/-- Vector budget for the production checker. `assumptionCells` bounds resident
open assumptions by `k * a`; `assumptionMergeCells` bounds referenced finite-set
inputs by `a` times the number of row references, where `a` is the number of
`asm` records. -/
structure CheckerWork where
  ruleChecks : Nat
  arrayWrites : Nat
  ruleInputCells : Nat
  assumptionCells : Nat
  assumptionMergeCells : Nat
  solutionInputCells : Nat
deriving Repr, DecidableEq

def CheckerWork.zero : CheckerWork :=
  { ruleChecks := 0
    arrayWrites := 0
    ruleInputCells := 0
    assumptionCells := 0
    assumptionMergeCells := 0
    solutionInputCells := 0 }

def CheckerWork.add (left right : CheckerWork) : CheckerWork :=
  { ruleChecks := left.ruleChecks + right.ruleChecks
    arrayWrites := left.arrayWrites + right.arrayWrites
    ruleInputCells := left.ruleInputCells + right.ruleInputCells
    assumptionCells := left.assumptionCells + right.assumptionCells
    assumptionMergeCells :=
      left.assumptionMergeCells + right.assumptionMergeCells
    solutionInputCells := left.solutionInputCells + right.solutionInputCells }

/-- Componentwise comparison of structural work vectors. -/
def CheckerWork.LE (actual upper : CheckerWork) : Prop :=
  actual.ruleChecks ≤ upper.ruleChecks ∧
    actual.arrayWrites ≤ upper.arrayWrites ∧
    actual.ruleInputCells ≤ upper.ruleInputCells ∧
    actual.assumptionCells ≤ upper.assumptionCells ∧
    actual.assumptionMergeCells ≤ upper.assumptionMergeCells ∧
    actual.solutionInputCells ≤ upper.solutionInputCells

/-- Replay-pool memory, separated from structural execution work. -/
structure CheckerSpace where
  poolEntries : Nat
  rowCells : Nat
  assumptionCells : Nat
deriving Repr, DecidableEq

/-- Componentwise comparison of replay-space vectors. -/
def CheckerSpace.LE (actual upper : CheckerSpace) : Prop :=
  actual.poolEntries ≤ upper.poolEntries ∧
    actual.rowCells ≤ upper.rowCells ∧
    actual.assumptionCells ≤ upper.assumptionCells

def CheckerSpace.ofPool (pool : CheckerPool) : CheckerSpace :=
  { poolEntries := pool.size
    rowCells := poolRowCellCount pool
    assumptionCells := assumptionCellCount pool }

def CheckerSpace.total (space : CheckerSpace) : Nat :=
  space.poolEntries + space.rowCells + space.assumptionCells

/-- Structural charge for one visited replay record. Merge work is charged by
`a` cells per reference, justified by the assumption-provenance theorem above.
An array write is charged only when the record passes validation. -/
def stepWorkCharge (v : Vipr) (a : Nat) (wrote : Bool) (step : SStep) :
    CheckerWork :=
  { ruleChecks := 1
    arrayWrites := if wrote then 1 else 0
    ruleInputCells := stepRuleInputCells v step
    assumptionCells := 0
    assumptionMergeCells := a * reasonReferenceCount step.reason
    solutionInputCells := stepSolutionInputCells v step }

/-- Instrumented replay with exactly the same branching and pool updates as
`replaySteps?`. The second projection records structural work charged on the
visited prefix; arithmetic bit complexity is intentionally not included. -/
def replayStepsProfiled? (v : Vipr) (a : Nat) (pool : CheckerPool) :
    List SStep → Option CheckerPool × CheckerWork
  | [] => (some pool, CheckerWork.zero)
  | step :: steps =>
      if stepValidB v pool step then
        let tail :=
          replayStepsProfiled? v a
            (pool.push (entryOf pool step)) steps
        (tail.1,
          CheckerWork.add
            (stepWorkCharge v a true step) tail.2)
      else
        (none, stepWorkCharge v a false step)

/-- Whole-list replay budget corresponding to visiting and accepting every
derivation record. -/
def replayWorkUpper (v : Vipr) (a : Nat) : List SStep → CheckerWork
  | [] => CheckerWork.zero
  | step :: steps =>
      CheckerWork.add
        (stepWorkCharge v a true step)
        (replayWorkUpper v a steps)

theorem replayStepsProfiled_result
    (v : Vipr) (a : Nat) (pool : CheckerPool) (steps : List SStep) :
    (replayStepsProfiled? v a pool steps).1 =
      replaySteps? v pool steps := by
  induction steps generalizing pool with
  | nil =>
      rfl
  | cons step steps ih =>
      simp only [replayStepsProfiled?, replaySteps?]
      by_cases hvalid : stepValidB v pool step = true
      · simp [hvalid, ih]
      · simp [hvalid]

/-- Instrumented replay never exceeds the budget obtained by visiting and
accepting every remaining record. -/
theorem replayStepsProfiled_work_le
    (v : Vipr) (a : Nat) (pool : CheckerPool) (steps : List SStep) :
    CheckerWork.LE
      (replayStepsProfiled? v a pool steps).2
      (replayWorkUpper v a steps) := by
  induction steps generalizing pool with
  | nil =>
      simp [replayStepsProfiled?, replayWorkUpper, CheckerWork.LE,
        CheckerWork.zero]
  | cons step steps ih =>
      simp only [replayStepsProfiled?, replayWorkUpper]
      by_cases hvalid : stepValidB v pool step = true
      · simp only [hvalid, ite_true]
        have htail :=
          ih (pool.push (entryOf pool step))
        simp only [CheckerWork.LE, CheckerWork.add] at htail ⊢
        exact ⟨Nat.add_le_add_left htail.1 _,
          Nat.add_le_add_left htail.2.1 _,
          Nat.add_le_add_left htail.2.2.1 _,
          Nat.add_le_add_left htail.2.2.2.1 _,
          Nat.add_le_add_left htail.2.2.2.2.1 _,
          Nat.add_le_add_left htail.2.2.2.2.2 _⟩
      · simp [hvalid, CheckerWork.LE, CheckerWork.add, stepWorkCharge]

theorem replayWorkUpper_ruleChecks
    (v : Vipr) (a : Nat) (steps : List SStep) :
    (replayWorkUpper v a steps).ruleChecks = steps.length := by
  induction steps with
  | nil =>
      rfl
  | cons step steps ih =>
      simp [replayWorkUpper, CheckerWork.add, stepWorkCharge, ih, Nat.add_comm]

theorem replayWorkUpper_arrayWrites
    (v : Vipr) (a : Nat) (steps : List SStep) :
    (replayWorkUpper v a steps).arrayWrites = steps.length := by
  induction steps with
  | nil =>
      rfl
  | cons step steps ih =>
      simp [replayWorkUpper, CheckerWork.add, stepWorkCharge, ih, Nat.add_comm]

theorem replayWorkUpper_ruleInputCells
    (v : Vipr) (a : Nat) (steps : List SStep) :
    (replayWorkUpper v a steps).ruleInputCells =
      (steps.map fun step => stepRuleInputCells v step).sum := by
  induction steps with
  | nil =>
      rfl
  | cons step steps ih =>
      simp [replayWorkUpper, CheckerWork.add, stepWorkCharge, ih]

theorem replayWorkUpper_assumptionCells
    (v : Vipr) (a : Nat) (steps : List SStep) :
    (replayWorkUpper v a steps).assumptionCells = 0 := by
  induction steps with
  | nil =>
      rfl
  | cons step steps ih =>
      simp [replayWorkUpper, CheckerWork.add, stepWorkCharge, ih]

theorem replayWorkUpper_assumptionMergeCells
    (v : Vipr) (a : Nat) (steps : List SStep) :
    (replayWorkUpper v a steps).assumptionMergeCells =
      a * totalReferenceCount steps := by
  induction steps with
  | nil =>
      simp [replayWorkUpper, totalReferenceCount, CheckerWork.zero]
  | cons step steps ih =>
      simp [replayWorkUpper, CheckerWork.add, stepWorkCharge,
        totalReferenceCount, ih, Nat.mul_add]

theorem replayWorkUpper_solutionInputCells
    (v : Vipr) (a : Nat) (steps : List SStep) :
    (replayWorkUpper v a steps).solutionInputCells =
      solReasonCount steps * solutionVectorInputCells v := by
  induction steps with
  | nil =>
      simp [replayWorkUpper, solReasonCount, CheckerWork.zero]
  | cons step steps ih =>
      cases hreason : step.reason <;>
        simp [replayWorkUpper, CheckerWork.add, stepWorkCharge,
          stepSolutionInputCells, solReasonCount, hreason, ih,
          Nat.add_mul]

def checkerWorkUpper (v : Vipr) : CheckerWork :=
  let steps := viprSteps v
  let k := steps.length
  let a := asmCount steps
  { ruleChecks := k
    arrayWrites := k
    ruleInputCells := replayRuleInputCells v
    assumptionCells := k * a
    assumptionMergeCells := a * totalReferenceCount steps
    solutionInputCells := solutionInputCells v }

/-- Structural time charged in unit sparse/set input cells. Resident
assumption storage is excluded and reported by `CheckerSpace`. -/
def CheckerWork.timeTotal (w : CheckerWork) : Nat :=
  w.ruleChecks + w.arrayWrites + w.ruleInputCells +
    w.assumptionMergeCells + w.solutionInputCells

/-- Compatibility alias for the former undifferentiated cost API. -/
def CheckerWork.total (w : CheckerWork) : Nat :=
  w.timeTotal

/-- Whole-replay resident-space budget. Row storage is parameterized by the
actual sparse rows; open assumptions contribute `k * a`. -/
def checkerSpaceUpper (v : Vipr) : CheckerSpace :=
  let steps := viprSteps v
  let k := steps.length
  let a := asmCount steps
  { poolEntries := (initialPool v).size + k
    rowCells := poolRowCellCount (initialPool v) + stepsRowCells steps
    assumptionCells := k * a }

/-- Fixed solution-section charge: one complete feasibility scan and at most
one complete objective-witness scan. -/
def solutionSectionWork (v : Vipr) : CheckerWork :=
  { CheckerWork.zero with
    solutionInputCells := 2 * solutionVectorInputCells v }

/-- Production-equivalent checker execution paired with its charged
source-level structural work on the actually visited replay prefix. -/
def checkViprProfiled (v : Vipr) : Bool × CheckerWork :=
  let a := asmCount (viprSteps v)
  let replay :=
    replayStepsProfiled? v a (initialPool v) (viprSteps v)
  let accepted :=
    solSectionB v &&
      match replay.1.map Array.back? with
      | none => false
      | some last? => finalValidB v last?
  (accepted, CheckerWork.add (solutionSectionWork v) replay.2)

theorem checkViprProfiled_value (v : Vipr) :
    (checkViprProfiled v).1 = checkVipr v := by
  unfold checkViprProfiled checkVipr replay?
  dsimp
  rw [replayStepsProfiled_result]
  rfl

/-- The instrumented execution is componentwise bounded by the public
whole-certificate structural budget. -/
theorem checkViprProfiled_work_le (v : Vipr) :
    CheckerWork.LE
      (checkViprProfiled v).2
      (checkerWorkUpper v) := by
  let k := (viprSteps v).length
  let a := asmCount (viprSteps v)
  let steps := viprSteps v
  have hreplay :=
    replayStepsProfiled_work_le
      v a (initialPool v) steps
  have hruleChecks :=
    replayWorkUpper_ruleChecks v a steps
  have harrayWrites :=
    replayWorkUpper_arrayWrites v a steps
  have hruleInput :=
    replayWorkUpper_ruleInputCells v a steps
  have hassumptions :=
    replayWorkUpper_assumptionCells v a steps
  have hmerge :=
    replayWorkUpper_assumptionMergeCells v a steps
  have hsolutions :=
    replayWorkUpper_solutionInputCells v a steps
  simp only [CheckerWork.LE] at hreplay ⊢
  simp only [checkViprProfiled, solutionSectionWork, CheckerWork.add,
    CheckerWork.zero, checkerWorkUpper]
  change
    _ ≤ k ∧ _ ≤ k ∧ _ ≤ replayRuleInputCells v ∧
      _ ≤ k * a ∧ _ ≤ a * totalReferenceCount steps ∧
      _ ≤ solutionInputCells v
  constructor
  · simpa [k, steps, hruleChecks] using hreplay.1
  constructor
  · simpa [k, steps, harrayWrites] using hreplay.2.1
  constructor
  · have h := hreplay.2.2.1
    rw [hruleInput] at h
    simpa [steps, replayRuleInputCells, stepRuleInputCells] using h
  constructor
  · have h := hreplay.2.2.2.1
    rw [hassumptions] at h
    simpa [k, a, steps] using h.trans (Nat.zero_le (k * a))
  constructor
  · have h := hreplay.2.2.2.2.1
    rw [hmerge] at h
    simpa [steps] using h
  · have h := hreplay.2.2.2.2.2
    rw [hsolutions] at h
    simpa [solutionInputCells, steps, Nat.add_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_left h (2 * solutionVectorInputCells v)

theorem checkerWorkUpper_ruleChecks (v : Vipr) :
    (checkerWorkUpper v).ruleChecks = (viprSteps v).length := rfl

theorem checkerWorkUpper_arrayWrites (v : Vipr) :
    (checkerWorkUpper v).arrayWrites = (viprSteps v).length := rfl

/-- Successful replay stores exactly the initial sparse rows followed by one
stated sparse row per accepted derivation record. -/
theorem replaySteps_rowCells (v : Vipr) :
    ∀ (pool : CheckerPool) (steps : List SStep) (final : CheckerPool),
      replaySteps? v pool steps = some final →
      poolRowCellCount final =
        poolRowCellCount pool + stepsRowCells steps := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro final hreplay
      simp only [replaySteps?] at hreplay
      cases hreplay
      simp [stepsRowCells]
  | cons step steps ih =>
      intro final hreplay
      simp only [replaySteps?] at hreplay
      by_cases hvalid : stepValidB v pool step = true
      · simp only [hvalid, ite_true] at hreplay
        have htail :=
          ih (pool.push (entryOf pool step)) final hreplay
        simpa [poolRowCellCount, stepsRowCells, stepRowCells,
          entryOf_row, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using htail
      · simp [hvalid] at hreplay

/-- Successful production replay satisfies the componentwise replay-space
budget: linear pool and sparse-row storage, plus `k * a` open assumptions. -/
theorem successfulReplay_space_le
    {v : Vipr} {final : CheckerPool}
    (hreplay :
      replaySteps? v (initialPool v) (viprSteps v) = some final) :
    CheckerSpace.LE (CheckerSpace.ofPool final) (checkerSpaceUpper v) := by
  have hsize :=
    ViprTermination.replaySteps_size
      v (initialPool v) (viprSteps v) final hreplay
  have hrows :=
    replaySteps_rowCells
      v (initialPool v) (viprSteps v) final hreplay
  have hassumptions :=
    successfulReplay_assumptionCells_le hreplay
  exact ⟨by simpa [CheckerSpace.ofPool, checkerSpaceUpper] using hsize.le,
    by simpa [CheckerSpace.ofPool, checkerSpaceUpper] using hrows.le,
    by simpa [CheckerSpace.ofPool, checkerSpaceUpper] using hassumptions⟩

/-- Exact expansion of the production checker's structural time model. -/
theorem checkVipr_structural_time (v : Vipr) :
    (checkerWorkUpper v).timeTotal =
      2 * (viprSteps v).length +
      replayRuleInputCells v +
      asmCount (viprSteps v) * totalReferenceCount (viprSteps v) +
      solutionInputCells v := by
  simp [CheckerWork.timeTotal, checkerWorkUpper]
  omega

/-- Exact expansion of the resident replay-space model. -/
theorem checkVipr_structural_space (v : Vipr) :
    (checkerSpaceUpper v).total =
      (initialPool v).size +
      (viprSteps v).length +
      poolRowCellCount (initialPool v) +
      stepsRowCells (viprSteps v) +
      (viprSteps v).length * asmCount (viprSteps v) := by
  simp [CheckerSpace.total, checkerSpaceUpper]
  omega

/-- Branch-free replays pay no assumption-merging cost. -/
theorem checkVipr_structural_time_no_asm
    (v : Vipr) (hnoAsm : asmCount (viprSteps v) = 0) :
    (checkerWorkUpper v).timeTotal =
      2 * (viprSteps v).length +
      replayRuleInputCells v +
      solutionInputCells v := by
  rw [checkVipr_structural_time, hnoAsm]
  simp

/-- Branch-free replays store no open-assumption cells. -/
theorem checkVipr_structural_space_no_asm
    (v : Vipr) (hnoAsm : asmCount (viprSteps v) = 0) :
    (checkerSpaceUpper v).total =
      (initialPool v).size +
      (viprSteps v).length +
      poolRowCellCount (initialPool v) +
      stepsRowCells (viprSteps v) := by
  rw [checkVipr_structural_space, hnoAsm]
  simp

/-- Compatibility form of `checkVipr_structural_time`. -/
theorem checkVipr_structural_cost (v : Vipr) :
    (checkerWorkUpper v).total =
      2 * (viprSteps v).length +
      replayRuleInputCells v +
      asmCount (viprSteps v) * totalReferenceCount (viprSteps v) +
      solutionInputCells v := by
  simpa [CheckerWork.total] using checkVipr_structural_time v

end LeanVIPR.Cert.ViprComplexity
