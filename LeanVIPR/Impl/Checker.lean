module

public import LeanVIPR.Impl.Checker.Solution

@[expose] public section

/-!
# Array-backed VIPR checker

This module implements the production VIPR checker:

* storing replay entries in an `Array`;
* fusing step validation and replay into one pass;
* computing each linear combination once per rule check.
-/

namespace LeanVIPR.Checker

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.Lower
open LeanVIPR.Parser.Vipr

abbrev CheckerEntry := SLe × SAsm
abbrev CheckerPool := Array CheckerEntry

@[inline] def poolEntry (pool : CheckerPool) (i : Nat) : CheckerEntry :=
  pool.getD i sdflt

@[inline] def poolRow (pool : CheckerPool) (i : Nat) : SLe :=
  (poolEntry pool i).1

@[inline] def poolAsm (pool : CheckerPool) (i : Nat) : SAsm :=
  (poolEntry pool i).2

def resolveRefs (pool : CheckerPool) (comb : List (ℚ × Nat)) : List (ℚ × SLe) :=
  comb.map fun p => (p.1, poolRow pool p.2)

def collectReferencedAsms (pool : CheckerPool) : List (ℚ × Nat) → SAsm
  | [] => ∅
  | p :: ps => poolAsm pool p.2 ∪ collectReferencedAsms pool ps

def entryOf (pool : CheckerPool) (s : SStep) : CheckerEntry :=
  match s.reason with
  | .asm => (s.stated, {s.stated})
  | .lin comb => (s.stated, collectReferencedAsms pool comb)
  | .rnd comb => (s.stated, collectReferencedAsms pool comb)
  | .uns i1 l1 i2 l2 =>
      (s.stated, (poolAsm pool i1).erase (poolRow pool l1) ∪
        (poolAsm pool i2).erase (poolRow pool l2))
  | .sol => (s.stated, ∅)

def referencesPastB (pool : CheckerPool) : SReason → Bool
  | .asm => true
  | .lin comb => comb.all fun p => decide (p.2 < pool.size)
  | .rnd comb => comb.all fun p => decide (p.2 < pool.size)
  | .uns i1 l1 i2 l2 =>
      decide (i1 < pool.size) && decide (l1 < pool.size) &&
      decide (i2 < pool.size) && decide (l2 < pool.size)
  | .sol => true

/-- The rule-specific half of a step check: everything except the index-bound test.

This reads rows out of the pool, and never assumption sets and never `pool.size`. So for
a step all of whose references point into the past, it gives the same answer against the
finished pool as against the shorter pool the sequential replay would have built by the
time it reached that step. `LeanVIPR.Thm.Checker` turns that into the equality with the
parallel checker. -/
def ruleCheckB (v : Vipr) (pool : CheckerPool) (s : SStep) : Bool :=
  match s.reason with
  | .asm => true
  | .lin comb => linCheck s.stated (resolveRefs pool comb)
  | .rnd comb => rndCheck v.intVars s.stated (resolveRefs pool comb)
  | .uns i1 l1 i2 l2 =>
      domSLe (poolRow pool i1) s.stated &&
      domSLe (poolRow pool i2) s.stated &&
      unsBoundsB v.intVars (poolRow pool l1) (poolRow pool l2)
  | .sol => solReasonB v s.stated

def stepValidB (v : Vipr) (pool : CheckerPool) (s : SStep) : Bool :=
  referencesPastB pool s.reason && ruleCheckB v pool s

def initialPool (v : Vipr) : CheckerPool :=
  v.cons.map fun c => (conToSLe v c, (∅ : SAsm))

def replaySteps? (v : Vipr) (pool : CheckerPool) : List SStep → Option CheckerPool
  | [] => some pool
  | s :: ss =>
      if stepValidB v pool s then
        replaySteps? v (pool.push (entryOf pool s)) ss
      else
        none

/-- `none` means that a step failed. `some last?` means replay succeeded, with the
optional final pool entry. -/
def replay? (v : Vipr) : Option (Option CheckerEntry) :=
  (replaySteps? v (initialPool v) (viprSteps v)).map Array.back?

def closedAbsurdB : Option CheckerEntry → Bool
  | none => false
  | some e => decide (e.2 = ∅) && absurdB e.1

def closedDominatesB (target : SLe) : Option CheckerEntry → Bool
  | none => false
  | some e => decide (e.2 = ∅) && domSLe e.1 target

def finalValidB (v : Vipr) (last? : Option CheckerEntry) : Bool :=
  match v.rtp with
  | .infeas => closedAbsurdB last?
  | .range lb ub =>
      if v.objSense = "min" then
        match lb with
        | none => true
        | some lower => closedDominatesB (objectiveLowerRow v lower) last?
      else if v.objSense = "max" then
        match ub with
        | none => true
        | some upper => closedDominatesB (objectiveUpperRow v upper) last?
      else false

/-! ## Parallel replay

Measured on `alu16_5`, 91% of replay is `ruleCheckB` and 2% is the assumption-set fold,
so the arithmetic is where the time is -- and it is independent across steps. Every row in
the pool comes straight from the certificate (`entryOf` always states `s.stated`), so the
pool can be built without validating anything, and then each step's rule check run against
the finished pool.

`Task` is pure in Lean's logic -- `Task.spawn fn = { get := fn () }` -- so the parallel
checker is provably equal to the sequential one and introduces no axioms, and kernel mode
reduces it sequentially. `LeanVIPR.Thm.Checker.checkViprPar_eq` is that equality. -/

/-- Build the pool without validating. Rows come from the certificate, so this is what the
sequential replay would produce if every check passed. -/
def buildPool (v : Vipr) (pool : CheckerPool) : List SStep → CheckerPool
  | [] => pool
  | s :: ss => buildPool v (pool.push (entryOf pool s)) ss

/-- `referencesPastB` against a pool of the given size. -/
def refsBelowB (size : Nat) : SReason → Bool
  | .asm => true
  | .lin comb => comb.all fun p => decide (p.2 < size)
  | .rnd comb => comb.all fun p => decide (p.2 < size)
  | .uns i1 l1 i2 l2 =>
      decide (i1 < size) && decide (l1 < size) &&
      decide (i2 < size) && decide (l2 < size)
  | .sol => true

/-- The index-bound half of replay: cheap, and the only half that must run in order. -/
def boundsOkB (size : Nat) : List SStep → Bool
  | [] => true
  | s :: ss => refsBelowB size s.reason && boundsOkB (size + 1) ss

/-- Split into runs of at most `n`, keeping the order. -/
def chunk (n : Nat) : List SStep → List (List SStep)
  | [] => []
  | s :: ss =>
      (s :: ss).take (max n 1) :: chunk n ((s :: ss).drop (max n 1))
  termination_by xs => xs.length
  decreasing_by
    simp only [List.length_drop, List.length_cons]
    omega

/-- `xs.all p`, evaluated one chunk per task. -/
def parAll (n : Nat) (p : SStep → Bool) (xs : List SStep) : Bool :=
  ((chunk n xs).map (fun c => Task.spawn (fun _ => c.all p))).all Task.get

/-- Steps per task, given how many tasks to aim for. One chunk per core measured best:
more chunks than that cost more in contention over the shared pool than they recover in
parallelism. The count is a parameter rather than a constant because the right value is
the core count, which only the `IO` layer can ask for -- and because the equality with
`checkVipr` holds for every value, so nothing about soundness depends on it. -/
def parChunkSize (tasks steps : Nat) : Nat := max 1 (steps / max tasks 1)

/-- Parallel production checker. Equal to `checkVipr` by
`LeanVIPR.Thm.Checker.checkViprPar_eq`. -/
def checkViprPar (tasks : Nat) (v : Vipr) : Bool :=
  solSectionB v &&
  (let steps := viprSteps v
   let start := initialPool v
   let final := buildPool v start steps
   boundsOkB start.size steps &&
   parAll (parChunkSize tasks steps.length) (fun s => ruleCheckB v final s) steps &&
   finalValidB v final.back?)

/-- Production checker for both infeasibility and objective-range VIPR claims. -/
def checkVipr (v : Vipr) : Bool :=
  solSectionB v &&
  match replay? v with
  | none => false
  | some last? => finalValidB v last?

/-- Checker for a backward-sliced infeasibility certificate: accept `sliced` as a
refutation of `original`. The slicer itself is untrusted, so this re-establishes every
side condition of `checkViprInfeasibleSubset_sound` at run time. The slicer keeps rows
in their original order, so a sublist test suffices. -/
def checkViprSlice (original sliced : Vipr) : Bool :=
  decide (sliced.rtp = .infeas) && decide (sliced.intVars = original.intVars) &&
    (conSLes sliced).isSublist (conSLes original) && checkVipr sliced

/-- `checkViprSlice` with the replay run in parallel. Equal to it by
`LeanVIPR.Thm.Checker.checkViprSlicePar_eq`. -/
def checkViprSlicePar (tasks : Nat) (original sliced : Vipr) : Bool :=
  decide (sliced.rtp = .infeas) && decide (sliced.intVars = original.intVars) &&
    (conSLes sliced).isSublist (conSLes original) && checkViprPar tasks sliced

end LeanVIPR.Checker
