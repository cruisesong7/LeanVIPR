module

public import LeanVIPR.Spec.System

@[expose] public section

/-!
# What completeness of the proof system would mean

Soundness starts with a certificate and proves semantic validity. Completeness goes the
other way: from semantic infeasibility, construct a finite certificate. This file states
that direction; it proves nothing. `LeanVIPR.Thm.System.Completeness` proves what can be
proved, which is one of the two ingredients.

The full mixed-integer theorem has two mathematically distinct parts:

1. exact rational LP infeasibility admits rational Farkas multipliers;
2. mixed-integer infeasibility admits a finite branch-and-cut derivation whose leaves
   are such LP refutations.

Each is named as its own proposition — `RationalFarkasComplete` and
`FiniteBranchAndCutComplete` — rather than silently assumed, so that a cited result from
the literature cannot be mistaken for something proved here.
-/

namespace LeanVIPR.Semantics.Completeness

open LeanVIPR.Semantics LeanVIPR.Semantics.System

/-- The problem really has no solution, over the reals with the stated variables
integral. -/
def SemanticallyInfeasible (base : List SLe) (intVars : List Nat) : Prop :=
  ∀ a : RealValuation,
    (∀ j ∈ intVars, IsIntReal (a j)) →
    (∀ c ∈ base, satReal c a) →
    False

/-- Some finite VIPR derivation refutes the problem. -/
def HasViprRefutation (base : List SLe) (intVars : List Nat) : Prop :=
  ∃ steps : List SStep, ProofValid intVars base steps

/-- The desired semantic completeness statement for VIPR infeasibility proofs. -/
def ProofSystemComplete : Prop :=
  ∀ (base : List SLe) (intVars : List Nat),
    SemanticallyInfeasible base intVars →
    HasViprRefutation base intVars

/-- An exact rational Farkas witness over the initial VIPR pool. Multipliers may be
signed because suitability is interpreted using each row's sense. -/
structure RationalFarkasWitness (base : List SLe) where
  comb : List (ℚ × Nat)
  referencesPast : ∀ p ∈ comb, p.2 < base.length
  suitable : SuitableLe (resolve (sinitPool base) comb)
  zero : FormZeroReal (scomb (resolve (sinitPool base) comb)).form
  negative : (scomb (resolve (sinitPool base) comb)).rhs < 0

def RationalFarkasWitness.conclusion {base : List SLe}
    (w : RationalFarkasWitness base) : SLe :=
  ⟨'L', (scomb (resolve (sinitPool base) w.comb)).form,
    (scomb (resolve (sinitPool base) w.comb)).rhs⟩

def RationalFarkasWitness.step {base : List SLe}
    (w : RationalFarkasWitness base) : SStep :=
  ⟨w.conclusion, .lin w.comb⟩

/-- Exact rational Farkas completeness, isolated as the mathematical existence theorem
the LP fragment needs. Not proved here. -/
def RationalFarkasComplete : Prop :=
  ∀ base : List SLe,
    SemanticallyInfeasible base [] →
    Nonempty (RationalFarkasWitness base)

/-- Completeness restricted to the rational LP fragment: no integer variables. -/
def LPFragmentComplete : Prop :=
  ∀ base : List SLe,
    SemanticallyInfeasible base [] →
    HasViprRefutation base []

/-- The remaining proposition needed for full mixed-integer completeness: every
semantically infeasible rational MILP has a finite VIPR derivation. Keeping this
explicit prevents the cited branch-and-cut completeness result from being mistaken for
something already proved in this development. -/
def FiniteBranchAndCutComplete : Prop := ProofSystemComplete

end LeanVIPR.Semantics.Completeness
