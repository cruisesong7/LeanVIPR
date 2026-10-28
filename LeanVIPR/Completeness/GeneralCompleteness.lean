module

public import LeanVIPR.Completeness.ProjectionCompile

@[expose] public section

/-!
# A sufficient reduction through the syntactic refutation-tree model

All mixed-sense and continuous-variable obligations are discharged before the
remaining theorem.  The `RefTree.derive` constructor records the literal
concatenated form of a combination, so this module gives a useful sufficient
reduction but is stricter than the general VIPR `rnd` rule.  Arbitrary
Chvátal--Gomory cuts, whose coefficients may become integral only after
aggregation, are modeled in `ChvatalGomory`.
-/

namespace LeanVIPR.Completeness.GeneralCompleteness

open LeanVIPR.Cert LeanVIPR.Completeness.IntegerProjection
  LeanVIPR.Completeness.ProjectionCompile LeanVIPR.Completeness.ViprCompleteness

/-- A sufficient pure-integer theorem in the restricted syntactic tree model:
every infeasible finite rational inequality system over declared integer
variables has a finite refutation tree. -/
def PureIntegerRefTreeComplete : Prop :=
  ∀ (rows : List Le) (intVars : List Nat),
    RowsOnIntVars intVars rows →
    NoIntSolution intVars rows →
    ∃ tree,
      RefTree.Valid (fun idx => idx ∈ intVars) rows tree

/-- Completeness of the restricted pure-integer tree model implies
completeness of the full VIPR proof system. -/
theorem proofSystem_complete_of_pureInteger
    (hpure : PureIntegerRefTreeComplete) :
    ProofSystemComplete := by
  intro base intVars hrows hinfeasible
  let rows := integerRows (normalizedLeRows base) intVars
  have hOnIntVars : RowsOnIntVars intVars rows := by
    exact integerRows_integral (normalizedLeRows base) intVars
  have hNoSolution : NoIntSolution intVars rows := by
    exact integerRows_noIntSolution hrows hinfeasible
  obtain ⟨tree, htree⟩ :=
    hpure rows intVars hOnIntVars hNoSolution
  exact projectedRefTree_proof_complete htree

end LeanVIPR.Completeness.GeneralCompleteness
