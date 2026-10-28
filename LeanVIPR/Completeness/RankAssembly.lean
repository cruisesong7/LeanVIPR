module

public import LeanVIPR.Completeness.RankTransport

@[expose] public section

/-!
# Assembling pointwise finite-rank consequences

The classical finite-CG-rank theorem is naturally pointwise: every integral
inequality valid on the integer points occurs after finitely many CG rounds.
Different inequalities may be witnessed by different finite derivations.

This file proves that pointwise statement is sufficient.  A derivation of one
target can be transported to the row context accumulated so far, and finitely
many such transported derivations can be concatenated.  If the targets are
jointly rationally infeasible, the assembled derivation is a semantic
finite-rank refutation.
-/

namespace LeanVIPR.Completeness.RankAssembly

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
  LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.FiniteRankCriterion
  LeanVIPR.Completeness.IntegerHullTargets
  LeanVIPR.Completeness.IntegerProjection
  LeanVIPR.Completeness.RankTransport
  LeanVIPR.Completeness.ValidInequalityCompleteness
  LeanVIPR.Completeness.ViprCompleteness

/-- A finite semantic CG derivation in which one specified target occurs. -/
structure SemanticRankConsequence
    (intVars : List Nat) (rows : List Le) (target : Le) where
  finalRows : List Le
  derivation : SemanticRankDerivation intVars rows finalRows
  mem_target : target ∈ finalRows

/-- A derivation transported to a stronger initial row context.  Its result
contains both the old derivation's result and the stronger initial context. -/
structure LiftedDerivation
    (intVars : List Nat) (oldFinal newFirst : List Le) where
  finalRows : List Le
  derivation : SemanticRankDerivation intVars newFirst finalRows
  oldFinal_subset : ∀ row ∈ oldFinal, row ∈ finalRows
  newFirst_subset : ∀ row ∈ newFirst, row ∈ finalRows

/-- Transport a semantic rank derivation to a stronger initial context.  The
stronger context may already become rationally infeasible before the original
derivation finishes; otherwise the transported result retains all old final
rows and all rows of the stronger context. -/
theorem SemanticRankDerivation.lift_or_refute
    {intVars : List Nat} {first final : List Le}
    (derivation : SemanticRankDerivation intVars first final)
    (larger : List Le)
    (hsubset : ∀ row ∈ first, row ∈ larger) :
    Nonempty (SemanticRankRefutation intVars larger) ∨
      Nonempty (LiftedDerivation intVars final larger) := by
  induction derivation generalizing larger with
  | done rows =>
      exact
        Or.inr
          ⟨
            { finalRows := larger
              derivation := .done larger
              oldFinal_subset := hsubset
              newFirst_subset := fun _ hrow => hrow }⟩
  | @round rows final head tail ih =>
      by_cases hlarger : RatFeasible larger
      · let lifted : SemanticRound intVars larger :=
          { feasible := hlarger
            targets := head.targets
            valid := by
              intro target htarget
              exact (head.valid target htarget).weaken hsubset }
        have hfinalSubset :
            ∀ row ∈ head.finalRows, row ∈ lifted.finalRows :=
          prependTargets_mono head.targets hsubset
        rcases ih lifted.finalRows hfinalSubset with hrefutation | htail
        · obtain ⟨refutation⟩ := hrefutation
          let initial :
              SemanticRankDerivation intVars larger lifted.finalRows :=
            .round lifted (.done lifted.finalRows)
          exact Or.inl ⟨refutation.prepend initial⟩
        · obtain ⟨liftedTail⟩ := htail
          exact
            Or.inr
              ⟨
                { finalRows := liftedTail.finalRows
                  derivation := .round lifted liftedTail.derivation
                  oldFinal_subset := liftedTail.oldFinal_subset
                  newFirst_subset := by
                    intro row hrow
                    apply liftedTail.newFirst_subset
                    exact mem_prependTargets_right head.targets larger hrow }⟩
      · exact
          Or.inl
            ⟨
              { finalRows := larger
                derivation := .done larger
                infeasible := by
                  intro a hrows
                  exact hlarger ⟨a, hrows⟩ }⟩

/-- A derivation from `current` whose result contains all requested targets
and all rows already present in `current`. -/
structure TargetsDerivation
    (intVars : List Nat) (current targets : List Le) where
  finalRows : List Le
  derivation : SemanticRankDerivation intVars current finalRows
  targets_subset : ∀ row ∈ targets, row ∈ finalRows
  current_subset : ∀ row ∈ current, row ∈ finalRows

/-- Assemble independently witnessed pointwise consequences, transporting
each next witness to the row context accumulated by its predecessors. -/
theorem deriveTargets_or_refute
    {intVars : List Nat} {initial targets current : List Le}
    (hconsequence :
      ∀ target ∈ targets,
        Nonempty (SemanticRankConsequence intVars initial target))
    (hsubset : ∀ row ∈ initial, row ∈ current) :
    Nonempty (SemanticRankRefutation intVars current) ∨
      Nonempty (TargetsDerivation intVars current targets) := by
  induction targets generalizing current with
  | nil =>
      exact
        Or.inr
          ⟨
            { finalRows := current
              derivation := .done current
              targets_subset := by simp
              current_subset := fun _ hrow => hrow }⟩
  | cons target targets ih =>
      obtain ⟨consequence⟩ :=
        hconsequence target (by simp)
      rcases
          LeanVIPR.Completeness.RankAssembly.SemanticRankDerivation.lift_or_refute
            consequence.derivation current hsubset with
        hrefutation | hlifted
      · exact Or.inl hrefutation
      · obtain ⟨lifted⟩ := hlifted
        have htarget :
            target ∈ lifted.finalRows :=
          lifted.oldFinal_subset target consequence.mem_target
        have hinitial :
            ∀ row ∈ initial, row ∈ lifted.finalRows := by
          intro row hrow
          exact lifted.newFirst_subset row (hsubset row hrow)
        rcases
            ih
              (fun candidate hcandidate =>
                hconsequence candidate (by simp [hcandidate]))
              hinitial with
          hrefutation | htail
        · obtain ⟨refutation⟩ := hrefutation
          exact Or.inl ⟨refutation.prepend lifted.derivation⟩
        · obtain ⟨tail⟩ := htail
          exact
            Or.inr
              ⟨
                { finalRows := tail.finalRows
                  derivation := lifted.derivation.trans tail.derivation
                  targets_subset := by
                    intro row hrow
                    rcases List.mem_cons.mp hrow with rfl | hrow
                    · exact tail.current_subset _ htarget
                    · exact tail.targets_subset row hrow
                  current_subset := by
                    intro row hrow
                    exact
                      tail.current_subset row
                        (lifted.newFirst_subset row hrow) }⟩

/-- Finitely many jointly infeasible pointwise finite-rank consequences give
a semantic finite-rank refutation. -/
theorem refutation_of_finite_consequences
    {intVars : List Nat} {rows targets : List Le}
    (hconsequence :
      ∀ target ∈ targets,
        Nonempty (SemanticRankConsequence intVars rows target))
    (hinfeasible : RatInfeasible targets) :
    Nonempty (SemanticRankRefutation intVars rows) := by
  rcases
      deriveTargets_or_refute hconsequence
        (fun _ hrow => hrow) with
    hrefutation | hderivation
  · exact hrefutation
  · obtain ⟨derivation⟩ := hderivation
    exact
      ⟨SemanticRankRefutation.of_infeasible_subset
        derivation.derivation hinfeasible derivation.targets_subset⟩

/-- For finitely many targets, pointwise outcomes can be collected: either
one target already supplies a refutation, or every target supplies a finite
rank consequence. -/
theorem collectConsequences_or_refute
    {intVars : List Nat} {rows targets : List Le}
    (houtcome :
      ∀ target ∈ targets,
        Nonempty (SemanticRankRefutation intVars rows) ∨
          Nonempty (SemanticRankConsequence intVars rows target)) :
    Nonempty (SemanticRankRefutation intVars rows) ∨
      (∀ target ∈ targets,
        Nonempty (SemanticRankConsequence intVars rows target)) := by
  induction targets with
  | nil =>
      exact Or.inr (by simp)
  | cons target targets ih =>
      rcases houtcome target (by simp) with hrefutation | hconsequence
      · exact Or.inl hrefutation
      · rcases
          ih
            (fun candidate hcandidate =>
              houtcome candidate (by simp [hcandidate])) with
        hrefutation | htail
        · exact Or.inl hrefutation
        · exact
            Or.inr fun candidate hcandidate => by
              rcases List.mem_cons.mp hcandidate with rfl | hcandidate
              · exact hconsequence
              · exact htail candidate hcandidate

/-- Jointly infeasible targets whose pointwise finite-rank outcomes may stop
early with a refutation still give one semantic finite-rank refutation. -/
theorem refutation_of_finite_outcomes
    {intVars : List Nat} {rows targets : List Le}
    (houtcome :
      ∀ target ∈ targets,
        Nonempty (SemanticRankRefutation intVars rows) ∨
          Nonempty (SemanticRankConsequence intVars rows target))
    (hinfeasible : RatInfeasible targets) :
    Nonempty (SemanticRankRefutation intVars rows) := by
  rcases collectConsequences_or_refute houtcome with
    hrefutation | hconsequence
  · exact hrefutation
  · exact refutation_of_finite_consequences hconsequence hinfeasible

/-- Pointwise form of the remaining classical finite-CG-rank theorem: every
integral inequality valid on the original mixed-integer points either has
some finite semantic CG derivation from the original rational relaxation, or
an earlier closure round is already rationally infeasible. -/
def IntegerValidFiniteRank : Prop :=
  ∀ (rows : List Le) (intVars : List Nat) (target : Le),
    RowsOnIntVars intVars rows →
    FormIntegralReal intVars target.form →
    IsIntVal target.rhs →
    (∀ a : Valuation,
      (∀ idx ∈ intVars, IsIntVal (a idx)) →
      (∀ row ∈ rows, Le.sat row a) →
      Le.sat target a) →
    Nonempty (SemanticRankRefutation intVars rows) ∨
      Nonempty (SemanticRankConsequence intVars rows target)

/-- Pointwise finite CG rank suffices for semantic refutation completeness. -/
theorem semanticRank_complete_of_integerValidFiniteRank
    (hrank : IntegerValidFiniteRank) :
    ∀ (rows : List Le) (intVars : List Nat),
      RowsOnIntVars intVars rows →
      NoIntSolution intVars rows →
      Nonempty (SemanticRankRefutation intVars rows) := by
  intro rows intVars hrows hno
  obtain
      ⟨targets, hinfeasible, _, hintegral, hrhs, hvalid⟩ :=
    exists_finite_integral_integerHull_targets hrows hno
  apply refutation_of_finite_outcomes
  · intro target htarget
    exact
      hrank rows intVars target hrows
        (hintegral target htarget)
        (hrhs target htarget)
        (hvalid target htarget)
  · exact hinfeasible

/-- Pointwise finite CG rank closes the verified compilation chain and yields
full VIPR proof-system completeness. -/
theorem proofSystem_complete_of_integerValidFiniteRank
    (hrank : IntegerValidFiniteRank) :
    ProofSystemComplete := by
  apply proofSystem_complete_of_semanticRank
  exact semanticRank_complete_of_integerValidFiniteRank hrank

end LeanVIPR.Completeness.RankAssembly
