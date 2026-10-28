module

public import LeanVIPR.Completeness.AffineHyperplaneRank

@[expose] public section

/-!
# Transporting semantic CG rank derivations

Semantic CG cuts remain valid when their row context is strengthened.  This
file lifts whole finite-rank derivations to larger starting contexts, stopping
early if the strengthened context is already rationally infeasible.
-/

namespace LeanVIPR.Completeness.RankTransport

open LeanVIPR.Cert LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness

theorem prependTargets_mono
    {smaller larger : List Le}
    (targets : List Le)
    (hsubset : ∀ row ∈ smaller, row ∈ larger) :
    ∀ row ∈ prependTargets targets smaller,
      row ∈ prependTargets targets larger := by
  intro row hrow
  rw [prependTargets_eq_reverse_append] at hrow ⊢
  rcases List.mem_append.mp hrow with htarget | hrow
  · exact List.mem_append.mpr (Or.inl htarget)
  · exact List.mem_append.mpr (Or.inr (hsubset row hrow))

/-- A finite semantic CG derivation ending in rational infeasibility can be
replayed from any stronger initial row context. -/
theorem SemanticRankDerivation.refutation_of_weaken
    {intVars : List Nat} {first final : List Le}
    (derivation : SemanticRankDerivation intVars first final)
    (hinfeasible : RatInfeasible final)
    (larger : List Le)
    (hsubset : ∀ row ∈ first, row ∈ larger) :
    Nonempty (SemanticRankRefutation intVars larger) := by
  induction derivation generalizing larger with
  | done rows =>
      exact
        ⟨
          { finalRows := larger
            derivation := .done larger
            infeasible := by
              intro a hlarger
              exact
                hinfeasible a fun row hrow =>
                  hlarger row (hsubset row hrow) }⟩
  | @round rows final head tail ih =>
      by_cases hlarger : RatFeasible larger
      · let lifted : SemanticRound intVars larger :=
          { feasible := hlarger
            targets := head.targets
            valid := by
              intro target htarget
              exact
                (head.valid target htarget).weaken
                  hsubset }
        have hfinalSubset :
            ∀ row ∈ head.finalRows,
              row ∈ lifted.finalRows := by
          exact
            prependTargets_mono head.targets hsubset
        obtain ⟨suffix⟩ :=
          ih hinfeasible lifted.finalRows hfinalSubset
        let initial :
            SemanticRankDerivation intVars larger
              lifted.finalRows :=
          .round lifted (.done lifted.finalRows)
        exact ⟨suffix.prepend initial⟩
      · exact
          ⟨
            { finalRows := larger
              derivation := .done larger
              infeasible := by
                intro a hrows
                exact hlarger ⟨a, hrows⟩ }⟩

/-- A semantic finite-rank refutation is monotone under strengthening its
initial rational relaxation. -/
theorem SemanticRankRefutation.weaken
    {intVars : List Nat} {rows larger : List Le}
    (refutation : SemanticRankRefutation intVars rows)
    (hsubset : ∀ row ∈ rows, row ∈ larger) :
    Nonempty (SemanticRankRefutation intVars larger) :=
  SemanticRankDerivation.refutation_of_weaken
    refutation.derivation refutation.infeasible larger hsubset

end LeanVIPR.Completeness.RankTransport
