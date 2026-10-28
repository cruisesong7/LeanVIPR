module

public import LeanVIPR.Completeness.ChvatalGomory

@[expose] public section

/-!
# A finite-rank criterion for semantic CG closure

Schrijver's finite-rank argument has a finite assembly step independent of
polyhedral geometry.  If each closure round has a finite row description, and
a finite rationally infeasible family of integer-hull inequalities eventually
appears in the iterated descriptions, then some finite iterate is rationally
infeasible.

This file formalizes that assembly step.  The remaining geometric obligation
is to construct such a finite closure operator and prove eventual appearance
of a finite integer-hull description.
-/

namespace LeanVIPR.Completeness.FiniteRankCriterion

open LeanVIPR.Cert LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness

/-- A finite choice of semantic CG cuts for each feasible rational row
context. -/
structure ClosureOperator (intVars : List Nat) where
  targets : List Le → List Le
  valid : ∀ rows, RatFeasible rows → ∀ target ∈ targets rows,
    SemanticCut intVars rows target

def ClosureOperator.next {intVars : List Nat}
    (operator : ClosureOperator intVars) (rows : List Le) : List Le :=
  prependTargets (operator.targets rows) rows

def ClosureOperator.round {intVars : List Nat}
    (operator : ClosureOperator intVars) (rows : List Le)
    (hfeasible : RatFeasible rows) :
    SemanticRound intVars rows where
  feasible := hfeasible
  targets := operator.targets rows
  valid := operator.valid rows hfeasible

@[simp]
theorem ClosureOperator.round_finalRows {intVars : List Nat}
    (operator : ClosureOperator intVars) (rows : List Le)
    (hfeasible : RatFeasible rows) :
    (operator.round rows hfeasible).finalRows = operator.next rows := rfl

theorem mem_prependTargets_right {row : Le} (targets rows : List Le)
    (hrow : row ∈ rows) :
    row ∈ prependTargets targets rows := by
  induction targets generalizing rows with
  | nil => exact hrow
  | cons target targets ih =>
      exact ih (target :: rows) (by simp [hrow])

theorem ClosureOperator.mem_next_of_mem {intVars : List Nat}
    (operator : ClosureOperator intVars) {rows : List Le} {row : Le}
    (hrow : row ∈ rows) :
    row ∈ operator.next rows :=
  mem_prependTargets_right (operator.targets rows) rows hrow

def ClosureOperator.iterate {intVars : List Nat}
    (operator : ClosureOperator intVars) (initial : List Le) :
    Nat → List Le
  | 0 => initial
  | n + 1 => operator.next (operator.iterate initial n)

theorem ClosureOperator.iterate_step_subset {intVars : List Nat}
    (operator : ClosureOperator intVars) (initial : List Le) (n : Nat) :
    ∀ row ∈ operator.iterate initial n,
      row ∈ operator.iterate initial (n + 1) := by
  intro row hrow
  exact operator.mem_next_of_mem hrow

theorem ClosureOperator.iterate_subset_of_le {intVars : List Nat}
    (operator : ClosureOperator intVars) (initial : List Le)
    {m n : Nat} (hmn : m ≤ n) :
    ∀ row ∈ operator.iterate initial m,
      row ∈ operator.iterate initial n := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact fun _ hrow => hrow
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact fun _ hrow => hrow
      · have hmn' : m ≤ n := by omega
        intro row hrow
        exact operator.iterate_step_subset initial n row
          (ih hmn' row hrow)

theorem ClosureOperator.feasible_previous {intVars : List Nat}
    (operator : ClosureOperator intVars) (initial : List Le) {n : Nat}
    (hfeasible : RatFeasible (operator.iterate initial (n + 1))) :
    RatFeasible (operator.iterate initial n) := by
  obtain ⟨a, hrows⟩ := hfeasible
  exact ⟨a, fun row hrow =>
    hrows row (operator.iterate_step_subset initial n row hrow)⟩

def ClosureOperator.derivationTo {intVars : List Nat}
    (operator : ClosureOperator intVars) (initial : List Le) :
    (n : Nat) →
    RatFeasible (operator.iterate initial n) →
    SemanticRankDerivation intVars initial (operator.iterate initial n)
  | 0, _ => .done initial
  | n + 1, hfeasible =>
      let hprevious := operator.feasible_previous initial hfeasible
      let first := operator.derivationTo initial n hprevious
      let head := operator.round (operator.iterate initial n) hprevious
      first.trans (.round head (.done head.finalRows))

theorem ClosureOperator.refutation_of_iterate_infeasible
    {intVars : List Nat} (operator : ClosureOperator intVars)
    (initial : List Le) :
    ∀ n,
      RatInfeasible (operator.iterate initial n) →
      Nonempty (SemanticRankRefutation intVars initial) := by
  intro n
  induction n with
  | zero =>
      intro hinfeasible
      exact ⟨
        { finalRows := initial
          derivation := .done initial
          infeasible := hinfeasible }⟩
  | succ n ih =>
      intro hinfeasible
      by_cases hprevious :
          RatFeasible (operator.iterate initial n)
      · let first := operator.derivationTo initial n hprevious
        let head :=
          operator.round (operator.iterate initial n) hprevious
        let derivation :
            SemanticRankDerivation intVars initial
              (operator.iterate initial (n + 1)) :=
          first.trans (.round head (.done head.finalRows))
        exact ⟨
          { finalRows := operator.iterate initial (n + 1)
            derivation := derivation
            infeasible := hinfeasible }⟩
      · have hinfeasiblePrevious :
            RatInfeasible (operator.iterate initial n) := by
          intro a hrows
          exact hprevious ⟨a, hrows⟩
        exact ih hinfeasiblePrevious

theorem ClosureOperator.exists_common_rank
    {intVars : List Nat} (operator : ClosureOperator intVars)
    (initial targets : List Le)
    (heventual :
      ∀ target ∈ targets,
        ∃ n, target ∈ operator.iterate initial n) :
    ∃ n, ∀ target ∈ targets,
      target ∈ operator.iterate initial n := by
  induction targets with
  | nil =>
      exact ⟨0, by simp⟩
  | cons target targets ih =>
      obtain ⟨targetRank, htargetRank⟩ :=
        heventual target (by simp)
      obtain ⟨tailRank, htailRank⟩ :=
        ih fun row hrow => heventual row (by simp [hrow])
      refine ⟨max targetRank tailRank, ?_⟩
      intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · exact operator.iterate_subset_of_le initial
          (Nat.le_max_left targetRank tailRank) row htargetRank
      · exact operator.iterate_subset_of_le initial
          (Nat.le_max_right targetRank tailRank) row
          (htailRank row hrow)

/-- If finitely many jointly infeasible rows all occur at finite ranks of one
finitely described semantic closure sequence, then a finite semantic CG-rank
refutation exists. -/
theorem ClosureOperator.refutation_of_eventually_infeasible
    {intVars : List Nat} (operator : ClosureOperator intVars)
    (initial targets : List Le)
    (hinfeasible : RatInfeasible targets)
    (heventual :
      ∀ target ∈ targets,
        ∃ n, target ∈ operator.iterate initial n) :
    Nonempty (SemanticRankRefutation intVars initial) := by
  obtain ⟨n, htargets⟩ :=
    operator.exists_common_rank initial targets heventual
  have hiterate :
      RatInfeasible (operator.iterate initial n) := by
    intro a hrows
    exact hinfeasible a fun target htarget =>
      hrows target (htargets target htarget)
  exact operator.refutation_of_iterate_infeasible initial n hiterate

end LeanVIPR.Completeness.FiniteRankCriterion
