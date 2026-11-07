module

public import LeanVIPR.Thm.Checker.Sound
public import LeanVIPR.Thm.System.RuleComplete

@[expose] public section

/-!
# The checker decides the declarative proof system

`checkVipr_refines` shows that acceptance by the array-backed checker implies the
declarative predicate `Vipr.ProofValid`. This module proves the converse: every
declaratively valid certificate is accepted. Hence `checkVipr v = true` holds
exactly when `Vipr.ProofValid v` does, so the checker never rejects a certificate
that is valid under the declarative rules.
-/

namespace LeanVIPR.Checker

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.Lower
open LeanVIPR.Parser.Vipr LeanVIPR.Semantics.System LeanVIPR.Semantics.RuleComplete

/-! ## Solutions and `{ sol }` rows -/

theorem satQ_complete_solution {c : SLe} {s : NamedSolution}
    (h : satReal c (solutionValuation s)) :
    satQ c (sparseValuation s.2) = true := by
  simp only [satReal, evalReal_solution] at h
  simp only [satQ]
  split_ifs at h ⊢ <;> exact decide_eq_true (by exact_mod_cast h)

theorem solutionFeasible_complete {v : Vipr} {s : NamedSolution}
    (h : Feasible v (solutionValuation s)) : solutionFeasible v s = true := by
  rw [solutionFeasible, Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun j hj => ?_, List.all_eq_true.mpr fun c hc => ?_⟩
  · obtain ⟨z, hz⟩ := h.1 j hj
    change ((sparseValuation s.2 j : ℚ) : ℝ) = (z : ℝ) at hz
    exact isIntVal_complete ⟨z, by exact_mod_cast hz⟩
  · exact satQ_complete_solution (h.2 c hc)

theorem allSolutions_complete {v : Vipr} (h : AllSolutionsValid v) :
    allSolutions v = true :=
  List.all_eq_true.mpr fun s hs => solutionFeasible_complete (h s hs)

theorem solSection_complete {v : Vipr} (h : SolSectionValid v) :
    solSection v = true := by
  cases hr : v.rtp with
  | infeas =>
      have hsols : v.sols.toList = [] := by simpa [SolSectionValid, hr] using h
      simp [solSection, hr, hsols]
  | range lb ub =>
      simp only [SolSectionValid, hr] at h
      obtain ⟨hall, hwitness⟩ := h
      simp only [solSection, hr, allSolutions_complete hall, Bool.true_and]
      by_cases hmin : v.objSense = "min"
      · simp only [hmin, ite_true] at hwitness ⊢
        cases ub with
        | none => rfl
        | some upper =>
            obtain ⟨s, hs, hle⟩ := hwitness
            exact List.any_eq_true.mpr ⟨s, hs, decide_eq_true hle⟩
      · by_cases hmax : v.objSense = "max"
        · simp only [hmax, ite_true] at hwitness ⊢
          cases lb with
          | none => rfl
          | some lower =>
              obtain ⟨s, hs, hle⟩ := hwitness
              exact List.any_eq_true.mpr ⟨s, hs, decide_eq_true hle⟩
        · simp [hmin, hmax] at hwitness

theorem solReason_complete {v : Vipr} {stated : SLe}
    (h : SolReasonValid v stated) : solReason v stated = true := by
  unfold SolReasonValid at h
  unfold solReason
  by_cases hmin : v.objSense = "min"
  · simp only [hmin, ite_true] at h ⊢
    obtain ⟨s, hs, hdom⟩ := h
    exact List.any_eq_true.mpr ⟨s, hs, domSLe_complete hdom⟩
  · by_cases hmax : v.objSense = "max"
    · simp only [hmax, ite_true] at h ⊢
      obtain ⟨s, hs, hdom⟩ := h
      exact List.any_eq_true.mpr ⟨s, hs, domSLe_complete hdom⟩
    · simp [hmin, hmax] at h

/-! ## Single steps and replay -/

theorem refsPast_complete {pool : CheckerPool} {r : SReason}
    (h : ReferencesPast pool.toList r) : refsPast pool r = true := by
  cases r with
  | asm => rfl
  | lin comb =>
      exact List.all_eq_true.mpr fun p hp => decide_eq_true (by simpa using h p hp)
  | rnd comb =>
      exact List.all_eq_true.mpr fun p hp => decide_eq_true (by simpa using h p hp)
  | uns i1 l1 i2 l2 =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only [Array.length_toList] at h1 h2 h3 h4
      simp [refsPast, h1, h2, h3, h4]
  | sol => rfl

/-- Declarative step validity implies Boolean acceptance of the array-backed step. -/
theorem stepValid_complete {v : Vipr} {pool : CheckerPool} {s : SStep}
    (h : Vipr.StepValid v pool.toList s) : stepValid v pool s = true := by
  obtain ⟨hrefs, hrule⟩ := h
  rw [stepValid, Bool.and_eq_true]
  refine ⟨refsPast_complete hrefs, ?_⟩
  cases hr : s.reason with
  | asm => simp [ruleCheck, hr]
  | lin comb =>
      simp only [ruleCheck, hr] at hrule ⊢
      rw [resolveRefs_eq]
      exact linCheck_complete hrule
  | rnd comb =>
      simp only [ruleCheck, hr] at hrule ⊢
      rw [resolveRefs_eq]
      exact rndCheck_complete hrule
  | uns i1 l1 i2 l2 =>
      simp only [ruleCheck, hr] at hrule ⊢
      obtain ⟨hdom1, hdom2, hbounds⟩ := hrule
      simp only [poolRow_eq, Bool.and_eq_true]
      exact ⟨⟨domSLe_complete hdom1, domSLe_complete hdom2⟩,
        unsBounds_complete hbounds⟩
  | sol =>
      simp only [ruleCheck, hr] at hrule ⊢
      exact solReason_complete hrule

/-- A declaratively valid derivation replays successfully, producing the
declarative pool. -/
theorem replaySteps_complete (v : Vipr) :
    ∀ (pool : CheckerPool) (steps : List SStep),
      Vipr.DerivationValid v pool.toList steps →
      ∃ final, replaySteps? v pool steps = some final ∧
        final.toList = sfreplay pool.toList steps := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro _
      exact ⟨pool, rfl, by simp [sfreplay]⟩
  | cons s ss ih =>
      intro h
      obtain ⟨hstep, htail⟩ := h
      have hpush : (pool.push (entryOf pool s)).toList =
          pool.toList ++ [sentryOf pool.toList s] := by
        simp [entryOf_eq]
      obtain ⟨final, hfinal, heq⟩ :=
        ih (pool.push (entryOf pool s)) (by rw [hpush]; exact htail)
      refine ⟨final, ?_, ?_⟩
      · simp only [replaySteps?, stepValid_complete hstep, ite_true]
        exact hfinal
      · rw [heq, hpush]
        rfl

theorem replay_complete {v : Vipr}
    (h : Vipr.DerivationValid v (sinitPool (conSLes v)) (viprSteps v)) :
    replay? v = some (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? := by
  obtain ⟨final, hfinal, heq⟩ :=
    replaySteps_complete v (initialPool v) (viprSteps v) (by rwa [initialPool_eq])
  unfold replay?
  rw [hfinal, Option.map_some, back?_toList, heq, initialPool_eq]

/-! ## Final claim and the whole certificate -/

theorem finalValid_complete {v : Vipr} (h : FinalValid v) :
    finalValid v (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = true := by
  cases hr : v.rtp with
  | infeas =>
      simp only [FinalValid, hr] at h
      obtain ⟨e, hlast, hclosed, habs⟩ := h
      simp [finalValid, hr, hlast, closedAbsurd, hclosed, isAbsurd_complete habs]
  | range lb ub =>
      simp only [FinalValid, hr] at h
      by_cases hmin : v.objSense = "min"
      · simp only [hmin, ite_true] at h
        cases lb with
        | none => simp [finalValid, hr, hmin]
        | some lower =>
            obtain ⟨e, hlast, hclosed, hdom⟩ := h
            simp [finalValid, hr, hmin, hlast, closedDominates, hclosed,
              domSLe_complete hdom]
      · by_cases hmax : v.objSense = "max"
        · simp only [hmax, ite_true] at h
          cases ub with
          | none => simp [finalValid, hr, hmax]
          | some upper =>
              obtain ⟨e, hlast, hclosed, hdom⟩ := h
              simp [finalValid, hr, hmax, hlast, closedDominates, hclosed,
                domSLe_complete hdom]
        · simp [hmin, hmax] at h

/-- Every declaratively valid certificate is accepted by the checker. -/
theorem checkVipr_complete {v : Vipr} (h : Vipr.ProofValid v) : checkVipr v = true := by
  obtain ⟨hsols, hder, hfinal⟩ := h
  simp only [checkVipr, Bool.and_eq_true]
  refine ⟨solSection_complete hsols, ?_⟩
  rw [replay_complete hder]
  exact finalValid_complete hfinal

end LeanVIPR.Checker
