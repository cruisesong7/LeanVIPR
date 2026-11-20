module

public import LeanVIPR.Impl.Checker
public import LeanVIPR.Thm.System.Claim
public import LeanVIPR.Thm.System

@[expose] public section

/-!
# Soundness of the array-backed VIPR checker

This module proves the production checker sound directly against the declarative
VIPR proof system. No second executable checker or executable-checker equivalence
theorem is involved.
-/

namespace LeanVIPR.Checker

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.Lower
open LeanVIPR.Parser.Vipr LeanVIPR.Semantics.System

theorem poolEntry_eq (pool : CheckerPool) (i : Nat) :
    poolEntry pool i = pool.toList.getD i sdflt := by
  simp [poolEntry, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem poolRow_eq (pool : CheckerPool) (i : Nat) :
    poolRow pool i = spoolRow pool.toList i := by
  simp [poolRow, spoolRow, poolEntry_eq]

theorem poolAsm_eq (pool : CheckerPool) (i : Nat) :
    poolAsm pool i = spoolAsm pool.toList i := by
  simp [poolAsm, spoolAsm, poolEntry_eq]

theorem resolveRefs_eq (pool : CheckerPool) (comb : List (ℚ × Nat)) :
    resolveRefs pool comb = resolve pool.toList comb := by
  simp [resolveRefs, resolve, poolRow_eq]

theorem referencedAsms_eq (pool : CheckerPool) (comb : List (ℚ × Nat)) :
    referencedAsms pool comb = collectAsms pool.toList comb := by
  induction comb with
  | nil => rfl
  | cons p ps ih => simp [referencedAsms, collectAsms, poolAsm_eq, ih]

theorem entryOf_eq (pool : CheckerPool) (s : SStep) :
    entryOf pool s = sentryOf pool.toList s := by
  cases s with
  | mk stated reason =>
    cases reason <;> simp [entryOf, sentryOf, poolRow_eq, poolAsm_eq,
      referencedAsms_eq]

theorem back?_toList (pool : CheckerPool) :
    pool.back? = pool.toList.getLast? := by
  rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?]
  simp [Array.getElem?_toList]

theorem referencesPast_sound {pool : CheckerPool} {r : SReason}
    (h : referencesPast pool r = true) : ReferencesPast pool.toList r := by
  cases r with
  | asm => trivial
  | lin comb =>
      intro p hp
      simpa using of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | rnd comb =>
      intro p hp
      simpa using of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | uns i1 l1 i2 l2 =>
      simp only [referencesPast, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨by simpa using h.1.1.1, by simpa using h.1.1.2,
        by simpa using h.1.2, by simpa using h.2⟩
  | sol => trivial

/-- Boolean acceptance of one array-backed step implies declarative step validity. -/
theorem stepValid_sound {v : Vipr} {pool : CheckerPool} {s : SStep}
    (h : stepValid v pool s = true) : Vipr.StepValid v pool.toList s := by
  rw [stepValid, Bool.and_eq_true] at h
  refine ⟨referencesPast_sound h.1, ?_⟩
  cases hr : s.reason with
  | asm => trivial
  | lin comb =>
      simp only [ruleCheck, hr] at h
      apply Rule.linCheck_valid_real
      simpa only [resolveRefs_eq] using h.2
  | rnd comb =>
      simp only [ruleCheck, hr] at h
      apply Rule.rndCheck_valid_real
      simpa only [resolveRefs_eq] using h.2
  | uns i1 l1 i2 l2 =>
      simp only [ruleCheck, hr, Bool.and_eq_true] at h
      exact ⟨Rule.dominates_valid_real (by simpa [poolRow_eq] using h.2.1.1),
        Rule.dominates_valid_real (by simpa [poolRow_eq] using h.2.1.2),
        Rule.unsBounds_valid_real (by simpa [poolRow_eq] using h.2.2)⟩
  | sol =>
      simp only [ruleCheck, hr] at h
      exact solReason_sound h.2

theorem replaySteps_refines (v : Vipr) :
    ∀ (pool : CheckerPool) (steps : List SStep) (final : CheckerPool),
      replaySteps? v pool steps = some final →
      Vipr.DerivationValid v pool.toList steps ∧
        final.toList = sfreplay pool.toList steps := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro final h
      simp only [replaySteps?] at h
      cases h
      exact ⟨trivial, by simp [sfreplay]⟩
  | cons s ss ih =>
      intro final h
      simp only [replaySteps?] at h
      by_cases hs : stepValid v pool s = true
      · simp only [hs, ite_true] at h
        have htail := ih (pool.push (entryOf pool s)) final h
        have htailValid :
            Vipr.DerivationValid
              v (pool.toList ++ [sentryOf pool.toList s]) ss := by
          simpa [entryOf_eq] using htail.1
        refine ⟨⟨stepValid_sound hs, htailValid⟩, ?_⟩
        simpa [sfreplay, entryOf_eq] using htail.2
      · simp [hs] at h

theorem initialPool_eq (v : Vipr) :
    (initialPool v).toList = sinitPool (conSLes v) := by
  simp [initialPool, sinitPool, conSLes]

theorem replay_refines {v : Vipr} {final : CheckerPool}
    (h : replay? v = some final) :
    Vipr.DerivationValid v (sinitPool (conSLes v)) (viprSteps v) ∧
      final.toList = sfreplay (sinitPool (conSLes v)) (viprSteps v) := by
  have hrefine := replaySteps_refines v (initialPool v) (viprSteps v) final h
  rw [initialPool_eq] at hrefine
  exact hrefine

/-- A closed entry found by `anyClosed` is a member of the pool. -/
theorem anyClosed_sound {p : SLe → Bool} {pool : CheckerPool}
    (h : anyClosed p pool = true) : ∃ e ∈ pool.toList, e.2 = ∅ ∧ p e.1 = true := by
  unfold anyClosed at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · cases hb : pool.back? with
    | none => simp [hb] at h
    | some e =>
        simp only [hb, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨e, List.mem_of_getLast? (by rw [← back?_toList]; exact hb), h⟩
  · obtain ⟨e, he, hp⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨e, he, hp⟩


theorem finalValid_sound {v : Vipr} {pool : CheckerPool}
    (hpool : pool.toList = sfreplay (sinitPool (conSLes v)) (viprSteps v))
    (h : finalValid v pool = true) : FinalValid v := by
  cases hr : v.rtp with
  | infeas =>
      simp only [FinalValid, hr]
      simp only [finalValid, hr] at h
      obtain ⟨e, he, hclosed, habs⟩ := anyClosed_sound h
      exact ⟨e, hpool ▸ he, hclosed, Rule.isAbsurd_sound_real habs⟩
  | range lb ub =>
      simp only [FinalValid, hr]
      simp only [finalValid, hr] at h
      by_cases hmin : v.objSense = "min"
      · simp only [ite_eq_left hmin] at h ⊢
        cases lb with
        | none => trivial
        | some lower =>
            simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
            obtain ⟨e, he, hclosed, hdom⟩ := anyClosed_sound h.1
            exact ⟨⟨e, hpool ▸ he, hclosed, Rule.dominates_valid_real hdom⟩, h.2⟩
      · by_cases hmax : v.objSense = "max"
        · simp only [ite_eq_right hmin, ite_eq_left hmax] at h ⊢
          cases ub with
          | none => trivial
          | some upper =>
              simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
              obtain ⟨e, he, hclosed, hdom⟩ := anyClosed_sound h.1
              exact ⟨⟨e, hpool ▸ he, hclosed, Rule.dominates_valid_real hdom⟩, h.2⟩
        · simp [hmin, hmax] at h

/-- The executable checker refines the declarative VIPR proof system. -/
theorem checkVipr_refines {v : Vipr} (h : checkVipr v = true) :
    Vipr.ProofValid v := by
  simp only [checkVipr, Bool.and_eq_true] at h
  cases hr : replay? v with
  | none => simp [hr] at h
  | some final =>
      have hrefine := replay_refines (v := v) (final := final) hr
      exact ⟨solSection_sound h.1, hrefine.1,
        finalValid_sound hrefine.2 (by simpa [hr] using h.2)⟩

/-- Main soundness theorem for the production VIPR checker. -/
theorem checkVipr_sound (v : Vipr) (h : checkVipr v = true) :
    Vipr.ClaimValid v :=
  Vipr.proofSystem_sound v (checkVipr_refines h)

/-- A checked infeasible row subset also refutes the original mixed-integer system. -/
theorem checkViprInfeasibleSubset_sound (original sliced : Vipr)
    (hinfeas : sliced.rtp = .infeas)
    (hint : sliced.intVars = original.intVars)
    (hrows : ∀ c ∈ conSLes sliced, c ∈ conSLes original)
    (hcheck : checkVipr sliced = true) :
    ∀ a, Feasible original a → False := by
  intro a hfeas
  have hsound : ∀ a, Feasible sliced a → False := by
    simpa [Vipr.ClaimValid, hinfeas] using checkVipr_sound sliced hcheck
  exact hsound a
    ⟨fun j hj => hfeas.1 j (by simpa [hint] using hj), fun c hc => hfeas.2 c (hrows c hc)⟩

end LeanVIPR.Checker
