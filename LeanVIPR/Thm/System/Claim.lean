module

public import LeanVIPR.Impl.Checker.Solution
public import LeanVIPR.Thm.System

@[expose] public section

/-!
# The claim semantics is sound

That the declarative proof system of `LeanVIPR.Spec.Semantics.System` establishes the claim of
`LeanVIPR.Spec.Semantics.Claim`, and that the executable solution checks of
`LeanVIPR.Impl.Checker.Solution` decide it. `ClaimValid.optimal_within` is the reading to quote:
every optimal value lies within the claimed range.
-/

namespace LeanVIPR.Parser.Vipr

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.System
open LeanVIPR.Semantics.Lower


theorem candidate_feasible {v : Vipr} {a : RealValuation} (h : Candidate v a) :
    Feasible v a := by
  cases hr : v.rtp with
  | infeas => simpa [Candidate, hr] using h
  | range lb ub =>
      exact (show Feasible v a ∧ SolBounded v a from by simpa [Candidate, hr] using h).1

/-- Soundness of a `{ sol }` derivation row.  For infeasibility certificates the
solution set is empty, so this rule cannot be valid.  For range certificates it
holds at every valuation that is no worse than the referenced solution. -/
theorem solReasonValid_sound {v : Vipr} {stated : SLe} {a : RealValuation}
    (hsols : SolSectionValid v) (hcand : Candidate v a)
    (hreason : SolReasonValid v stated) : satReal stated a := by
  cases hr : v.rtp with
  | infeas =>
      have hempty : v.sols.toList = [] := by
        simpa [SolSectionValid, hr] using hsols
      simp only [SolReasonValid] at hreason
      split_ifs at hreason with hmin hmax
      · obtain ⟨s, hs, _⟩ := hreason
        rw [hempty] at hs
        simp at hs
      · obtain ⟨s, hs, _⟩ := hreason
        rw [hempty] at hs
        simp at hs
  | range lb ub =>
      have hall : AllSolutionsValid v :=
        (show AllSolutionsValid v ∧ _ from by
          simpa [SolSectionValid, hr] using hsols).1
      have hbounded : SolBounded v a :=
        (show Feasible v a ∧ SolBounded v a from by
          simpa [Candidate, hr] using hcand).2
      simp only [SolReasonValid] at hreason
      split_ifs at hreason with hmin hmax
      · obtain ⟨s, hs, hdom⟩ := hreason
        have hall' : ∀ t ∈ v.sols.toList, objectiveReal v a ≤ (objectiveQ v t : ℝ) := by
          simpa [SolBounded, hmin] using hbounded
        have hle := hall' s hs
        exact dominates_sound hdom (by
          simpa [satReal, objectiveReal] using hle)
      · obtain ⟨s, hs, hdom⟩ := hreason
        have hall' : ∀ t ∈ v.sols.toList, (objectiveQ v t : ℝ) ≤ objectiveReal v a := by
          simpa [SolBounded, hmin, hmax] using hbounded
        have hge := hall' s hs
        exact dominates_sound hdom (by
          simpa [satReal, objectiveReal] using hge)

/-- Every entry produced by a declaratively valid full-result replay is sound at
the relevant candidate valuations: feasible valuations for infeasibility results,
and optimal valuations for range results. -/
theorem replay_sound (v : Vipr) (a : RealValuation)
    (hsols : SolSectionValid v) (hcand : Candidate v a) :
    ∀ (pool : SPool) (steps : List SStep),
      DerivationValid v pool steps →
      (∀ e ∈ pool, EntryHolds (conSLes v) a e) →
      ∀ e ∈ sfreplay pool steps, EntryHolds (conSLes v) a e := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro _ hpool
      simpa [sfreplay] using hpool
  | cons s ss ih =>
      intro hv hpool
      obtain ⟨hstep, hrest⟩ := hv
      refine ih (pool ++ [sentryOf pool s]) hrest ?_
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hpool e he
      · rw [List.mem_singleton.mp he]
        obtain ⟨_, hrule⟩ := hstep
        cases hr : s.reason with
        | asm =>
            simp only [sentryOf, hr]
            intro _ hS
            exact hS s.stated (by simp)
        | lin comb =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro hbase hS
            refine linValid_sound hrule (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact System.spoolRow_holds (conSLes v) a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | rnd comb =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro hbase hS
            refine rndValid_sound hrule (candidate_feasible hcand).1 (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact System.spoolRow_holds (conSLes v) a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | uns i1 l1 i2 l2 =>
            simp only [hr] at hrule
            obtain ⟨hdom1, hdom2, hbnd⟩ := hrule
            simp only [sentryOf, hr]
            intro hbase hS
            rcases complementaryBounds_split hbnd (candidate_feasible hcand).1 with hb1 | hb2
            · refine dominates_sound hdom1 ?_
              refine System.spoolRow_holds (conSLes v) a pool hpool i1 hbase
                (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l1
              · rw [hteq]
                exact hb1
              · exact hS t (Finset.mem_union_left _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
            · refine dominates_sound hdom2 ?_
              refine System.spoolRow_holds (conSLes v) a pool hpool i2 hbase
                (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l2
              · rw [hteq]
                exact hb2
              · exact hS t (Finset.mem_union_right _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
        | sol =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro _ _
            exact solReasonValid_sound hsols hcand hrule

private theorem closedFinal_holds {v : Vipr} {a : RealValuation}
    (hsols : SolSectionValid v) (hcand : Candidate v a)
    (hder : DerivationValid v (sinitPool (conSLes v)) (viprSteps v))
    {e : SLe × SAsm}
    (hlast : (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e)
    (hclosed : e.2 = ∅) : satReal e.1 a := by
  have hall := replay_sound v a hsols hcand
    (sinitPool (conSLes v)) (viprSteps v) hder
    (initialPool_holds (conSLes v) a)
  have he : EntryHolds (conSLes v) a e := hall e (List.mem_of_getLast? hlast)
  exact he (candidate_feasible hcand).2 (by simp [hclosed])

private theorem list_exists_min {α : Type} (f : α → ℚ) :
    ∀ l : List α, l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, f x ≤ f y
  | [], h => absurd rfl h
  | x :: rest, _ => by
      by_cases hrest : rest = []
      · subst hrest
        exact ⟨x, by simp, by simp⟩
      · obtain ⟨m, hm, hmin⟩ := list_exists_min f rest hrest
        by_cases hx : f x ≤ f m
        · refine ⟨x, by simp, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact le_rfl
          · exact hx.trans (hmin y hy)
        · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact (lt_of_not_ge hx).le
          · exact hmin y hy

/-- A finite nonempty solution list has a solution of least objective value. -/
private theorem exists_min_solution (v : Vipr) (hne : v.sols.toList ≠ []) :
    ∃ s ∈ v.sols.toList, ∀ t ∈ v.sols.toList, objectiveQ v s ≤ objectiveQ v t :=
  list_exists_min (objectiveQ v) _ hne

private theorem exists_max_solution (v : Vipr) (hne : v.sols.toList ≠ []) :
    ∃ s ∈ v.sols.toList, ∀ t ∈ v.sols.toList, objectiveQ v t ≤ objectiveQ v s := by
  obtain ⟨s, hs, hmin⟩ := list_exists_min (fun s => -objectiveQ v s) _ hne
  exact ⟨s, hs, fun t ht => neg_le_neg_iff.mp (hmin t ht)⟩

/-- Soundness of the full declarative VIPR proof system, including `SOL`,
`{ sol }`, infeasibility results, and objective ranges. -/
theorem proofSystem_sound (v : Vipr)
    (hvalid : ProofValid v) : ClaimValid v := by
  obtain ⟨hsols, hder, hfinal⟩ := hvalid
  cases hr : v.rtp with
  | infeas =>
      rw [ClaimValid, hr]
      intro a hfeas
      have hcand : Candidate v a := by
        simpa [Candidate, hr] using hfeas
      obtain ⟨e, hlast, hclosed, habs⟩ := by
        simpa only [FinalValid, hr] using hfinal
      exact System.absurd_unsat habs a
        (closedFinal_holds hsols hcand hder hlast hclosed)
  | range lb ub =>
      rw [ClaimValid, hr]
      refine ⟨hsols, ?_⟩
      have hall : AllSolutionsValid v :=
        (show AllSolutionsValid v ∧ _ from by
          simpa [SolSectionValid, hr] using hsols).1
      have hcandOf : ∀ a, Feasible v a → SolBounded v a → Candidate v a := by
        intro a hfeas hb
        simpa [Candidate, hr] using And.intro hfeas hb
      unfold RangeBoundValid
      by_cases hmin : v.objSense = "min"
      · rw [ite_eq_left hmin]
        cases lb with
        | none => trivial
        | some lower =>
            have hfinalData := hfinal
            simp only [FinalValid, hr, ite_eq_left hmin] at hfinalData
            obtain ⟨e, hlast, hclosed, hdom⟩ := hfinalData
            -- the closed final row holds at every candidate valuation
            have hat : ∀ a, Candidate v a → (lower : ℝ) ≤ objectiveReal v a := by
              intro a hcand
              have hgoal := System.dominates_sound hdom
                (closedFinal_holds hsols hcand hder hlast hclosed)
              simpa [objectiveLowerRow, satReal, objectiveReal] using hgoal
            intro a hfeas
            by_cases hb : SolBounded v a
            · exact hat a (hcandOf a hfeas hb)
            · -- some listed solution is strictly better than `a`; the best one is a
              -- candidate, and it bounds `a` from below
              simp only [SolBounded, ite_eq_left hmin, not_forall, not_le] at hb
              obtain ⟨t, ht, hlt⟩ := hb
              have hne : v.sols.toList ≠ [] := List.ne_nil_of_mem ht
              obtain ⟨s, hs, hsmin⟩ := exists_min_solution v hne
              have hsCand : Candidate v (solutionValuation s) := by
                refine hcandOf _ (hall s hs) ?_
                simp only [SolBounded, ite_eq_left hmin, objectiveReal_solution]
                exact fun u hu => by exact_mod_cast hsmin u hu
              have hs_le := hat _ hsCand
              rw [objectiveReal_solution] at hs_le
              have hst : (objectiveQ v s : ℝ) ≤ objectiveQ v t := by
                exact_mod_cast hsmin t ht
              linarith
      · rw [ite_eq_right hmin]
        by_cases hmax : v.objSense = "max"
        · rw [ite_eq_left hmax]
          cases ub with
          | none => trivial
          | some upper =>
              have hfinalData := hfinal
              simp only [FinalValid, hr, ite_eq_right hmin, ite_eq_left hmax] at hfinalData
              obtain ⟨e, hlast, hclosed, hdom⟩ := hfinalData
              have hat : ∀ a, Candidate v a → objectiveReal v a ≤ (upper : ℝ) := by
                intro a hcand
                have hgoal := System.dominates_sound hdom
                  (closedFinal_holds hsols hcand hder hlast hclosed)
                simpa [objectiveUpperRow, satReal, objectiveReal] using hgoal
              intro a hfeas
              by_cases hb : SolBounded v a
              · exact hat a (hcandOf a hfeas hb)
              · simp only [SolBounded, ite_eq_right hmin, ite_eq_left hmax, not_forall,
                  not_le] at hb
                obtain ⟨t, ht, hlt⟩ := hb
                have hne : v.sols.toList ≠ [] := List.ne_nil_of_mem ht
                obtain ⟨s, hs, hsmax⟩ := exists_max_solution v hne
                have hsCand : Candidate v (solutionValuation s) := by
                  refine hcandOf _ (hall s hs) ?_
                  simp only [SolBounded, ite_eq_right hmin, ite_eq_left hmax,
                    objectiveReal_solution]
                  exact fun u hu => by exact_mod_cast hsmax u hu
                have hs_le := hat _ hsCand
                rw [objectiveReal_solution] at hs_le
                have hts : (objectiveQ v t : ℝ) ≤ objectiveQ v s := by
                  exact_mod_cast hsmax t ht
                linarith
        · simp [SolSectionValid, hr, hmin, hmax] at hsols

/-- The claimed result depends only on the problem, the relation to prove, and the
listed solutions, never on the derivation list. Replacing the derivations, for example by
their `lin weak` completions, therefore leaves the certified claim unchanged. -/
theorem Feasible.withDers {v : Vipr} {a : RealValuation} (ders : Array ViprDer) :
    Feasible { v with ders := ders } a ↔ Feasible v a := Iff.rfl

theorem ClaimValid.withDers {v : Vipr} (ders : Array ViprDer) :
    ClaimValid { v with ders := ders } ↔ ClaimValid v := Iff.rfl

/-- The strengthened range claim implies the classical one: every optimal valuation
lies in the reported interval. -/
theorem ClaimValid.optimal_within {v : Vipr} {lb ub : Option ℚ}
    (h : ClaimValid v) (hr : v.rtp = .range lb ub) :
    ∀ a, IsOptimal v a → WithinRange lb ub (objectiveReal v a) := by
  rw [ClaimValid, hr] at h
  obtain ⟨hsols, hbound⟩ := h
  have hsolData := hsols
  simp only [SolSectionValid, hr] at hsolData
  obtain ⟨hall, hwitness⟩ := hsolData
  intro a hopt
  by_cases hmin : v.objSense = "min"
  · have hoptData :
        Feasible v a ∧ ∀ b, Feasible v b → objectiveReal v a ≤ objectiveReal v b := by
      simpa [IsOptimal, hmin] using hopt
    simp only [RangeBoundValid, ite_eq_left hmin] at hbound
    simp only [ite_eq_left hmin] at hwitness
    constructor
    · cases lb with
      | none => trivial
      | some lower => exact hbound a hoptData.1
    · cases ub with
      | none => trivial
      | some upper =>
          obtain ⟨s, hs, hupper⟩ := hwitness
          have hle := hoptData.2 (solutionValuation s) (hall s hs)
          rw [objectiveReal_solution] at hle
          exact hle.trans (by exact_mod_cast hupper)
  · by_cases hmax : v.objSense = "max"
    · have hoptData :
          Feasible v a ∧ ∀ b, Feasible v b → objectiveReal v b ≤ objectiveReal v a := by
        simpa [IsOptimal, hmin, hmax] using hopt
      simp only [RangeBoundValid, ite_eq_right hmin, ite_eq_left hmax] at hbound
      simp only [ite_eq_right hmin, ite_eq_left hmax] at hwitness
      constructor
      · cases lb with
        | none => trivial
        | some lower =>
            obtain ⟨s, hs, hlower⟩ := hwitness
            have hge := hoptData.2 (solutionValuation s) (hall s hs)
            rw [objectiveReal_solution] at hge
            exact (by exact_mod_cast hlower : (lower : ℝ) ≤ _).trans hge
      · cases ub with
        | none => trivial
        | some upper => exact hbound a hoptData.1
    · simp [IsOptimal, hmin, hmax] at hopt

/-! ### Refinement of executable solution checks to the declarative proof system -/

theorem satRat_sound_solution {c : SLe} {s : NamedSolution}
    (h : satRat c (sparseValuation s.2) = true) :
    satReal c (solutionValuation s) := by
  simp only [satRat] at h
  simp only [satReal]
  split_ifs at h ⊢ with hL hG hE
  · rw [evalReal_solution]
    exact_mod_cast of_decide_eq_true h
  · rw [evalReal_solution]
    exact_mod_cast of_decide_eq_true h
  · rw [evalReal_solution]
    exact_mod_cast of_decide_eq_true h

theorem solutionFeasible_sound {v : Vipr} {s : NamedSolution}
    (h : solutionFeasible v s = true) : Feasible v (solutionValuation s) := by
  rw [solutionFeasible, Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro j hj
    have hjb := (List.all_eq_true.mp h.1) j hj
    obtain ⟨z, hz⟩ := isIntVal_sound hjb
    refine ⟨z, ?_⟩
    change (sparseValuation s.2 j : ℝ) = (z : ℝ)
    exact_mod_cast hz
  · intro c hc
    exact satRat_sound_solution ((List.all_eq_true.mp h.2) c hc)

theorem allSolutionsFeasible_sound {v : Vipr} (h : allSolutionsFeasible v = true) :
    AllSolutionsValid v := by
  intro s hs
  exact solutionFeasible_sound ((List.all_eq_true.mp h) s hs)

theorem solSection_sound {v : Vipr} (h : solSection v = true) :
    SolSectionValid v := by
  cases hr : v.rtp with
  | infeas =>
      rw [SolSectionValid, hr]
      change v.sols.toList = []
      cases hs : v.sols.toList with
      | nil => rfl
      | cons s ss =>
          simp [solSection, hr, hs] at h
  | range lb ub =>
      rw [SolSectionValid, hr]
      simp only [solSection, hr, Bool.and_eq_true] at h
      refine ⟨allSolutionsFeasible_sound h.1, ?_⟩
      by_cases hmin : v.objSense = "min"
      · simp only [ite_eq_left hmin] at h
        simp only [hmin]
        cases ub with
        | none => trivial
        | some upper =>
            obtain ⟨s, hs, hle⟩ := List.any_eq_true.mp h.2
            exact ⟨s, hs, of_decide_eq_true hle⟩
      · by_cases hmax : v.objSense = "max"
        · simp only [ite_eq_right hmin, ite_eq_left hmax] at h
          simp only [hmax]
          cases lb with
          | none => trivial
          | some lower =>
              obtain ⟨s, hs, hle⟩ := List.any_eq_true.mp h.2
              exact ⟨s, hs, of_decide_eq_true hle⟩
        · simp [hmin, hmax] at h

theorem solReason_sound {v : Vipr} {stated : SLe}
    (h : solReason v stated = true) : SolReasonValid v stated := by
  unfold solReason at h
  unfold SolReasonValid
  by_cases hmin : v.objSense = "min"
  · simp only [ite_eq_left hmin] at h ⊢
    obtain ⟨s, hs, hdom⟩ := List.any_eq_true.mp h
    exact ⟨s, hs, Rule.dominates_valid_real hdom⟩
  · by_cases hmax : v.objSense = "max"
    · simp only [ite_eq_right hmin, ite_eq_left hmax] at h ⊢
      obtain ⟨s, hs, hdom⟩ := List.any_eq_true.mp h
      exact ⟨s, hs, Rule.dominates_valid_real hdom⟩
    · simp [hmin, hmax] at h

end LeanVIPR.Parser.Vipr
