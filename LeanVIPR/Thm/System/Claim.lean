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
        have hb : objectiveReal v a ≤ (objectiveQ v s : ℝ) ∧
            (ObjectiveIntegral v → objectiveReal v a ≤ (objectiveQ v s : ℝ) - 1) := by
          rw [SolBounded, ite_eq_left hmin] at hbounded
          exact hbounded s hs
        rcases hdom with hdom | ⟨hint, hdom⟩
        · exact dominates_sound hdom (by simpa [satReal, objectiveReal] using hb.1)
        · exact dominates_sound hdom (by simpa [satReal, objectiveReal] using hb.2 hint)
      · obtain ⟨s, hs, hdom⟩ := hreason
        have hb : (objectiveQ v s : ℝ) ≤ objectiveReal v a ∧
            (ObjectiveIntegral v → (objectiveQ v s : ℝ) + 1 ≤ objectiveReal v a) := by
          rw [SolBounded, ite_eq_right hmin, ite_eq_left hmax] at hbounded
          exact hbounded s hs
        rcases hdom with hdom | ⟨hint, hdom⟩
        · exact dominates_sound hdom (by simpa [satReal, objectiveReal] using hb.1)
        · exact dominates_sound hdom (by simpa [satReal, objectiveReal] using hb.2 hint)

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
    (hmem : e ∈ sfreplay (sinitPool (conSLes v)) (viprSteps v))
    (hclosed : e.2 = ∅) : satReal e.1 a := by
  have hall := replay_sound v a hsols hcand
    (sinitPool (conSLes v)) (viprSteps v) hder
    (initialPool_holds (conSLes v) a)
  have he : EntryHolds (conSLes v) a e := hall e hmem
  exact he (candidate_feasible hcand).2 (by simp [hclosed])

/-- Between integers, exceeding `y - 1` means reaching `y`. -/
private theorem le_of_not_le_sub_one {x y : ℝ} (hx : IsIntReal x) (hy : IsIntReal y)
    (h : ¬ x ≤ y - 1) : y ≤ x := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hlt : ((n - 1 : ℤ) : ℝ) < m := by push_cast; exact lt_of_not_ge h
  have : n - 1 < m := by exact_mod_cast hlt
  exact_mod_cast (show n ≤ m by omega)

/-- Between integers, falling short of `y + 1` means not exceeding `y`. -/
private theorem le_of_not_add_one_le {x y : ℝ} (hx : IsIntReal x) (hy : IsIntReal y)
    (h : ¬ y + 1 ≤ x) : x ≤ y := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hlt : (m : ℝ) < ((n + 1 : ℤ) : ℝ) := by push_cast; exact lt_of_not_ge h
  have : m < n + 1 := by exact_mod_cast hlt
  exact_mod_cast (show m ≤ n by omega)

/-- A listed solution's objective value is an integer when the objective is integral. -/
private theorem objectiveQ_isInt {v : Vipr} (hint : ObjectiveIntegral v)
    (hall : AllSolutionsValid v) {t : NamedSolution} (ht : t ∈ v.sols.toList) :
    IsIntReal (objectiveQ v t : ℝ) := by
  have h := hint (solutionValuation t) (hall t ht).1
  rw [evalReal_solution] at h
  exact h

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
            obtain ⟨⟨e, hlast, hclosed, hdom⟩, hsolsLower⟩ := hfinalData
            -- the closed final row holds at every candidate valuation
            have hat : ∀ a, Candidate v a → (lower : ℝ) ≤ objectiveReal v a := by
              intro a hcand
              have hgoal := System.dominates_sound hdom
                (closedFinal_holds hsols hcand hder hlast hclosed)
              simpa [objectiveLowerRow, satReal, objectiveReal] using hgoal
            intro a hfeas
            by_cases hb : SolBounded v a
            · exact hat a (hcandOf a hfeas hb)
            · -- `a` does not beat some listed solution `t`, and the bound does not pass `t`
              simp only [SolBounded, ite_eq_left hmin, not_forall] at hb
              obtain ⟨t, ht, hnot⟩ := hb
              have hlow : (lower : ℝ) ≤ objectiveQ v t := by exact_mod_cast hsolsLower t ht
              have hta : (objectiveQ v t : ℝ) ≤ objectiveReal v a := by
                by_cases hle : objectiveReal v a ≤ objectiveQ v t
                · have hint : ObjectiveIntegral v := by
                    by_contra hint
                    exact hnot ⟨hle, fun h => absurd h hint⟩
                  have hsub : ¬ objectiveReal v a ≤ (objectiveQ v t : ℝ) - 1 :=
                    fun h => hnot ⟨hle, fun _ => h⟩
                  exact le_of_not_le_sub_one (hint a hfeas.1)
                    (objectiveQ_isInt hint hall ht) hsub
                · exact (lt_of_not_ge hle).le
              linarith
      · rw [ite_eq_right hmin]
        by_cases hmax : v.objSense = "max"
        · rw [ite_eq_left hmax]
          cases ub with
          | none => trivial
          | some upper =>
              have hfinalData := hfinal
              simp only [FinalValid, hr, ite_eq_right hmin, ite_eq_left hmax] at hfinalData
              obtain ⟨⟨e, hlast, hclosed, hdom⟩, hsolsUpper⟩ := hfinalData
              have hat : ∀ a, Candidate v a → objectiveReal v a ≤ (upper : ℝ) := by
                intro a hcand
                have hgoal := System.dominates_sound hdom
                  (closedFinal_holds hsols hcand hder hlast hclosed)
                simpa [objectiveUpperRow, satReal, objectiveReal] using hgoal
              intro a hfeas
              by_cases hb : SolBounded v a
              · exact hat a (hcandOf a hfeas hb)
              · simp only [SolBounded, ite_eq_right hmin, ite_eq_left hmax, not_forall] at hb
                obtain ⟨t, ht, hnot⟩ := hb
                have hup : (objectiveQ v t : ℝ) ≤ upper := by exact_mod_cast hsolsUpper t ht
                have hat' : objectiveReal v a ≤ (objectiveQ v t : ℝ) := by
                  by_cases hle : (objectiveQ v t : ℝ) ≤ objectiveReal v a
                  · have hint : ObjectiveIntegral v := by
                      by_contra hint
                      exact hnot ⟨hle, fun h => absurd h hint⟩
                    have hadd : ¬ (objectiveQ v t : ℝ) + 1 ≤ objectiveReal v a :=
                      fun h => hnot ⟨hle, fun _ => h⟩
                    exact le_of_not_add_one_le (hint a hfeas.1)
                      (objectiveQ_isInt hint hall ht) hadd
                  · exact (lt_of_not_ge hle).le
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
    obtain ⟨s, hs, hor⟩ := List.any_eq_true.mp h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hor
    rcases hor with hdom | ⟨hint, hdom⟩
    · exact ⟨s, hs, Or.inl (Rule.dominates_valid_real hdom)⟩
    · exact ⟨s, hs, Or.inr ⟨Rule.formIsInt_sound_real hint, Rule.dominates_valid_real hdom⟩⟩
  · by_cases hmax : v.objSense = "max"
    · simp only [ite_eq_right hmin, ite_eq_left hmax] at h ⊢
      obtain ⟨s, hs, hor⟩ := List.any_eq_true.mp h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hor
      rcases hor with hdom | ⟨hint, hdom⟩
      · exact ⟨s, hs, Or.inl (Rule.dominates_valid_real hdom)⟩
      · exact ⟨s, hs, Or.inr ⟨Rule.formIsInt_sound_real hint, Rule.dominates_valid_real hdom⟩⟩
    · simp [hmin, hmax] at h

end LeanVIPR.Parser.Vipr
