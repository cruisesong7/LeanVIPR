module

public import LeanVIPR.Cert.ViprRuleSound

@[expose] public section

/-!
# Completeness of the executable rule checks

`ViprRuleSound` proves that each Boolean rule check implies its declarative,
real-valued counterpart. This module proves the converse: every declaratively valid
rule application is accepted by the executable check. Together they show that the
checks decide the declarative rules exactly.
-/

namespace LeanVIPR.Cert.ViprRuleComplete

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem

/-- Embed an exact rational valuation into the real semantics. -/
def ratToReal (a : Valuation) : RealValuation :=
  fun idx => (a idx : ℝ)

theorem evalReal_ratToReal (f : LinForm) (a : Valuation) :
    evalReal f (ratToReal a) = (LinForm.eval f a : ℝ) := by
  induction f with
  | nil => simp [evalReal, LinForm.eval]
  | cons t f ih =>
      simp only [evalReal, LinForm.eval, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp [ratToReal]

/-- A rational basis valuation selecting one variable. -/
def basisValuation (idx : Nat) : Valuation :=
  fun j => if j = idx then 1 else 0


def alKeys (al : List (Nat × ℚ)) : List Nat :=
  al.map Prod.fst

theorem mem_alKeys_addTerm (al : List (Nat × ℚ)) (i j : Nat) (c : ℚ) :
    j ∈ alKeys (addTerm al i c) ↔ j = i ∨ j ∈ alKeys al := by
  induction al with
  | nil =>
      simp [alKeys, addTerm]
  | cons head tail ih =>
      obtain ⟨k, d⟩ := head
      by_cases hik : i = k
      · subst i
        simp [alKeys, addTerm]
      · rw [show addTerm ((k, d) :: tail) i c =
          (k, d) :: addTerm tail i c by simp [addTerm, hik]]
        constructor
        · intro hj
          rcases List.mem_cons.mp
              (show j ∈ alKeys ((k, d) :: addTerm tail i c) from hj) with
            hj | hj
          · exact Or.inr (by
              apply List.mem_cons.mpr
              exact Or.inl hj)
          · rcases (ih).mp hj with hj | hj
            · exact Or.inl hj
            · exact Or.inr (by
                apply List.mem_cons.mpr
                exact Or.inr hj)
        · rintro (hj | hj)
          · apply List.mem_cons.mpr
            right
            exact (ih).mpr (Or.inl hj)
          · rcases List.mem_cons.mp hj with hj | hj
            · exact List.mem_cons.mpr (Or.inl hj)
            · exact List.mem_cons.mpr (Or.inr ((ih).mpr (Or.inr hj)))

theorem alKeys_addTerm_nodup {al : List (Nat × ℚ)} {i : Nat} {c : ℚ}
    (h : (alKeys al).Nodup) :
    (alKeys (addTerm al i c)).Nodup := by
  induction al with
  | nil =>
      simp [alKeys, addTerm]
  | cons head tail ih =>
      obtain ⟨k, d⟩ := head
      simp only [alKeys, List.map_cons, List.nodup_cons] at h ⊢
      by_cases hik : i = k
      · subst i
        simpa [addTerm] using h
      · rw [show addTerm ((k, d) :: tail) i c =
          (k, d) :: addTerm tail i c by simp [addTerm, hik]]
        simp only [List.map_cons, List.nodup_cons]
        constructor
        · intro hk
          rcases (mem_alKeys_addTerm tail i k c).mp hk with hk | hk
          · exact hik hk.symm
          · exact h.1 hk
        · exact ih h.2

theorem foldl_addTerm_nodup (f : LinForm) (al : List (Nat × ℚ))
    (h : (alKeys al).Nodup) :
    (alKeys (f.foldl (fun acc t => addTerm acc t.idx t.coeff) al)).Nodup := by
  induction f generalizing al with
  | nil => exact h
  | cons term tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (alKeys_addTerm_nodup h)

theorem normForm_keys_nodup (f : LinForm) :
    (alKeys (normForm f)).Nodup := by
  exact foldl_addTerm_nodup f [] (by simp [alKeys])

theorem evalAL_basis_zero {al : List (Nat × ℚ)} {idx : Nat}
    (hidx : idx ∉ alKeys al) :
    evalAL al (basisValuation idx) = 0 := by
  induction al with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨j, q⟩ := head
      have hj : j ≠ idx := by
        intro h
        apply hidx
        unfold alKeys
        simp [h]
      have htail : idx ∉ alKeys tail := by
        intro h
        apply hidx
        unfold alKeys at h ⊢
        exact List.mem_cons_of_mem _ h
      change q * basisValuation idx j +
          evalAL tail (basisValuation idx) = 0
      rw [ih htail]
      simp [basisValuation, hj]

theorem evalAL_basis_of_mem {al : List (Nat × ℚ)} {p : Nat × ℚ}
    (hnodup : (alKeys al).Nodup) (hp : p ∈ al) :
    evalAL al (basisValuation p.1) = p.2 := by
  induction al with
  | nil => simp at hp
  | cons head tail ih =>
      obtain ⟨idx, q⟩ := head
      simp only [alKeys, List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hp with rfl | hp
      · have hzero := evalAL_basis_zero (idx := idx) hnodup.1
        change q * basisValuation idx idx +
            evalAL tail (basisValuation idx) = q
        rw [hzero]
        simp [basisValuation]
      · have hne : idx ≠ p.1 := by
          intro h
          apply hnodup.1
          rw [h]
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        change q * basisValuation p.1 idx +
            evalAL tail (basisValuation p.1) = p.2
        rw [ih hnodup.2 hp]
        simp [basisValuation, hne]

/-- Semantic zero over exact rationals is also accepted by the executable test. -/
theorem formIsZero_complete {f : LinForm}
    (hzero : ∀ a : Valuation, f.eval a = 0) :
    formIsZero f = true := by
  unfold formIsZero
  apply List.all_eq_true.mpr
  intro p hp
  rw [beq_iff_eq]
  have hisolate :=
    evalAL_basis_of_mem (normForm_keys_nodup f) hp
  rw [normForm_eval] at hisolate
  rw [hzero] at hisolate
  exact hisolate.symm

/-- Semantic equality over exact rationals is accepted by `formEq`. -/
theorem formEq_complete {left right : LinForm}
    (heq : ∀ a : Valuation, left.eval a = right.eval a) :
    formEq left right = true := by
  apply formIsZero_complete
  intro a
  simp [sNegForm, heq a]

theorem ratEvalZero_of_formZeroReal {f : LinForm}
    (h : FormZeroReal f) :
    ∀ a : Valuation, f.eval a = 0 := by
  intro a
  have hr := h (ratToReal a)
  rw [evalReal_ratToReal] at hr
  exact_mod_cast hr

theorem ratEvalEq_of_formEqReal {left right : LinForm}
    (h : FormEqReal left right) :
    ∀ a : Valuation, left.eval a = right.eval a := by
  intro a
  have hr := h (ratToReal a)
  rw [evalReal_ratToReal, evalReal_ratToReal] at hr
  exact_mod_cast hr

theorem formIsZero_complete_real {f : LinForm} (h : FormZeroReal f) :
    formIsZero f = true :=
  formIsZero_complete (ratEvalZero_of_formZeroReal h)

theorem formEq_complete_real {left right : LinForm}
    (h : FormEqReal left right) :
    formEq left right = true :=
  formEq_complete (ratEvalEq_of_formEqReal h)

theorem senseSign_cast (sense : Char) :
    senseSignReal sense = (senseSign sense : ℝ) := by
  by_cases hL : sense = 'L'
  · simp [senseSignReal, senseSign, hL]
  · by_cases hG : sense = 'G'
    · simp [senseSignReal, senseSign, hG]
    · simp [senseSignReal, senseSign, hL, hG]

theorem suitLeB_complete {comb : List (ℚ × SLe)}
    (h : SuitableLe comb) :
    suitLeB comb = true := by
  unfold suitLeB
  apply List.all_eq_true.mpr
  intro p hp
  rw [decide_eq_true_eq]
  have hpReal := h p hp
  rw [senseSign_cast] at hpReal
  exact_mod_cast hpReal

theorem suitGeB_complete {comb : List (ℚ × SLe)}
    (h : SuitableGe comb) :
    suitGeB comb = true := by
  unfold suitGeB
  apply List.all_eq_true.mpr
  intro p hp
  rw [decide_eq_true_eq]
  have hpReal := h p hp
  rw [senseSign_cast] at hpReal
  exact_mod_cast hpReal

theorem isIntValB_complete {q : ℚ} (h : IsIntVal q) :
    isIntValB q = true := by
  obtain ⟨z, rfl⟩ := h
  simp [isIntValB]

theorem eval_scale_valuation (f : LinForm) (s : ℚ) (a : Valuation) :
    LinForm.eval f (fun j => s * a j) = s * LinForm.eval f a := by
  induction f with
  | nil => simp [LinForm.eval]
  | cons t f ih =>
      change t.coeff * (s * a t.idx) + LinForm.eval f (fun j => s * a j) =
        s * (t.coeff * a t.idx + LinForm.eval f a)
      rw [ih]
      ring

theorem not_isIntReal_half : ¬ IsIntReal ((1 / 2 : ℚ) : ℝ) := by
  rintro ⟨z, hz⟩
  have hq : (1 / 2 : ℚ) = (z : ℚ) := by exact_mod_cast hz
  have h2 : ((2 * z : ℤ) : ℚ) = 1 := by push_cast; rw [← hq]; norm_num
  have : 2 * z = 1 := by exact_mod_cast h2
  omega

/-- A semantically integer-valued form passes the normalized executable test:
each normalized coefficient is isolated by a scaled basis valuation. -/
theorem formIntB_complete_real {intVars : List Nat} {form : LinForm}
    (h : FormIntegralReal intVars form) :
    formIntB intVars form = true := by
  unfold formIntB
  apply List.all_eq_true.mpr
  intro p hp
  have hbasis : form.eval (basisValuation p.1) = p.2 := by
    rw [← normForm_eval]
    exact evalAL_basis_of_mem (normForm_keys_nodup form) hp
  have hvalue : ∀ s : ℚ, (∀ j ∈ intVars, IsIntVal (s * basisValuation p.1 j)) →
      IsIntReal (((s * p.2 : ℚ)) : ℝ) := by
    intro s hs
    have hr := h (ratToReal fun j => s * basisValuation p.1 j) (by
      intro j hj
      obtain ⟨z, hz⟩ := hs j hj
      exact ⟨z, by simp [ratToReal, hz]⟩)
    rwa [evalReal_ratToReal, eval_scale_valuation, hbasis] at hr
  simp only [intEntryB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  by_cases hidx : p.1 ∈ intVars
  · right
    refine ⟨isIntValB_complete ?_, hidx⟩
    obtain ⟨z, hz⟩ := hvalue 1 (by
      intro j _
      by_cases hj : j = p.1
      · exact ⟨1, by simp [basisValuation, hj]⟩
      · exact ⟨0, by simp [basisValuation, hj]⟩)
    have hz' : ((p.2 : ℚ) : ℝ) = ((z : ℚ) : ℝ) := by simpa using hz
    exact ⟨z, by exact_mod_cast hz'⟩
  · left
    by_contra hne
    apply not_isIntReal_half
    have hhalf : 1 / (2 * p.2) * p.2 = 1 / 2 := by field_simp
    rw [← hhalf]
    apply hvalue
    intro j hj
    have hj' : j ≠ p.1 := fun heq => hidx (heq ▸ hj)
    exact ⟨0, by simp [basisValuation, hj']⟩

theorem linAbsurd_complete {comb : List (ℚ × SLe)}
    (h : LinAbsurd comb) :
    linAbsurd comb (scomb comb) (normForm (scomb comb).form) = true := by
  rcases h with ⟨hsuit, hzero, hnegative⟩ | ⟨hsuit, hzero, hpositive⟩
  · simp [linAbsurd, suitLeB_complete hsuit,
      formIsZero_complete_real hzero, hnegative]
  · simp [linAbsurd, suitGeB_complete hsuit,
      formIsZero_complete_real hzero, hpositive]

theorem linCheck_complete {stated : SLe} {comb : List (ℚ × SLe)}
    (h : LinValid stated comb) :
    linCheck stated comb = true := by
  rcases h with habsurd | ⟨hform, hdir⟩
  · simp [linCheck, linAbsurd_complete habsurd]
  · simp only [linCheck, alIsZero_alExtend_normForm, Bool.or_eq_true]
    right
    rw [Bool.and_eq_true]
    refine ⟨formEq_complete_real hform, ?_⟩
    rcases hdir with ⟨hL, hsuit, hrhs⟩ | ⟨hG, hsuit, hrhs⟩ | ⟨hE, hle, hge, hrhs⟩
    · simp [hL, suitLeB_complete hsuit, hrhs]
    · simp [hG, suitGeB_complete hsuit, hrhs]
    · simp [hE, suitLeB_complete hle, suitGeB_complete hge, hrhs]

theorem rndCheck_complete {intVars : List Nat} {stated : SLe}
    {comb : List (ℚ × SLe)}
    (h : RndValid intVars stated comb) :
    rndCheck intVars stated comb = true := by
  obtain ⟨hform, hint, hdir⟩ := h
  simp only [rndCheck, alIsZero_alExtend_normForm, alIntB_normForm, Bool.and_eq_true]
  constructor
  · exact ⟨formEq_complete_real hform, formIntB_complete_real hint⟩
  rcases hdir with ⟨hL, hsuit, hrhs⟩ | ⟨hG, hsuit, hrhs⟩
  · simp [hL, suitLeB_complete hsuit, hrhs]
  · simp [hG, suitGeB_complete hsuit, hrhs]

theorem absurdB_complete {row : SLe} (h : Absurd row) :
    absurdB row = true := by
  obtain ⟨hzero, hdir⟩ := h
  rw [absurdB, Bool.and_eq_true]
  refine ⟨formIsZero_complete_real hzero, ?_⟩
  rcases hdir with ⟨hL, hnegative⟩ | ⟨hG, hpositive⟩ | ⟨hE, hne⟩
  · simp [hL, hnegative]
  · simp [hG, hpositive]
  · simp [hE, hne]

theorem domSLe_complete {source target : SLe}
    (h : Dominates source target) :
    domSLe source target = true := by
  rcases h with habsurd | ⟨hform, hdir⟩
  · simp [domSLe, absurdB_complete habsurd]
  · rw [domSLe, Bool.or_eq_true]
    right
    rw [Bool.and_eq_true]
    refine ⟨formEq_complete_real hform, ?_⟩
    rcases hdir with
      ⟨hL, hsource, hrhs⟩ |
      ⟨hG, hsource, hrhs⟩ |
      ⟨hE, hsource, hrhs⟩
    · rcases hsource with hsource | hsource <;>
        simp [hL, hsource, hrhs]
    · rcases hsource with hsource | hsource <;>
        simp [hG, hsource, hrhs]
    · simp [hE, hsource, hrhs]

theorem unsBoundsB_complete {intVars : List Nat} {left right : SLe}
    (h : ComplementaryBounds intVars left right) :
    unsBoundsB intVars left right = true := by
  rcases h with
    ⟨hL, hG, hform, hformInt, hint, hrhs⟩ |
    ⟨hG, hL, hform, hformInt, hint, hrhs⟩
  · simp [unsBoundsB, hL, hG, formEq_complete_real hform,
      formIntB_complete_real hformInt, isIntValB_complete hint, hrhs]
  · simp [unsBoundsB, hL, hG, formEq_complete_real hform,
      formIntB_complete_real hformInt, isIntValB_complete hint, hrhs]

end LeanVIPR.Cert.ViprRuleComplete
