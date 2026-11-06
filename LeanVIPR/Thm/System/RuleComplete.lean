module

public import LeanVIPR.Thm.System.RuleSound

@[expose] public section

/-!
# Completeness of the executable rule checks

`ViprRuleSound` proves that each Boolean rule check implies its declarative,
real-valued counterpart. This module proves the converse: every declaratively valid
rule application is accepted by the executable check. Together they show that the
checks decide the declarative rules exactly.
-/

namespace LeanVIPR.Semantics.RuleComplete

open LeanVIPR.Semantics LeanVIPR.Semantics.System

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

/-! ### Distinct keys

`normForm` sorts by key and then merges adjacent equal keys, so its keys are strictly
increasing and in particular distinct. The basis-valuation argument below needs that to
read one coefficient off a normalized form at a time. -/

private theorem combineAdj_keys_subset : ∀ (l : List (Nat × ℚ)) {k : Nat},
    k ∈ alKeys (combineAdj l) → k ∈ alKeys l
  | [], k, h => by rw [combineAdj] at h; exact h
  | [_], k, h => by rw [combineAdj] at h; exact h
  | (i, c) :: (j, d) :: rest, k, h => by
      rw [combineAdj] at h
      split at h
      case isTrue hij =>
          subst hij
          have := combineAdj_keys_subset ((i, c + d) :: rest) h
          simp only [alKeys, List.map_cons, List.mem_cons] at this ⊢
          rcases this with rfl | hk
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hk)
      case isFalse =>
          simp only [alKeys, List.map_cons, List.mem_cons] at h ⊢
          rcases h with rfl | hk
          · exact Or.inl rfl
          · have := combineAdj_keys_subset ((j, d) :: rest) (by simpa [alKeys] using hk)
            simp only [alKeys, List.map_cons, List.mem_cons] at this
            exact Or.inr this
  termination_by l => l.length

private theorem alKeys_cons (a : Nat) (c : ℚ) (t : List (Nat × ℚ)) :
    alKeys ((a, c) :: t) = a :: alKeys t := rfl

private theorem combineAdj_keys_nodup : ∀ (l : List (Nat × ℚ)),
    (alKeys l).Pairwise (· ≤ ·) → (alKeys (combineAdj l)).Nodup
  | [], _ => by rw [combineAdj]; simp [alKeys]
  | [_], _ => by rw [combineAdj]; simp [alKeys]
  | (i, c) :: (j, d) :: rest, hp => by
      rw [alKeys_cons, alKeys_cons] at hp
      obtain ⟨hi, hp'⟩ := List.pairwise_cons.mp hp
      have hpt : (alKeys ((j, d) :: rest)).Pairwise (· ≤ ·) := by
        rw [alKeys_cons]; exact hp'
      have hij : i ≤ j := hi j (List.mem_cons_self ..)
      rw [combineAdj]
      split
      case isTrue heq =>
          subst heq
          exact combineAdj_keys_nodup ((i, c + d) :: rest) (by rw [alKeys_cons]; exact hp')
      case isFalse hne =>
          rw [alKeys_cons]
          refine List.nodup_cons.mpr ⟨?_, combineAdj_keys_nodup ((j, d) :: rest) hpt⟩
          intro hmem
          have hk := combineAdj_keys_subset ((j, d) :: rest) hmem
          rw [alKeys_cons] at hk
          rcases List.mem_cons.mp hk with rfl | hk'
          · exact hne rfl
          · have := (List.pairwise_cons.mp hp').1 i hk'
            omega
  termination_by l => l.length

/-- `collectNZ` counts indices down and prepends, so its keys come out strictly
increasing. -/
private theorem collectNZ_keys_lt : ∀ (arr : Array ℚ) (k : Nat) (acc : List (Nat × ℚ)),
    (∀ j ∈ alKeys acc, k ≤ j) → (alKeys acc).Pairwise (· < ·) →
    (alKeys (collectNZ arr k acc)).Pairwise (· < ·)
  | _, 0, _, _, hp => by rw [collectNZ]; exact hp
  | arr, k + 1, acc, hge, hp => by
      rw [collectNZ]
      split
      case isTrue =>
          exact collectNZ_keys_lt arr k acc (fun j hj => le_of_lt (hge j hj)) hp
      case isFalse =>
          refine collectNZ_keys_lt arr k ((k, arr[k]!) :: acc) ?_ ?_
          · intro j hj
            rw [alKeys_cons] at hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact le_refl _
            · exact le_of_lt (hge j hj)
          · rw [alKeys_cons]
            refine List.pairwise_cons.mpr ⟨?_, hp⟩
            intro b hb
            exact hge b hb

theorem normFormDense_keys_nodup (f : LinForm) :
    (alKeys (collectNZ (denseAccum (formWidth f) f) (formWidth f) [])).Nodup :=
  ((collectNZ_keys_lt _ _ [] (by simp [alKeys]) (by simp [alKeys])).imp
    (fun h => ne_of_lt h)).nodup

theorem normForm_keys_nodup (f : LinForm) : (alKeys (normForm f)).Nodup := by
  rw [normForm]
  split
  · exact normFormDense_keys_nodup f
  · refine combineAdj_keys_nodup _ ?_
    simpa [alKeys, List.pairwise_map, KeySorted] using
      sortKV_sorted (f.map (fun t => (t.idx, t.coeff)))

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
  · simp only [linCheck, Bool.or_eq_true]
    left
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
  simp only [rndCheck, alIntB_normForm, Bool.and_eq_true]
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

end LeanVIPR.Semantics.RuleComplete
