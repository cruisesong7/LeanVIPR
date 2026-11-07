module

public import LeanVIPR.Thm.System.Sound
public import LeanVIPR.Spec.Semantics.Lower

@[expose] public section

/-!
# Soundness of the executable VIPR rule checks

This module proves that the executable Boolean side-condition checks for the
individual VIPR rules refine their declarative real-valued semantics.
-/

namespace LeanVIPR.Semantics.Rule

open LeanVIPR.Semantics LeanVIPR.Semantics.System

/-! ## Boolean arithmetic checks imply their real-semantic counterparts -/

private def evalALReal (al : List (Nat × ℚ)) (a : RealValuation) : ℝ :=
  (al.map (fun p => (p.2 : ℝ) * a p.1)).sum

@[simp] private theorem evalALReal_cons (p : Nat × ℚ) (tl : List (Nat × ℚ))
    (a : RealValuation) :
    evalALReal (p :: tl) a = (p.2 : ℝ) * a p.1 + evalALReal tl a := by
  simp [evalALReal]

/-! The sort-and-merge normalization over the reals, mirroring
`LeanVIPR.Semantics.normForm_eval`: sorting is a permutation and the sum is invariant
under it, and merging two entries with the same key uses `c * x + d * x = (c + d) * x`. -/

private theorem evalALReal_combineAdj : ∀ (l : List (Nat × ℚ)) (a : RealValuation),
    evalALReal (combineAdj l) a = evalALReal l a
  | [], _ => by rw [combineAdj]
  | [_], _ => by rw [combineAdj]
  | (i, c) :: (j, d) :: rest, a => by
      rw [combineAdj]
      split
      case isTrue hij =>
          subst hij
          rw [evalALReal_combineAdj ((i, c + d) :: rest) a]
          simp only [evalALReal_cons, Rat.cast_add]
          ring
      case isFalse =>
          rw [evalALReal_cons, evalALReal_combineAdj ((j, d) :: rest) a]
          exact (evalALReal_cons _ _ _).symm
  termination_by l _ => l.length

private theorem evalALReal_perm {l₁ l₂ : List (Nat × ℚ)} (h : l₁.Perm l₂)
    (a : RealValuation) : evalALReal l₁ a = evalALReal l₂ a := by
  unfold evalALReal
  exact (h.map _).sum_eq

private theorem evalALReal_map_form (f : LinForm) (a : RealValuation) :
    evalALReal (f.map (fun t => (t.idx, t.coeff))) a = evalReal f a := by
  unfold evalALReal evalReal
  rw [List.map_map]
  rfl

/-! The dense normalization over the reals, mirroring
`LeanVIPR.Thm.System.LinForm.normFormDense_eval`. The array facts it rests on —
`size_denseAccum`, `getBang_set_self`, `getBang_set_ne`, `lt_formWidth` — say nothing
about values and are shared with the rational version. -/

/-- Value over the reals of the first `k` slots of a coefficient array. -/
private def arrSumReal (arr : Array ℚ) (a : RealValuation) : Nat → ℝ
  | 0 => 0
  | i + 1 => (arr[i]! : ℝ) * a i + arrSumReal arr a i

private theorem evalALReal_collectNZ : ∀ (arr : Array ℚ) (k : Nat)
    (acc : List (Nat × ℚ)) (a : RealValuation), k ≤ arr.size →
    evalALReal (collectNZ arr k acc) a = arrSumReal arr a k + evalALReal acc a
  | _, 0, _, _, _ => by rw [collectNZ, arrSumReal]; ring
  | arr, k + 1, acc, a, hk => by
      rw [collectNZ, evalALReal_collectNZ arr k _ a (by omega), arrSumReal]
      split
      case isTrue hz =>
          have hzz : arr[k]! = 0 := by simpa using hz
          rw [hzz]; push_cast; ring
      case isFalse => rw [evalALReal_cons]; ring

private theorem arrSumReal_set : ∀ (arr : Array ℚ) (a : RealValuation) (i : Nat) (c : ℚ)
    (k : Nat), i < arr.size → k ≤ arr.size →
    arrSumReal (arr.set! i (arr[i]! + c)) a k
      = arrSumReal arr a k + (if i < k then (c : ℝ) * a i else 0)
  | _, _, _, _, 0, _, _ => by simp [arrSumReal]
  | arr, a, i, c, k + 1, hi, hk => by
      rw [arrSumReal, arrSumReal, arrSumReal_set arr a i c k hi (by omega)]
      by_cases hik : i = k
      · subst hik
        rw [getBang_set_self hi]
        simp only [lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
        push_cast
        ring
      · rw [getBang_set_ne (by omega) (fun h => hik h.symm)]
        by_cases hlt : i < k
        · simp only [hlt, ite_true, show i < k + 1 from by omega]
          ring
        · have hnk : ¬ i < k + 1 := by omega
          simp only [hlt, ite_false, hnk]
          ring

private theorem arrSumReal_denseAccum : ∀ (g : LinForm) (arr : Array ℚ) (n : Nat)
    (a : RealValuation), arr.size = n → (∀ t ∈ g, t.idx < n) →
    arrSumReal (g.foldl (fun b t => b.set! t.idx (b[t.idx]! + t.coeff)) arr) a n
      = arrSumReal arr a n + evalReal g a
  | [], arr, n, a, _, _ => by simp [evalReal]
  | t :: ts, arr, n, a, hn, hb => by
      have hlt : t.idx < arr.size := by rw [hn]; exact hb t (by simp)
      rw [List.foldl_cons,
        arrSumReal_denseAccum ts _ n a (by rw [Array.size_set!, hn])
          (fun u hu => hb u (by simp [hu])),
        arrSumReal_set arr a t.idx t.coeff n hlt (le_of_eq hn.symm)]
      have hcons : evalReal (t :: ts) a = (t.coeff : ℝ) * a t.idx + evalReal ts a := by
        simp [evalReal]
      rw [hcons]
      simp only [show t.idx < n from by rw [← hn]; exact hlt, ite_true]
      ring

private theorem arrSumReal_replicate_zero (n : Nat) (a : RealValuation) :
    ∀ k ≤ n, arrSumReal (Array.replicate n (0 : ℚ)) a k = 0
  | 0, _ => by rw [arrSumReal]
  | k + 1, hk => by
      rw [arrSumReal, arrSumReal_replicate_zero n a k (by omega),
        getBang_lt (by simpa using (by omega : k < n)), Array.getElem_replicate]
      push_cast
      ring

private theorem normFormDense_eval_real (f : LinForm) (a : RealValuation) :
    evalALReal (normFormDense f) a = evalReal f a := by
  rw [normFormDense]
  rw [evalALReal_collectNZ _ _ _ a (by rw [size_denseAccum]), denseAccum,
    arrSumReal_denseAccum f _ (formWidth f) a (by simp) (fun t ht => lt_formWidth ht),
    arrSumReal_replicate_zero _ a _ (le_refl _)]
  simp [evalALReal]

private theorem normFormSort_eval_real (f : LinForm) (a : RealValuation) :
    evalALReal (normFormSort f) a = evalReal f a := by
  rw [normFormSort, evalALReal_combineAdj, evalALReal_perm (sortKV_perm _) a,
    evalALReal_map_form]

private theorem normForm_eval_real (f : LinForm) (a : RealValuation) :
    evalALReal (normForm f) a = evalReal f a := by
  rw [normForm]
  split
  · exact normFormDense_eval_real f a
  · exact normFormSort_eval_real f a

private theorem evalALReal_zero_of_all (al : List (Nat × ℚ)) (a : RealValuation)
    (h : ∀ p ∈ al, p.2 = 0) : evalALReal al a = 0 := by
  induction al with
  | nil => simp [evalALReal]
  | cons p tl ih =>
      simp only [evalALReal_cons, h p (by simp), Rat.cast_zero, zero_mul,
        ih (fun q hq => h q (by simp [hq])), zero_add]

private theorem formIsZero_sound_real {f : LinForm} (h : formIsZero f = true) :
    FormZeroReal f := by
  intro a
  rw [← normForm_eval_real]
  refine evalALReal_zero_of_all _ a (fun p hp => ?_)
  exact eq_of_beq ((List.all_eq_true.mp h) p hp)

private theorem formEq_sound_real {f g : LinForm} (h : formEq f g = true) :
    FormEqReal f g := by
  intro a
  have hz := formIsZero_sound_real h a
  simp [sNegForm, evalReal_append, evalReal_scale] at hz
  linarith

private theorem evalALReal_isInt (al : List (Nat × ℚ)) (a : RealValuation)
    (h : ∀ p ∈ al, p.2 = 0 ∨ (IsIntVal p.2 ∧ IsIntReal (a p.1))) :
    IsIntReal (evalALReal al a) := by
  induction al with
  | nil => exact ⟨0, by simp [evalALReal]⟩
  | cons p tl ih =>
      obtain ⟨m, hm⟩ := ih (fun q hq => h q (by simp [hq]))
      rw [evalALReal_cons, hm]
      rcases h p (by simp) with hp | ⟨⟨c, hc⟩, ⟨v, hv⟩⟩
      · exact ⟨m, by simp [hp]⟩
      · exact ⟨c * v + m, by rw [hc, hv]; push_cast; ring⟩

private theorem formInt_sound_real {intVars : List Nat} {f : LinForm}
    (h : formInt intVars f = true) : FormIntegralReal intVars f := by
  intro a hint
  rw [← normForm_eval_real]
  refine evalALReal_isInt _ a fun p hp => ?_
  exact (intEntry_sound ((List.all_eq_true.mp h) p hp)).imp_right
    fun ⟨hq, hidx⟩ => ⟨hq, hint p.1 hidx⟩

private theorem senseSign_cast (s : Char) :
    senseSignReal s = ((senseSign s : ℚ) : ℝ) := by
  simp only [senseSignReal, senseSign]
  split_ifs <;> norm_num

private theorem suitLe_sound_real {cs : List (ℚ × SLe)} (h : suitLe cs = true) :
    SuitableLe cs := by
  intro p hp
  rw [senseSign_cast]
  exact_mod_cast suitLe_sound h p hp

private theorem suitGe_sound_real {cs : List (ℚ × SLe)} (h : suitGe cs = true) :
    SuitableGe cs := by
  intro p hp
  rw [senseSign_cast]
  exact_mod_cast suitGe_sound h p hp

private theorem linAbsurd_sound_real {cs : List (ℚ × SLe)}
    (h : linAbsurd cs (scomb cs) (normForm (scomb cs).form) = true) : LinAbsurd cs := by
  simp only [linAbsurd, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hs, hz⟩, hrhs⟩ | ⟨⟨hs, hz⟩, hrhs⟩
  · exact Or.inl ⟨suitLe_sound_real hs, formIsZero_sound_real hz, hrhs⟩
  · exact Or.inr ⟨suitGe_sound_real hs, formIsZero_sound_real hz, hrhs⟩

theorem linCheck_valid_real {stated : SLe} {cs : List (ℚ × SLe)}
    (h : linCheck stated cs = true) : LinValid stated cs := by
  simp only [linCheck, Bool.or_eq_true] at h
  rcases h with hnormal | habs
  swap
  · exact Or.inl (linAbsurd_sound_real habs)
  · rw [Bool.and_eq_true] at hnormal
    obtain ⟨hform, hrest⟩ := hnormal
    refine Or.inr ⟨formEq_sound_real hform, ?_⟩
    split_ifs at hrest with hL hG hE
    · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
      exact Or.inl ⟨hL, suitLe_sound_real hrest.1, hrest.2⟩
    · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
      exact Or.inr (Or.inl ⟨hG, suitGe_sound_real hrest.1, hrest.2⟩)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
      exact Or.inr (Or.inr ⟨hE, suitLe_sound_real hrest.1.1,
        suitGe_sound_real hrest.1.2, hrest.2⟩)

theorem rndCheck_valid_real {intVars : List Nat} {stated : SLe}
    {cs : List (ℚ × SLe)} (h : rndCheck intVars stated cs = true) :
    RndValid intVars stated cs := by
  simp only [rndCheck, alInt_normForm, Bool.and_eq_true] at h
  obtain ⟨⟨hform, hInt⟩, hrest⟩ := h
  refine ⟨formEq_sound_real hform, formInt_sound_real hInt, ?_⟩
  split_ifs at hrest with hL hG
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    exact Or.inl ⟨hL, suitLe_sound_real hrest.1, hrest.2⟩
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    exact Or.inr ⟨hG, suitGe_sound_real hrest.1, hrest.2⟩

theorem isAbsurd_sound_real {c : SLe} (h : isAbsurd c = true) : Absurd c := by
  simp only [isAbsurd, Bool.and_eq_true] at h
  obtain ⟨hz, hcase⟩ := h
  refine ⟨formIsZero_sound_real hz, ?_⟩
  split_ifs at hcase with hL hG hE
  · rw [decide_eq_true_eq] at hcase
    exact Or.inl ⟨hL, hcase⟩
  · rw [decide_eq_true_eq] at hcase
    exact Or.inr (Or.inl ⟨hG, hcase⟩)
  · rw [decide_eq_true_eq] at hcase
    exact Or.inr (Or.inr ⟨hE, hcase⟩)

theorem domSLe_valid_real {c d : SLe} (h : domSLe c d = true) :
    Dominates c d := by
  simp only [domSLe, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with habs | ⟨hform, hrest⟩
  · exact Or.inl (isAbsurd_sound_real habs)
  · refine Or.inr ⟨formEq_sound_real hform, ?_⟩
    split_ifs at hrest with hdL hdG hdE
    · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
        decide_eq_true_eq] at hrest
      exact Or.inl ⟨hdL, hrest.1, hrest.2⟩
    · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
        decide_eq_true_eq] at hrest
      exact Or.inr (Or.inl ⟨hdG, hrest.1, hrest.2⟩)
    · rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrest
      exact Or.inr (Or.inr ⟨hdE, hrest.1, hrest.2⟩)

theorem unsBounds_valid_real {intVars : List Nat} {b1 b2 : SLe}
    (h : unsBounds intVars b1 b2 = true) : ComplementaryBounds intVars b1 b2 := by
  simp only [unsBounds, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, hform⟩, hInt⟩, hb⟩, hrhs⟩ |
      ⟨⟨⟨⟨⟨h1, h2⟩, hform⟩, hInt⟩, hb⟩, hrhs⟩
  · exact Or.inl ⟨h1, h2, formEq_sound_real hform, formInt_sound_real hInt,
      isIntVal_sound hb, hrhs⟩
  · exact Or.inr ⟨h1, h2, formEq_sound_real hform, formInt_sound_real hInt,
      isIntVal_sound hb, hrhs⟩

end LeanVIPR.Semantics.Rule
