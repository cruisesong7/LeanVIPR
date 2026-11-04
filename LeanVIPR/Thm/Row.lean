module

public import LeanVIPR.Impl.Rules
public import LeanVIPR.Thm.LinForm

@[expose] public section

/-!
# Facts about sensed rows

Infrastructure for the soundness development: how `SLe` relates to the unsensed `Le`,
and basic facts about pools and assumption sets.
-/

namespace LeanVIPR.Semantics


theorem scomb_eval (comb : List (ℚ × SLe)) (a : Valuation) :
    (scomb comb).form.eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  simp only [scomb, combine, eval_combineForm, List.map_map]
  rfl

theorem scomb_rhs (comb : List (ℚ × SLe)) :
    (scomb comb).rhs = (comb.map (fun p => p.1 * p.2.rhs)).sum := by
  simp only [scomb, combine, List.map_map]
  rfl

theorem suitLeB_sound {cs} (h : suitLeB cs = true) : ∀ p ∈ cs, p.1 * senseSign p.2.sense ≤ 0 :=
  fun p hp => of_decide_eq_true ((List.all_eq_true.mp h) p hp)

theorem suitGeB_sound {cs} (h : suitGeB cs = true) : ∀ p ∈ cs, 0 ≤ p.1 * senseSign p.2.sense :=
  fun p hp => of_decide_eq_true ((List.all_eq_true.mp h) p hp)

@[simp] theorem alIsZero_normForm (f : LinForm) : alIsZero (normForm f) = formIsZero f := rfl

@[simp] theorem alIntB_normForm (intVars : List Nat) (f : LinForm) :
    alIntB intVars (normForm f) = formIntB intVars f := rfl

@[simp] theorem alIsZero_alExtend_normForm (f g : LinForm) :
    alIsZero (alExtend (normForm f) (sNegForm g)) = formEq f g := by
  simp only [alExtend, normForm, formEq, formIsZero, alIsZero, List.foldl_append]

theorem intEntryB_sound {intVars : List Nat} {p : Nat × ℚ}
    (h : intEntryB intVars p = true) :
    p.2 = 0 ∨ (IsIntVal p.2 ∧ p.1 ∈ intVars) := by
  simp only [intEntryB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with h | ⟨hq, hidx⟩
  · exact Or.inl h
  · exact Or.inr ⟨isIntValB_sound hq, hidx⟩

theorem mem_collectAsms {pool : SPool} {comb : List (ℚ × Nat)}
    {p : ℚ × Nat} (hp : p ∈ comb) {t : SLe} (ht : t ∈ spoolAsm pool p.2) :
    t ∈ collectAsms pool comb := by
  induction comb with
  | nil => simp at hp
  | cons q qs ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Finset.mem_union_left _ ht
      · exact Finset.mem_union_right _ (ih hp)

end LeanVIPR.Semantics
