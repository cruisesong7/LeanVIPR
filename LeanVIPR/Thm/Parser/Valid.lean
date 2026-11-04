module

public import LeanVIPR.Impl.Parser
public import LeanVIPR.Spec.Grammar
import Mathlib.Data.List.Sort

@[expose] public section

/-!
# The validator decides exactly well-formedness

`validateVipr_eq_ok_iff` lets `IsValid` replace `validateVipr` in the parser's
correctness statement, which is what removes the last implementation function from it.

The only real content is that an adjacent-duplicate scan over a sorted list decides
`List.Nodup`. The validator sorts because deciding `Nodup` directly is quadratic and
the corpus has reasons citing over three hundred rows; sorting with `mergeSort` rather
than `qsort` keeps that cheap while leaving it provable, since `List.mergeSort_perm` and
`List.pairwise_mergeSort` are exactly the two facts the argument needs and `Array.qsort`
has neither.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Semantics

/-! ## Plumbing -/

private theorem bind_unit_eq_ok_iff {x y : Except String Unit} :
    (x >>= fun _ => y) = .ok () ↔ (x = .ok () ∧ y = .ok ()) := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok u => cases u; simp [bind, Except.bind]

theorem checkAll_eq_ok_iff {α : Type} {f : α → Except String Unit} :
    ∀ {l : List α}, checkAll f l = .ok () ↔ ∀ a ∈ l, f a = .ok ()
  | [] => by simp [checkAll]
  | a :: as => by
      rw [checkAll, bind_unit_eq_ok_iff, @checkAll_eq_ok_iff α f as]
      constructor
      · rintro ⟨hfa, h⟩ b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hfa
        · exact h b hb
      · intro h
        exact ⟨h a (by simp), fun b hb => h b (by simp [hb])⟩

private theorem find?_ge_eq_none_iff {nvar : Nat} {idxs : List Nat} :
    idxs.find? (fun i => decide (nvar ≤ i)) = none ↔ ∀ i ∈ idxs, i < nvar := by
  rw [List.find?_eq_none]
  constructor
  · intro h i hi
    have := h i hi
    simp only [decide_eq_true_eq] at this
    omega
  · intro h i hi
    simpa using Nat.not_le.mpr (h i hi)

private theorem find?_key_ge_eq_none_iff {nvar : Nat} {vals : List (Nat × ℚ)} :
    vals.find? (fun p => decide (nvar ≤ p.1)) = none ↔ ∀ p ∈ vals, p.1 < nvar := by
  rw [List.find?_eq_none]
  constructor
  · intro h p hp
    have := h p hp
    simp only [decide_eq_true_eq] at this
    omega
  · intro h p hp
    simpa using Nat.not_le.mpr (h p hp)

/-! ## Sorting -/

private theorem pairwise_mergeSort_le (idxs : List Nat) :
    (idxs.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) idxs
  exact h.imp (by intro a b hab; simpa using hab)

private theorem pairwise_mergeSort_key (vals : List (Nat × ℚ)) :
    (vals.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise (fun a b => a.1 ≤ b.1) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat × ℚ => decide (a.1 ≤ b.1))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) vals
  exact h.imp (by intro a b hab; simpa using hab)

/-! ## Distinctness -/

theorem firstAdjacentDup_eq_none_of_nodup :
    ∀ {l : List Nat}, l.Nodup → firstAdjacentDup l = none
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      have hab : a ≠ b := fun he => (List.nodup_cons.mp h).1 (by simp [he])
      rw [firstAdjacentDup]
      split
      case isTrue he => exact absurd he hab
      case isFalse => exact firstAdjacentDup_eq_none_of_nodup (List.nodup_cons.mp h).2

/-- On a sorted list, finding no adjacent duplicate means there is no duplicate at all:
equal values in a sorted list are forced to be adjacent. -/
theorem nodup_of_firstAdjacentDup_eq_none :
    ∀ {l : List Nat}, l.Pairwise (· ≤ ·) → firstAdjacentDup l = none → l.Nodup
  | [], _, _ => List.nodup_nil
  | [_], _, _ => by simp
  | a :: b :: rest, hp, h => by
      rw [firstAdjacentDup] at h
      split at h
      case isTrue => exact absurd h (by simp)
      case isFalse hab =>
        have hpb : (b :: rest).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hp).2
        refine List.nodup_cons.mpr ⟨?_, nodup_of_firstAdjacentDup_eq_none hpb h⟩
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hab rfl
        · have h1 : a ≤ b := (List.pairwise_cons.mp hp).1 b (by simp)
          have h2 : b ≤ a := (List.pairwise_cons.mp hpb).1 a hmem
          exact hab (le_antisymm h1 h2)


private theorem checkDistinct_split {what : String} {idxs : List Nat} :
    checkDistinct what idxs = .ok () ↔
      firstAdjacentDup (idxs.mergeSort (fun a b => decide (a ≤ b))) = none := by
  unfold checkDistinct
  cases firstAdjacentDup (idxs.mergeSort (fun a b => decide (a ≤ b))) with
  | none => simp
  | some i => simp

theorem checkDistinct_eq_ok_iff {what : String} {idxs : List Nat} :
    checkDistinct what idxs = .ok () ↔ idxs.Nodup := by
  rw [checkDistinct_split]
  have hperm := List.mergeSort_perm idxs (fun a b => decide (a ≤ b))
  exact ⟨fun h => hperm.nodup_iff.mp
      (nodup_of_firstAdjacentDup_eq_none (pairwise_mergeSort_le idxs) h),
    fun h => firstAdjacentDup_eq_none_of_nodup (hperm.nodup_iff.mpr h)⟩

private theorem checkIndices_split {nvar : Nat} {what : String} {idxs : List Nat} :
    checkIndices nvar what idxs = .ok () ↔
      (idxs.find? (fun i => decide (nvar ≤ i)) = none ∧
        checkDistinct what idxs = .ok ()) := by
  unfold checkIndices
  cases idxs.find? (fun i => decide (nvar ≤ i)) with
  | none => simp
  | some i => simp

theorem checkIndices_eq_ok_iff {nvar : Nat} {what : String} {idxs : List Nat} :
    checkIndices nvar what idxs = .ok () ↔ IndicesOk nvar idxs := by
  rw [checkIndices_split, checkDistinct_eq_ok_iff, find?_ge_eq_none_iff]
  exact Iff.rfl

theorem checkFormIndices_eq_ok_iff {nvar : Nat} {what : String} {f : LinForm} :
    checkFormIndices nvar what f = .ok () ↔ IndicesOk nvar (f.map (·.idx)) :=
  checkIndices_eq_ok_iff

/-! ## Solution vectors -/

theorem firstKeyConflict_eq_none_of_functional : ∀ {l : List (Nat × ℚ)},
    (∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p.2 = q.2) → firstKeyConflict l = none
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      have hne : ¬ (a.1 = b.1 ∧ a.2 ≠ b.2) := fun hc =>
        hc.2 (h a (by simp) b (by simp) hc.1)
      rw [firstKeyConflict]
      split
      case isTrue hc => exact absurd hc hne
      case isFalse =>
        exact firstKeyConflict_eq_none_of_functional
          (fun p hp q hq => h p (by simp [hp]) q (by simp [hq]))

/-- On a list sorted by index, finding no adjacent conflict means the vector is
single-valued: entries with equal indices are forced to be adjacent. -/
theorem functional_of_firstKeyConflict_eq_none : ∀ {l : List (Nat × ℚ)},
    l.Pairwise (fun a b => a.1 ≤ b.1) → firstKeyConflict l = none →
      ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p.2 = q.2
  | [], _, _ => by simp
  | [x], _, _ => by
      intro p hp q hq _
      obtain rfl : p = x := by simpa using hp
      obtain rfl : q = p := by simpa using hq
      rfl
  | a :: b :: rest, hp, h => by
      rw [firstKeyConflict] at h
      split at h
      case isTrue => exact absurd h (by simp)
      case isFalse hc =>
        have hpb : (b :: rest).Pairwise (fun a b => a.1 ≤ b.1) :=
          (List.pairwise_cons.mp hp).2
        have ih := functional_of_firstKeyConflict_eq_none hpb h
        have hkeyA : ∀ q ∈ b :: rest, a.1 = q.1 → a.2 = q.2 := by
          intro q hq hk
          have hab : a.1 ≤ b.1 := (List.pairwise_cons.mp hp).1 b (by simp)
          have hbq : b.1 ≤ q.1 := by
            rcases List.mem_cons.mp hq with rfl | hq
            · exact le_rfl
            · exact (List.pairwise_cons.mp hpb).1 q hq
          have h1 : a.1 = b.1 := by omega
          have hab2 : a.2 = b.2 := by
            by_contra hne
            exact hc ⟨h1, hne⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hab2
          · exact hab2.trans (ih b (by simp) q (by simp [hq]) (by omega))
        intro p hpm q hqm hk
        rcases List.mem_cons.mp hpm with rfl | hp2
        · rcases List.mem_cons.mp hqm with rfl | hq2
          · rfl
          · exact hkeyA q hq2 hk
        · rcases List.mem_cons.mp hqm with rfl | hq2
          · exact (hkeyA p hp2 hk.symm).symm
          · exact ih p hp2 q hq2 hk

private theorem checkSolution_split {nvar : Nat} {what : String}
    {vals : List (Nat × ℚ)} : checkSolution nvar what vals = .ok () ↔
      (vals.find? (fun p => decide (nvar ≤ p.1)) = none ∧
        firstKeyConflict (vals.mergeSort (fun a b => decide (a.1 ≤ b.1))) = none) := by
  unfold checkSolution
  cases vals.find? (fun p => decide (nvar ≤ p.1)) with
  | some p => simp
  | none =>
      cases firstKeyConflict (vals.mergeSort (fun a b => decide (a.1 ≤ b.1))) with
      | none => simp
      | some i => simp

theorem checkSolution_eq_ok_iff {nvar : Nat} {what : String} {vals : List (Nat × ℚ)} :
    checkSolution nvar what vals = .ok () ↔ SolutionOk nvar vals := by
  rw [checkSolution_split, find?_key_ge_eq_none_iff]
  have hperm := List.mergeSort_perm vals (fun a b => decide (a.1 ≤ b.1))
  constructor
  · rintro ⟨hr, hk⟩
    refine ⟨hr, fun p hp q hq hkey => ?_⟩
    exact functional_of_firstKeyConflict_eq_none (pairwise_mergeSort_key vals) hk
      p (hperm.mem_iff.mpr hp) q (hperm.mem_iff.mpr hq) hkey
  · rintro ⟨hr, hfun⟩
    exact ⟨hr, firstKeyConflict_eq_none_of_functional
      (fun p hp q hq => hfun p (hperm.mem_iff.mp hp) q (hperm.mem_iff.mp hq))⟩

/-! ## The final-use rule -/

theorem finalUseViolations_eq_nil_iff (v : Vipr) :
    ∀ (pos : Nat) (ds : List ViprDer), finalUseViolations v pos ds = [] ↔
      ∀ before d after, ds = before ++ d :: after →
        ∀ k ∈ reasonRefs d.reason,
          ¬ usedAfterFinal v (v.cons.size + pos + before.length) k
  | pos, [] => by
      simp only [finalUseViolations, true_iff]
      intro before d after hsplit
      exact absurd hsplit.symm (by cases before <;> simp)
  | pos, d :: ds => by
      rw [finalUseViolations, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
        finalUseViolations_eq_nil_iff v (pos + 1) ds]
      constructor
      · rintro ⟨hhead, htail⟩ before d' after hsplit k hk
        cases before with
        | nil =>
            obtain ⟨rfl, rfl⟩ : d = d' ∧ ds = after := by simpa using hsplit
            have hnone := hhead k hk
            simp only [List.length_nil, Nat.add_zero]
            split at hnone
            case isTrue => exact absurd hnone (by simp)
            case isFalse hcond => exact hcond
        | cons e before' =>
            obtain ⟨rfl, hrest⟩ : d = e ∧ ds = before' ++ d' :: after := by
              simpa using hsplit
            have := htail before' d' after hrest k hk
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · intro h
        refine ⟨fun k hk => ?_, ?_⟩
        · have hok := h [] d ds rfl k hk
          simp only [List.length_nil, Nat.add_zero] at hok
          split
          case isTrue hbad => exact absurd hbad hok
          case isFalse => rfl
        · intro before d' after hrest k hk
          have := h (d :: before) d' after (by simpa using hrest) k hk
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private theorem checkFinalUse_split {v : Vipr} :
    checkFinalUse v = .ok () ↔ finalUseViolations v 0 v.ders.toList = [] := by
  unfold checkFinalUse
  cases finalUseViolations v 0 v.ders.toList with
  | nil => simp
  | cons x xs => simp

theorem checkFinalUse_eq_ok_iff {v : Vipr} :
    checkFinalUse v = .ok () ↔ FinalUseOk v := by
  rw [checkFinalUse_split, finalUseViolations_eq_nil_iff]
  simp only [Nat.add_zero]
  exact Iff.rfl

/-! ## The validator -/

private theorem validateVipr_split {v : Vipr} :
    validateVipr v = .ok () ↔
      (v.intVars.find? (fun i => decide (v.varNames.size ≤ i)) = none ∧
        checkIndices v.varNames.size "OBJ" (v.objTerms.map Prod.fst) = .ok () ∧
        (∀ c ∈ v.cons.toList,
          checkFormIndices v.varNames.size s!"CON {c.name}" c.form = .ok ()) ∧
        (∀ s ∈ v.sols.toList,
          checkSolution v.varNames.size s!"SOL {s.1}" s.2 = .ok ()) ∧
        (∀ d ∈ v.ders.toList,
          checkFormIndices v.varNames.size s!"DER {d.name}" d.form = .ok () ∧
            checkDistinct s!"DER {d.name} reason" (reasonMultipliers d.reason) = .ok ()) ∧
        checkFinalUse v = .ok ()) := by
  unfold validateVipr
  cases v.intVars.find? (fun i => decide (v.varNames.size ≤ i)) with
  | some i => simp
  | none =>
      simp only [bind_unit_eq_ok_iff, checkAll_eq_ok_iff, true_and]

/-- **The validator decides exactly `IsValid`.** -/
theorem validateVipr_eq_ok_iff {v : Vipr} : validateVipr v = .ok () ↔ IsValid v := by
  rw [validateVipr_split, find?_ge_eq_none_iff, checkIndices_eq_ok_iff]
  simp only [checkFormIndices_eq_ok_iff, checkSolution_eq_ok_iff,
    checkDistinct_eq_ok_iff, checkFinalUse_eq_ok_iff]
  exact Iff.rfl

end LeanVIPR.Parser
