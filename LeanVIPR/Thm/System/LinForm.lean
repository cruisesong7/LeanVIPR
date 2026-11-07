module

public import LeanVIPR.Impl.Checker.Form

@[expose] public section

/-!
# Facts about linear forms

Algebra over the sparse representation, and the agreement of the executable tests in
`LeanVIPR.Impl.Checker.Form` with the notions of `LeanVIPR.Spec.Semantics.LinForm`. Infrastructure: these
are used throughout the soundness development rather than cited on their own.
-/

namespace LeanVIPR.Semantics

open Classical


variable {α : Type*}

/-- Pointwise-`≤` implies `≤` on list sums.
`private`). -/
theorem list_sum_le (l : List α) (f g : α → ℚ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have h0 : f a ≤ g a := h a (by simp)
      have iht : (t.map f).sum ≤ (t.map g).sum :=
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      linarith

theorem eval_combineForm (comb : List (ℚ × Le)) (a : Valuation) :
    (combineForm comb).eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  induction comb with
  | nil => simp [combineForm, LinForm.eval]
  | cons p ps ih =>
      simp only [combineForm, LinForm.eval_append, LinForm.eval_scale, ih,
        List.map_cons, List.sum_cons]

/-- **`lin` soundness (general form).**  If every row used in a nonnegative
combination holds at `a`, so does the combined row.  This is the "implication"
generalization of `farkas_le`. -/
theorem lin_sound (comb : List (ℚ × Le)) (a : Valuation)
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hsat : ∀ p ∈ comb, Le.sat p.2 a) :
    Le.sat (combine comb) a := by
  show (combine comb).form.eval a ≤ (combine comb).rhs
  simp only [combine, eval_combineForm]
  exact list_sum_le comb _ _ fun p hp => mul_le_mul_of_nonneg_left (hsat p hp) (hnn p hp)

theorem isIntVal_cast (n : ℤ) : IsIntVal ((n : ℚ)) := ⟨n, rfl⟩

/-- If every term of a form has integral coefficient and integral variable value at
`a`, the form evaluates to an integer at `a`. -/
theorem LinForm.eval_isInt (f : LinForm) (a : Valuation)
    (h : ∀ t ∈ f, IsIntVal t.coeff ∧ IsIntVal (a t.idx)) :
    IsIntVal (f.eval a) := by
  induction f with
  | nil => exact ⟨0, by simp [LinForm.eval]⟩
  | cons t ts ih =>
      obtain ⟨⟨c, hc⟩, ⟨v, hv⟩⟩ := h t (by simp)
      obtain ⟨m, hm⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
      refine ⟨c * v + m, ?_⟩
      have hm' : (ts.map (fun t => t.coeff * a t.idx)).sum = (m : ℚ) := hm
      simp only [LinForm.eval, List.map_cons, List.sum_cons]
      rw [hc, hv, hm']
      push_cast; ring

/-- **`rnd` soundness.**  If `form ≤ β` at `a` and `form.eval a` is an integer, then
`form ≤ ⌊β⌋` at `a`. -/
theorem rnd_sound (form : LinForm) (β : ℚ) (a : Valuation)
    (hInt : IsIntVal (form.eval a))
    (hsat : Le.sat ⟨form, β⟩ a) :
    Le.sat ⟨form, ((⌊β⌋ : ℤ) : ℚ)⟩ a := by
  obtain ⟨n, hn⟩ := hInt
  show form.eval a ≤ ((⌊β⌋ : ℤ) : ℚ)
  have hsat' : form.eval a ≤ β := hsat
  have hnβ : (n : ℚ) ≤ β := by rw [← hn]; exact hsat'
  have hfloor : n ≤ ⌊β⌋ := Int.le_floor.mpr hnβ
  rw [hn]; exact_mod_cast hfloor

theorem sat_leLower (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leLower i k) a ↔ a i ≤ k := by
  unfold leLower Le.sat LinForm.eval
  simp

theorem sat_leUpper (a : Valuation) (i : Nat) (k : ℚ) :
    Le.sat (leUpper i k) a ↔ k + 1 ≤ a i := by
  unfold leUpper Le.sat LinForm.eval
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor <;> intro h <;> linarith

theorem isIntValB_sound {q : ℚ} (h : isIntValB q = true) : IsIntVal q := by
  have hden : q.den = 1 := by simp only [isIntValB, beq_iff_eq] at h; exact h
  have key : ((q.num : ℤ) : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd
    simpa using hnd
  exact ⟨q.num, key.symm⟩

theorem addTerm_eval (al : List (Nat × ℚ)) (i : Nat) (c : ℚ) (a : Valuation) :
    evalAL (addTerm al i c) a = evalAL al a + c * a i := by
  induction al with
  | nil => simp [addTerm]
  | cons hd tl ih =>
      obtain ⟨j, d⟩ := hd
      by_cases heq : i = j
      · subst heq
        simp only [addTerm, beq_self_eq_true, ite_true, evalAL_cons]; ring
      · have hcond : ¬ ((i == j) = true) := by rw [beq_iff_eq]; exact heq
        simp only [addTerm, ite_eq_right hcond, evalAL_cons, ih]; ring

theorem normForm_foldl_eval (f : LinForm) (al : List (Nat × ℚ)) (a : Valuation) :
    evalAL (f.foldl (fun acc t => addTerm acc t.idx t.coeff) al) a
      = evalAL al a + f.eval a := by
  induction f generalizing al with
  | nil => simp [LinForm.eval]
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih (addTerm al t.idx t.coeff), addTerm_eval]
      have : LinForm.eval (t :: ts) a = t.coeff * a t.idx + LinForm.eval ts a := by
        simp [LinForm.eval]
      rw [this]; ring

theorem normFormAssoc_eval (f : LinForm) (a : Valuation) :
    evalAL (normFormAssoc f) a = f.eval a := by
  simpa [normFormAssoc] using normForm_foldl_eval f [] a

/-! ### The sort-and-merge normalization

`normForm` sorts and folds adjacent equal keys rather than accumulating into an
association list. Both steps leave the value of the form alone: sorting is a permutation
and `evalAL` is a sum, and folding two entries with the same key uses
`c * a i + d * a i = (c + d) * a i`. -/

theorem evalAL_combineAdj : ∀ (l : List (Nat × ℚ)) (a : Valuation),
    evalAL (combineAdj l) a = evalAL l a
  | [], _ => by rw [combineAdj]
  | [_], _ => by rw [combineAdj]
  | (i, c) :: (j, d) :: rest, a => by
      rw [combineAdj]
      split
      case isTrue hij =>
          subst hij
          rw [evalAL_combineAdj ((i, c + d) :: rest) a]
          simp only [evalAL_cons]
          ring
      case isFalse =>
          rw [evalAL_cons, evalAL_combineAdj ((j, d) :: rest) a]
          exact (evalAL_cons _ _ _).symm
  termination_by l _ => l.length

theorem evalAL_perm {l₁ l₂ : List (Nat × ℚ)} (h : l₁.Perm l₂) (a : Valuation) :
    evalAL l₁ a = evalAL l₂ a := by
  unfold evalAL
  exact (h.map _).sum_eq

theorem evalAL_map_form (f : LinForm) (a : Valuation) :
    evalAL (f.map (fun t => (t.idx, t.coeff))) a = f.eval a := by
  unfold evalAL LinForm.eval
  rw [List.map_map]
  rfl

/-! ### The key sort

`sortKV` permutes its input whatever the fuel, which is all the value of a form depends
on. That it also sorts needs the fuel to be sufficient, and is used only to show the
normalized form has distinct keys. -/

/-- Association lists ordered by key. -/
def KeySorted (l : List (Nat × ℚ)) : Prop := l.Pairwise (fun a b => a.1 ≤ b.1)

theorem mergeKV_perm : ∀ (n : Nat) (xs ys : List (Nat × ℚ)),
    (mergeKV n xs ys).Perm (xs ++ ys)
  | 0, xs, ys => by rw [mergeKV]
  | _ + 1, [], ys => by rw [mergeKV, List.nil_append]
  | _ + 1, x :: xs, [] => by rw [mergeKV, List.append_nil]
  | n + 1, x :: xs, y :: ys => by
      rw [mergeKV]
      split
      · exact (mergeKV_perm n xs (y :: ys)).cons x
      · exact ((mergeKV_perm n (x :: xs) ys).cons y).trans List.perm_middle.symm

theorem splitAlt_perm : ∀ (l : List (Nat × ℚ)),
    ((splitAlt l).1 ++ (splitAlt l).2).Perm l
  | [] => by rw [splitAlt]; simp
  | [_] => by rw [splitAlt]; simp
  | a :: b :: rest => by
      rw [splitAlt, List.cons_append]
      exact (List.perm_middle.trans ((splitAlt_perm rest).cons b)).cons a

theorem msortKV_perm : ∀ (n : Nat) (l : List (Nat × ℚ)), (msortKV n l).Perm l
  | 0, l => by rw [msortKV]
  | _ + 1, [] => by rw [msortKV]
  | _ + 1, [_] => by rw [msortKV]
  | n + 1, a :: b :: rest => by
      rw [msortKV]
      exact (mergeKV_perm _ _ _).trans
        (((msortKV_perm n _).append (msortKV_perm n _)).trans (splitAlt_perm (a :: b :: rest)))

theorem sortKV_perm (l : List (Nat × ℚ)) : (sortKV l).Perm l := msortKV_perm _ _

theorem splitAlt_length : ∀ (l : List (Nat × ℚ)),
    (splitAlt l).1.length + (splitAlt l).2.length = l.length ∧
      (splitAlt l).2.length ≤ (splitAlt l).1.length ∧
      (splitAlt l).1.length ≤ (splitAlt l).2.length + 1
  | [] => by rw [splitAlt]; simp
  | [_] => by rw [splitAlt]; simp
  | _ :: _ :: rest => by
      have ih := splitAlt_length rest
      rw [splitAlt]
      simp only [List.length_cons]
      omega

theorem mergeKV_sorted : ∀ (n : Nat) (xs ys : List (Nat × ℚ)),
    xs.length + ys.length ≤ n → KeySorted xs → KeySorted ys → KeySorted (mergeKV n xs ys)
  | 0, xs, ys, hn, _, _ => by
      obtain ⟨rfl, rfl⟩ : xs = [] ∧ ys = [] :=
        ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
      rw [mergeKV, List.append_nil]
      exact List.Pairwise.nil
  | _ + 1, [], ys, _, _, hy => by rw [mergeKV]; exact hy
  | _ + 1, x :: xs, [], _, hx, _ => by rw [mergeKV]; exact hx
  | n + 1, x :: xs, y :: ys, hn, hx, hy => by
      obtain ⟨hxh, hxt⟩ := List.pairwise_cons.mp hx
      obtain ⟨hyh, hyt⟩ := List.pairwise_cons.mp hy
      rw [mergeKV]
      simp only [List.length_cons] at hn
      split
      case isTrue hle =>
          refine List.pairwise_cons.mpr
            ⟨?_, mergeKV_sorted n xs (y :: ys) (by simp only [List.length_cons]; omega) hxt hy⟩
          intro z hz
          rcases List.mem_append.mp ((mergeKV_perm n xs (y :: ys)).mem_iff.mp hz) with h | h
          · exact hxh z h
          · rcases List.mem_cons.mp h with rfl | h
            · exact hle
            · exact le_trans hle (hyh z h)
      case isFalse hlt =>
          refine List.pairwise_cons.mpr
            ⟨?_, mergeKV_sorted n (x :: xs) ys (by simp only [List.length_cons]; omega) hx hyt⟩
          intro z hz
          rcases List.mem_append.mp ((mergeKV_perm n (x :: xs) ys).mem_iff.mp hz) with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · omega
            · exact le_trans (by omega) (hxh z h)
          · exact hyh z h

theorem msortKV_sorted : ∀ (n : Nat) (l : List (Nat × ℚ)),
    l.length ≤ n → KeySorted (msortKV n l)
  | 0, l, hn => by
      rw [msortKV, List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)]
      exact List.Pairwise.nil
  | _ + 1, [], _ => by rw [msortKV]; exact List.Pairwise.nil
  | _ + 1, [a], _ => by
      rw [msortKV]
      exact List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
  | n + 1, a :: b :: rest, hn => by
      have hlen := splitAlt_length (a :: b :: rest)
      simp only [List.length_cons] at hn hlen
      rw [msortKV]
      refine mergeKV_sorted _ _ _ ?_
        (msortKV_sorted n _ (by omega)) (msortKV_sorted n _ (by omega))
      rw [(msortKV_perm n _).length_eq, (msortKV_perm n _).length_eq]

theorem sortKV_sorted (l : List (Nat × ℚ)) : KeySorted (sortKV l) :=
  msortKV_sorted _ _ (le_refl _)

/-! ### Dense accumulation

`arrSum arr a k` is the value of the first `k` slots of a coefficient array. The two
facts needed are that `collectNZ` computes it (dropping zero slots, which contribute
nothing) and that adding `c` at index `i` adds `c * a i` to it. -/

/-- Value of the first `k` slots of a coefficient array. -/
def arrSum (arr : Array ℚ) (a : Valuation) : Nat → ℚ
  | 0 => 0
  | i + 1 => arr[i]! * a i + arrSum arr a i

theorem getBang_lt {arr : Array ℚ} {i : Nat} (h : i < arr.size) : arr[i]! = arr[i] := by
  simp only [Array.getElem!_eq_getD, Array.getD]
  split
  · rfl
  · omega

theorem getBang_set_self {arr : Array ℚ} {i : Nat} (h : i < arr.size) (v : ℚ) :
    (arr.set! i v)[i]! = v := by
  rw [Array.set!_eq_setIfInBounds, getBang_lt (by simpa using h)]
  exact Array.getElem_setIfInBounds_self _

theorem getBang_set_ne {arr : Array ℚ} {i j : Nat} (hj : j < arr.size) (hne : j ≠ i)
    (v : ℚ) : (arr.set! i v)[j]! = arr[j]! := by
  rw [Array.set!_eq_setIfInBounds, getBang_lt (by simpa using hj), getBang_lt hj]
  exact Array.getElem_setIfInBounds_ne hj (fun h => hne h.symm)

theorem size_denseAccum : ∀ (n : Nat) (f : LinForm), (denseAccum n f).size = n
  | n, f => by
      rw [denseAccum]
      suffices gen : ∀ (g : LinForm) (arr : Array ℚ),
          (g.foldl (fun b t => b.set! t.idx (b[t.idx]! + t.coeff)) arr).size = arr.size by
        rw [gen]; simp
      intro g
      induction g with
      | nil => intro arr; rfl
      | cons hd tl ih =>
          intro arr
          rw [List.foldl_cons, ih, Array.size_set!]

theorem evalAL_collectNZ : ∀ (arr : Array ℚ) (k : Nat) (acc : List (Nat × ℚ))
    (a : Valuation), k ≤ arr.size →
    evalAL (collectNZ arr k acc) a = arrSum arr a k + evalAL acc a
  | _, 0, _, _, _ => by rw [collectNZ, arrSum]; ring
  | arr, k + 1, acc, a, hk => by
      rw [collectNZ, evalAL_collectNZ arr k _ a (by omega), arrSum]
      split
      case isTrue hz =>
          have hzz : arr[k]! = 0 := by simpa using hz
          rw [hzz]; ring
      case isFalse => rw [evalAL_cons]; ring

/-- Adding `c` into slot `i` adds `c * a i` to the value of the array. -/
theorem arrSum_set : ∀ (arr : Array ℚ) (a : Valuation) (i : Nat) (c : ℚ) (k : Nat),
    i < arr.size → k ≤ arr.size →
    arrSum (arr.set! i (arr[i]! + c)) a k
      = arrSum arr a k + (if i < k then c * a i else 0)
  | _, _, _, _, 0, _, _ => by simp [arrSum]
  | arr, a, i, c, k + 1, hi, hk => by
      rw [arrSum, arrSum, arrSum_set arr a i c k hi (by omega)]
      by_cases hik : i = k
      · subst hik
        rw [getBang_set_self hi]
        simp only [lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
        ring
      · rw [getBang_set_ne (by omega) (fun h => hik h.symm)]
        by_cases hlt : i < k
        · simp only [hlt, ite_true, show i < k + 1 from by omega]
          ring
        · have hnk : ¬ i < k + 1 := by omega
          simp only [hlt, ite_false, hnk]
          ring

private theorem le_foldl_width : ∀ (l : LinForm) (w : Nat),
    w ≤ l.foldl (fun w t => max w (t.idx + 1)) w
  | [], w => le_refl w
  | b :: bs, w => le_trans (le_max_left w (b.idx + 1)) (le_foldl_width bs _)

theorem lt_formWidth {f : LinForm} {t : Term} (h : t ∈ f) : t.idx < formWidth f := by
  suffices gen : ∀ (g : LinForm) (w : Nat), t ∈ g →
      t.idx < g.foldl (fun w t => max w (t.idx + 1)) w from gen f 0 h
  intro g
  induction g with
  | nil => intro _ hmem; simp at hmem
  | cons hd tl ih =>
      intro w hmem
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right w _))
          (le_foldl_width tl _)
      · exact ih _ hmem

/-- Accumulating `g` into an array wide enough for it adds `g`'s value to the array's. -/
theorem arrSum_denseAccum : ∀ (g : LinForm) (arr : Array ℚ) (n : Nat) (a : Valuation),
    arr.size = n → (∀ t ∈ g, t.idx < n) →
    arrSum (g.foldl (fun b t => b.set! t.idx (b[t.idx]! + t.coeff)) arr) a n
      = arrSum arr a n + LinForm.eval g a
  | [], arr, n, a, _, _ => by simp [LinForm.eval]
  | t :: ts, arr, n, a, hn, hb => by
      have hlt : t.idx < arr.size := by rw [hn]; exact hb t (by simp)
      rw [List.foldl_cons,
        arrSum_denseAccum ts _ n a (by rw [Array.size_set!, hn])
          (fun u hu => hb u (by simp [hu])),
        arrSum_set arr a t.idx t.coeff n hlt (le_of_eq hn.symm)]
      have hcons : LinForm.eval (t :: ts) a = t.coeff * a t.idx + LinForm.eval ts a := by
        simp [LinForm.eval]
      rw [hcons]
      simp only [show t.idx < n from by rw [← hn]; exact hlt, ite_true]
      ring

private theorem arrSum_replicate_zero (n : Nat) (a : Valuation) :
    ∀ k ≤ n, arrSum (Array.replicate n (0 : ℚ)) a k = 0
  | 0, _ => by rw [arrSum]
  | k + 1, hk => by
      rw [arrSum, arrSum_replicate_zero n a k (by omega),
        getBang_lt (by simpa using (by omega : k < n)), Array.getElem_replicate]
      ring

theorem normFormDense_eval (f : LinForm) (a : Valuation) :
    evalAL (normFormDense f) a = f.eval a := by
  rw [normFormDense]
  rw [evalAL_collectNZ _ _ _ a (by rw [size_denseAccum]), denseAccum,
    arrSum_denseAccum f _ (formWidth f) a (by simp) (fun t ht => lt_formWidth ht),
    arrSum_replicate_zero _ a _ (le_refl _), evalAL_nil]
  ring

theorem normFormSort_eval (f : LinForm) (a : Valuation) :
    evalAL (normFormSort f) a = f.eval a := by
  rw [normFormSort, evalAL_combineAdj, evalAL_perm (sortKV_perm _) a, evalAL_map_form]

theorem normForm_eval (f : LinForm) (a : Valuation) : evalAL (normForm f) a = f.eval a := by
  rw [normForm]
  split
  · exact normFormDense_eval f a
  · exact normFormSort_eval f a

/-- The two normalizations agree on the value of the form, which is all the soundness
argument asks of either. -/
theorem normForm_eval_eq_assoc (f : LinForm) (a : Valuation) :
    evalAL (normForm f) a = evalAL (normFormAssoc f) a := by
  rw [normForm_eval, normFormAssoc_eval]

end LeanVIPR.Semantics
