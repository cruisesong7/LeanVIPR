module

public import LeanVIPR.Completeness.GeneralCompleteness

@[expose] public section

/-!
# Completeness for one unbounded integer variable

For a canonical rational system over one integer variable, infeasibility has a
finite VIPR proof even without input bounds.  If the LP relaxation is feasible,
integer infeasibility forces at least one lower and one upper row.  Scaling and
rounding one row of each kind derives finite integral bounds, reducing to the
bounded completeness theorem.
-/

namespace LeanVIPR.Completeness.OneDimensionalCompleteness

open LeanVIPR.Cert LeanVIPR.Completeness.BoundedCompleteness
  LeanVIPR.Completeness.FarkasCompleteness LeanVIPR.Completeness.FourierMotzkin
  LeanVIPR.Completeness.IntegerProjection

def OneVarCanonical (idx : Nat) (rows : List Le) : Prop :=
  ∀ row ∈ rows,
    row.form = [] ∨
      ∃ q : ℚ, q ≠ 0 ∧ row.form = [⟨idx, q⟩]

theorem canonicalForm_indices_nodup (form : LinForm) :
    ((canonicalForm form).map Term.idx).Nodup := by
  simpa [canonicalForm, Function.comp_def] using
    (toFinsupp form).support.nodup_toList

theorem canonical_one_var {idx : Nat} {form : LinForm}
    (hsupported : ∀ term ∈ canonicalForm form, term.idx ∈ [idx]) :
    canonicalForm form = [] ∨
      ∃ q : ℚ, q ≠ 0 ∧ canonicalForm form = [⟨idx, q⟩] := by
  cases hform : canonicalForm form with
  | nil => exact Or.inl rfl
  | cons term tail =>
      right
      have htermIdx : term.idx = idx := by
        simpa using hsupported term (by simp [hform])
      have htail : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro candidate hcandidate
        have hcandidateIdx : candidate.idx = idx := by
          simpa using hsupported candidate (by
            rw [hform]
            exact List.mem_cons_of_mem _ hcandidate)
        have hnodup := canonicalForm_indices_nodup form
        rw [hform, List.map_cons, List.nodup_cons] at hnodup
        apply hnodup.1
        have hmem :
            candidate.idx ∈ List.map Term.idx tail :=
          List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
        simpa [htermIdx, hcandidateIdx] using hmem
      have hnonzero : term.coeff ≠ 0 :=
        (mem_canonicalForm (by
          rw [hform]
          exact List.mem_cons_self)).2
      refine ⟨term.coeff, hnonzero, ?_⟩
      rcases term with ⟨termIdx, coeff⟩
      simp only at htermIdx
      subst termIdx
      simp [htail]

theorem integerRows_oneVarCanonical (rows : List Le) (idx : Nat) :
    OneVarCanonical idx (integerRows rows [idx]) := by
  intro row hrow
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hrow
  have hsupported :
      ∀ term ∈ canonicalForm raw.form, term.idx ∈ [idx] := by
    intro term hterm
    exact integerRows_integral rows [idx]
      (canonicalRow raw) (List.mem_map.mpr ⟨raw, hraw, rfl⟩)
      term hterm
  simpa [canonicalRow] using canonical_one_var hsupported

theorem floor_cast_le (q : ℚ) : ((⌊q⌋ : ℤ) : ℚ) ≤ q :=
  Int.floor_le q

theorem le_ceil_cast (q : ℚ) : q ≤ ((⌈q⌉ : ℤ) : ℚ) :=
  Int.le_ceil q

theorem lowerRows_nonempty {idx : Nat} {rows : List Le}
    (hcanonical : OneVarCanonical idx rows)
    (hfeasible : ∃ a : Valuation, ∀ row ∈ rows, Le.sat row a)
    (hno : NoIntSolution [idx] rows) :
    lowerRows idx rows ≠ [] := by
  rintro hlower
  obtain ⟨a, hrows⟩ := hfeasible
  let value : ℚ := ((⌊a idx⌋ : ℤ) : ℚ)
  let b := assignVar a idx value
  apply hno b
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ⟨⌊a idx⌋, by simp [b, value]⟩
  · intro row hrow
    rcases hcanonical row hrow with hzero | ⟨q, hq, hform⟩
    · change LinForm.eval row.form b ≤ row.rhs
      rw [hzero]
      have hsat := hrows row hrow
      change LinForm.eval row.form a ≤ row.rhs at hsat
      rw [hzero] at hsat
      simpa [LinForm.eval] using hsat
    · have hqNonneg : 0 ≤ q := by
        by_contra hneg
        have hqNeg : q < 0 := lt_of_not_ge hneg
        have hmem : row ∈ lowerRows idx rows := by
          simp [lowerRows, hrow, hform, coeffAt, hqNeg]
        simp [hlower] at hmem
      have hvalue : value ≤ a idx := floor_cast_le (a idx)
      change LinForm.eval row.form b ≤ row.rhs
      rw [hform]
      have hsat := hrows row hrow
      change LinForm.eval row.form a ≤ row.rhs at hsat
      rw [hform] at hsat
      simp only [LinForm.eval, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at hsat ⊢
      change q * b idx ≤ row.rhs
      simpa [b] using
        le_trans (mul_le_mul_of_nonneg_left hvalue hqNonneg) hsat

theorem upperRows_nonempty {idx : Nat} {rows : List Le}
    (hcanonical : OneVarCanonical idx rows)
    (hfeasible : ∃ a : Valuation, ∀ row ∈ rows, Le.sat row a)
    (hno : NoIntSolution [idx] rows) :
    upperRows idx rows ≠ [] := by
  rintro hupper
  obtain ⟨a, hrows⟩ := hfeasible
  let value : ℚ := ((⌈a idx⌉ : ℤ) : ℚ)
  let b := assignVar a idx value
  apply hno b
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ⟨⌈a idx⌉, by simp [b, value]⟩
  · intro row hrow
    rcases hcanonical row hrow with hzero | ⟨q, hq, hform⟩
    · change LinForm.eval row.form b ≤ row.rhs
      rw [hzero]
      have hsat := hrows row hrow
      change LinForm.eval row.form a ≤ row.rhs at hsat
      rw [hzero] at hsat
      simpa [LinForm.eval] using hsat
    · have hqNonpos : q ≤ 0 := by
        by_contra hpos
        have hqPos : 0 < q := lt_of_not_ge hpos
        have hmem : row ∈ upperRows idx rows := by
          simp [upperRows, hrow, hform, coeffAt, hqPos]
        simp [hupper] at hmem
      have hvalue : a idx ≤ value := le_ceil_cast (a idx)
      change LinForm.eval row.form b ≤ row.rhs
      rw [hform]
      have hsat := hrows row hrow
      change LinForm.eval row.form a ≤ row.rhs at hsat
      rw [hform] at hsat
      simp only [LinForm.eval, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at hsat ⊢
      change q * b idx ≤ row.rhs
      simpa [b] using
        le_trans (mul_le_mul_of_nonpos_left hvalue hqNonpos) hsat

def lowerMultiplier (idx : Nat) (row : Le) : ℚ :=
  -1 / coeffAt idx row.form

def upperMultiplier (idx : Nat) (row : Le) : ℚ :=
  1 / coeffAt idx row.form

def roundedLower (idx : Nat) (row : Le) : ℤ :=
  -⌊lowerMultiplier idx row * row.rhs⌋

def roundedUpper (idx : Nat) (row : Le) : ℤ :=
  ⌊upperMultiplier idx row * row.rhs⌋

theorem lower_deriveRow {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : q < 0) :
    deriveRow [(lowerMultiplier idx row, row)] true =
      leUpper idx ((roundedLower idx row - 1 : ℤ) : ℚ) := by
  cases row with
  | mk form rhs =>
      simp only at hform
      subst form
      simp [deriveRow, lowerMultiplier, roundedLower, leUpper,
        coeffAt, combine, combineForm, LinForm.scale]
      exact div_mul_cancel₀ (-1 : ℚ) (ne_of_lt hq)

theorem upper_deriveRow {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : 0 < q) :
    deriveRow [(upperMultiplier idx row, row)] true =
      leLower idx ((roundedUpper idx row : ℤ) : ℚ) := by
  cases row with
  | mk form rhs =>
      simp only at hform
      subst form
      simp [deriveRow, upperMultiplier, roundedUpper, leLower,
        coeffAt, combine, combineForm, LinForm.scale]
      simpa [one_div] using div_mul_cancel₀ (1 : ℚ) (ne_of_gt hq)

theorem lower_combineForm {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : q < 0) :
    combineForm [(lowerMultiplier idx row, row)] = [⟨idx, -1⟩] := by
  cases row with
  | mk form rhs =>
      simp only at hform
      subst form
      simp [lowerMultiplier, coeffAt, combineForm, LinForm.scale]
      exact div_mul_cancel₀ (-1 : ℚ) (ne_of_lt hq)

theorem upper_combineForm {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : 0 < q) :
    combineForm [(upperMultiplier idx row, row)] = [⟨idx, 1⟩] := by
  cases row with
  | mk form rhs =>
      simp only at hform
      subst form
      simp [upperMultiplier, coeffAt, combineForm, LinForm.scale]
      simpa [one_div] using div_mul_cancel₀ (1 : ℚ) (ne_of_gt hq)

theorem lowerMultiplier_nonnegative {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : q < 0) :
    0 ≤ lowerMultiplier idx row := by
  rw [lowerMultiplier, hform]
  simp only [coeffAt, ite_true, add_zero]
  exact le_of_lt (div_pos_of_neg_of_neg (by norm_num) hq)

theorem upperMultiplier_nonnegative {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : 0 < q) :
    0 ≤ upperMultiplier idx row := by
  rw [upperMultiplier, hform]
  simp only [coeffAt, ite_true, add_zero]
  exact div_nonneg (by norm_num) (le_of_lt hq)

theorem lower_derive_valid {idx : Nat} {row : Le} {q : ℚ}
    {rows : List Le} {tree : RefTree} {isInt : Nat → Prop}
    (hrow : row ∈ rows) (hform : row.form = [⟨idx, q⟩])
    (hq : q < 0) (hidx : isInt idx)
    (htree :
      RefTree.Valid isInt
        (deriveRow [(lowerMultiplier idx row, row)] true :: rows) tree) :
    RefTree.Valid isInt rows
      (.derive [(lowerMultiplier idx row, row)] true tree) := by
  refine ⟨?_, ?_, ?_, htree⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact lowerMultiplier_nonnegative hform hq
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hrow
  · intro _
    rw [lower_combineForm hform hq]
    intro term hterm
    simp only [List.mem_singleton] at hterm
    subst term
    exact ⟨isIntVal_cast (-1), hidx⟩

theorem upper_derive_valid {idx : Nat} {row : Le} {q : ℚ}
    {rows : List Le} {tree : RefTree} {isInt : Nat → Prop}
    (hrow : row ∈ rows) (hform : row.form = [⟨idx, q⟩])
    (hq : 0 < q) (hidx : isInt idx)
    (htree :
      RefTree.Valid isInt
        (deriveRow [(upperMultiplier idx row, row)] true :: rows) tree) :
    RefTree.Valid isInt rows
      (.derive [(upperMultiplier idx row, row)] true tree) := by
  refine ⟨?_, ?_, ?_, htree⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact upperMultiplier_nonnegative hform hq
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hrow
  · intro _
    rw [upper_combineForm hform hq]
    intro term hterm
    simp only [List.mem_singleton] at hterm
    subst term
    exact ⟨isIntVal_cast 1, hidx⟩

theorem exists_lower_row {idx : Nat} {rows : List Le}
    (hcanonical : OneVarCanonical idx rows)
    (hfeasible : ∃ a : Valuation, ∀ row ∈ rows, Le.sat row a)
    (hno : IntegerProjection.NoIntSolution [idx] rows) :
    ∃ row q, row ∈ rows ∧ q < 0 ∧ row.form = [⟨idx, q⟩] := by
  have hnonempty := lowerRows_nonempty hcanonical hfeasible hno
  obtain ⟨row, hrowLower⟩ :=
    List.exists_mem_of_ne_nil (lowerRows idx rows) hnonempty
  have hrow : row ∈ rows := (List.mem_filter.mp hrowLower).1
  have hcoeff : coeffAt idx row.form < 0 :=
    of_decide_eq_true (List.mem_filter.mp hrowLower).2
  rcases hcanonical row hrow with hzero | ⟨q, hq, hform⟩
  · simp [hzero] at hcoeff
  · refine ⟨row, q, hrow, ?_, hform⟩
    simpa [hform, coeffAt] using hcoeff

theorem exists_upper_row {idx : Nat} {rows : List Le}
    (hcanonical : OneVarCanonical idx rows)
    (hfeasible : ∃ a : Valuation, ∀ row ∈ rows, Le.sat row a)
    (hno : IntegerProjection.NoIntSolution [idx] rows) :
    ∃ row q, row ∈ rows ∧ 0 < q ∧ row.form = [⟨idx, q⟩] := by
  have hnonempty := upperRows_nonempty hcanonical hfeasible hno
  obtain ⟨row, hrowUpper⟩ :=
    List.exists_mem_of_ne_nil (upperRows idx rows) hnonempty
  have hrow : row ∈ rows := (List.mem_filter.mp hrowUpper).1
  have hcoeff : 0 < coeffAt idx row.form :=
    of_decide_eq_true (List.mem_filter.mp hrowUpper).2
  rcases hcanonical row hrow with hzero | ⟨q, hq, hform⟩
  · simp [hzero] at hcoeff
  · refine ⟨row, q, hrow, ?_, hform⟩
    simpa [hform, coeffAt] using hcoeff

theorem integralBounds_refTree_complete {idx : Nat} {rows : List Le}
    {lower upper : ℤ}
    (hno : IntegerProjection.NoIntSolution [idx] rows) :
    ∃ tree,
      RefTree.Valid (fun j => j ∈ [idx])
        (leLower idx (upper : ℚ) ::
          leUpper idx ((lower - 1 : ℤ) : ℚ) :: rows) tree := by
  by_cases hbounds : lower ≤ upper
  · let spec : Interval :=
      ⟨idx, lower, (upper - lower).toNat⟩
    have hwidth :
        lower + ((upper - lower).toNat : ℤ) = upper := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hbounds)]
      omega
    have hLowerRow :
        spec.lowerRow =
          leUpper idx ((lower - 1 : ℤ) : ℚ) := by
      rfl
    have hUpperRow :
        spec.upperRow = leLower idx (upper : ℚ) := by
      unfold Interval.upperRow spec
      rw [hwidth]
    apply bounded_refTree_complete (fun j => j ∈ [idx]) [spec]
      (leLower idx (upper : ℚ) ::
        leUpper idx ((lower - 1 : ℤ) : ℚ) :: rows)
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      simp [spec]
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rw [hLowerRow, hUpperRow]
      simp
    · intro a hint hrows
      apply hno a
      · intro j hj
        simp only [List.mem_singleton] at hj
        subst j
        exact hint spec (by simp)
      · intro row hrow
        exact hrows row (by simp [hrow])
  · apply ratInfeasible_has_refTree_leaf
    intro a hrows
    have hupper :
        a idx ≤ (upper : ℚ) :=
      (sat_leLower a idx (upper : ℚ)).mp
        (hrows (leLower idx (upper : ℚ)) (by simp))
    have hlower :
        (lower : ℚ) ≤ a idx := by
      have h :=
        (sat_leUpper a idx (((lower - 1 : ℤ) : ℚ))).mp
          (hrows (leUpper idx (((lower - 1 : ℤ) : ℚ))) (by simp))
      norm_num at h ⊢
      exact h
    have hlt : upper < lower := lt_of_not_ge hbounds
    have hltRat : (upper : ℚ) < (lower : ℚ) := by
      exact_mod_cast hlt
    linarith

/-- Every infeasible canonical rational system over one integer variable has a
finite VIPR refutation tree. -/
theorem oneVar_refTree_complete {idx : Nat} {rows : List Le}
    (hcanonical : OneVarCanonical idx rows)
    (hno : IntegerProjection.NoIntSolution [idx] rows) :
    ∃ tree, RefTree.Valid (fun j => j ∈ [idx]) rows tree := by
  by_cases hrat : RatInfeasible rows
  · exact ratInfeasible_has_refTree_leaf (fun j => j ∈ [idx]) hrat
  · have hfeasible :
        ∃ a : Valuation, ∀ row ∈ rows, Le.sat row a := by
      by_contra hnot
      apply hrat
      intro a hrows
      exact hnot ⟨a, hrows⟩
    obtain ⟨lowerRow, lowerCoeff, hlowerMem, hlowerCoeff, hlowerForm⟩ :=
      exists_lower_row hcanonical hfeasible hno
    obtain ⟨upperRow, upperCoeff, hupperMem, hupperCoeff, hupperForm⟩ :=
      exists_upper_row hcanonical hfeasible hno
    let lowerComb : List (ℚ × Le) :=
      [(lowerMultiplier idx lowerRow, lowerRow)]
    let upperComb : List (ℚ × Le) :=
      [(upperMultiplier idx upperRow, upperRow)]
    obtain ⟨subtree, hsubtree⟩ :=
      integralBounds_refTree_complete
        (idx := idx) (rows := rows)
        (lower := roundedLower idx lowerRow)
        (upper := roundedUpper idx upperRow) hno
    have hsubtree' :
        RefTree.Valid (fun j => j ∈ [idx])
          (deriveRow upperComb true ::
            deriveRow lowerComb true :: rows) subtree := by
      simpa only [upperComb, lowerComb,
        upper_deriveRow hupperForm hupperCoeff,
        lower_deriveRow hlowerForm hlowerCoeff] using hsubtree
    have hidx : idx ∈ [idx] := by simp
    have hupperIn :
        upperRow ∈ deriveRow lowerComb true :: rows := by
      exact List.mem_cons_of_mem _ hupperMem
    have hupperValid :
        RefTree.Valid (fun j => j ∈ [idx])
          (deriveRow lowerComb true :: rows)
          (.derive upperComb true subtree) := by
      exact upper_derive_valid hupperIn hupperForm hupperCoeff hidx hsubtree'
    refine ⟨.derive lowerComb true (.derive upperComb true subtree), ?_⟩
    exact lower_derive_valid hlowerMem hlowerForm hlowerCoeff hidx hupperValid

/-- Completeness of the VIPR proof system for MIPs with one declared integer
variable and any finite number of continuous variables. -/
theorem oneIntegerVariable_proof_complete {base : List SLe} {idx : Nat}
    (hrows : ViprCompleteness.RowsWellFormed base)
    (hinfeasible : ViprCompleteness.SemanticallyInfeasible base [idx]) :
    ViprCompleteness.HasViprRefutation base [idx] := by
  let rows :=
    integerRows (ViprCompleteness.normalizedLeRows base) [idx]
  have hcanonical : OneVarCanonical idx rows := by
    exact integerRows_oneVarCanonical
      (ViprCompleteness.normalizedLeRows base) idx
  have hno : IntegerProjection.NoIntSolution [idx] rows := by
    exact integerRows_noIntSolution hrows hinfeasible
  obtain ⟨tree, htree⟩ :=
    oneVar_refTree_complete hcanonical hno
  exact ProjectionCompile.projectedRefTree_proof_complete htree

end LeanVIPR.Completeness.OneDimensionalCompleteness
