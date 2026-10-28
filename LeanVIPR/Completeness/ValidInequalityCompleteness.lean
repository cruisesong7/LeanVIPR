module

public import LeanVIPR.Completeness.ChvatalGomory
public import LeanVIPR.Completeness.OneDimensionalCompleteness
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Constructive completeness for valid rational inequalities

To derive a valid inequality `f(x) ≤ β`, introduce a fresh auxiliary variable
`y` together with `y = f(x)`, then project every original variable away by
Fourier--Motzkin elimination.  A finite one-variable projected system whose
feasible values all satisfy `y ≤ β` contains a supporting upper-bound row.
Tracking that row through elimination yields the required nonnegative
combination of the original constraints.

This file begins that construction with the fresh-variable and linking-row
infrastructure.
-/

namespace LeanVIPR.Completeness.ValidInequalityCompleteness

open LeanVIPR.Cert LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness LeanVIPR.Completeness.FourierMotzkin
  LeanVIPR.Completeness.IntegerProjection
  LeanVIPR.Completeness.OneDimensionalCompleteness LeanVIPR.Completeness.ViprCompleteness

def variableIndices (rows : List Le) (form : LinForm) : List Nat :=
  rowVars rows ++ form.map Term.idx

def freshVar (rows : List Le) (form : LinForm) : Nat :=
  (variableIndices rows form).sum + 1

theorem mem_le_sum {value : Nat} :
    ∀ {values : List Nat}, value ∈ values → value ≤ values.sum := by
  intro values hvalue
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      rcases List.mem_cons.mp hvalue with rfl | htail
      · simp
      · have := ih htail
        simp only [List.sum_cons]
        omega

theorem freshVar_not_mem_variableIndices (rows : List Le) (form : LinForm) :
    freshVar rows form ∉ variableIndices rows form := by
  intro hmem
  have hle := mem_le_sum hmem
  unfold freshVar at hle
  omega

theorem freshVar_not_mem_rowVars (rows : List Le) (form : LinForm) :
    freshVar rows form ∉ rowVars rows := by
  intro hmem
  exact freshVar_not_mem_variableIndices rows form
    (List.mem_append.mpr (Or.inl hmem))

theorem freshVar_ne_form_index {rows : List Le} {form : LinForm}
    {term : Term} (hterm : term ∈ form) :
    term.idx ≠ freshVar rows form := by
  intro heq
  apply freshVar_not_mem_variableIndices rows form
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨term, hterm, heq⟩

theorem freshVar_ne_row_index {rows : List Le} {form : LinForm}
    {row : Le} (hrow : row ∈ rows) {term : Term}
    (hterm : term ∈ row.form) :
    term.idx ≠ freshVar rows form := by
  intro heq
  apply freshVar_not_mem_rowVars rows form
  unfold rowVars
  apply List.mem_flatMap.mpr
  exact ⟨row, hrow, List.mem_map.mpr ⟨term, hterm, heq⟩⟩

theorem eval_assignVar_of_fresh {form : LinForm} {a : Valuation}
    {idx : Nat} {value : ℚ}
    (hfresh : ∀ term ∈ form, term.idx ≠ idx) :
    LinForm.eval form (assignVar a idx value) =
      LinForm.eval form a := by
  induction form with
  | nil => rfl
  | cons term tail ih =>
      change term.coeff * assignVar a idx value term.idx +
          LinForm.eval tail (assignVar a idx value) =
        term.coeff * a term.idx + LinForm.eval tail a
      rw [assignVar_of_ne (hfresh term (by simp))]
      rw [ih (fun candidate hcandidate =>
        hfresh candidate (by simp [hcandidate]))]

def lowerLink (idx : Nat) (form : LinForm) : Le :=
  ⟨[⟨idx, 1⟩] ++ LinForm.scale (-1) form, 0⟩

def upperLink (idx : Nat) (form : LinForm) : Le :=
  ⟨form ++ [⟨idx, -1⟩], 0⟩

theorem lowerLink_sat_iff (idx : Nat) (form : LinForm) (a : Valuation) :
    Le.sat (lowerLink idx form) a ↔
      a idx ≤ LinForm.eval form a := by
  change LinForm.eval ([⟨idx, 1⟩] ++ LinForm.scale (-1) form) a ≤ 0 ↔
    a idx ≤ LinForm.eval form a
  rw [LinForm.eval_append, LinForm.eval_scale]
  simp [LinForm.eval]

theorem upperLink_sat_iff (idx : Nat) (form : LinForm) (a : Valuation) :
    Le.sat (upperLink idx form) a ↔
      LinForm.eval form a ≤ a idx := by
  change LinForm.eval (form ++ [⟨idx, -1⟩]) a ≤ 0 ↔
    LinForm.eval form a ≤ a idx
  rw [LinForm.eval_append]
  simp [LinForm.eval]

theorem lowerLink_eval (idx : Nat) (form : LinForm) (a : Valuation) :
    LinForm.eval (lowerLink idx form).form a =
      a idx - LinForm.eval form a := by
  change LinForm.eval ([⟨idx, 1⟩] ++ LinForm.scale (-1) form) a =
    a idx - LinForm.eval form a
  rw [LinForm.eval_append, LinForm.eval_scale]
  simp [LinForm.eval]
  ring

theorem upperLink_eval (idx : Nat) (form : LinForm) (a : Valuation) :
    LinForm.eval (upperLink idx form).form a =
      LinForm.eval form a - a idx := by
  change LinForm.eval (form ++ [⟨idx, -1⟩]) a =
    LinForm.eval form a - a idx
  rw [LinForm.eval_append]
  simp [LinForm.eval]
  ring

def augmentedRows (rows : List Le) (form : LinForm) : List Le :=
  let idx := freshVar rows form
  lowerLink idx form :: upperLink idx form :: rows

theorem augmentedRows_sat_iff (rows : List Le) (form : LinForm)
    (a : Valuation) :
    (∀ row ∈ augmentedRows rows form, Le.sat row a) ↔
      (∀ row ∈ rows, Le.sat row a) ∧
      a (freshVar rows form) = LinForm.eval form a := by
  let idx := freshVar rows form
  constructor
  · intro hrows
    constructor
    · intro row hrow
      exact hrows row (by simp [augmentedRows, hrow])
    · apply le_antisymm
      · exact (lowerLink_sat_iff idx form a).mp
          (hrows (lowerLink idx form) (by simp [augmentedRows, idx]))
      · exact (upperLink_sat_iff idx form a).mp
          (hrows (upperLink idx form) (by simp [augmentedRows, idx]))
  · rintro ⟨hrows, heq⟩ row hrow
    simp only [augmentedRows, List.mem_cons] at hrow
    rcases hrow with rfl | rfl | hrow
    · exact (lowerLink_sat_iff idx form a).mpr heq.le
    · exact (upperLink_sat_iff idx form a).mpr heq.ge
    · exact hrows row hrow

theorem augmentedRows_feasible {rows : List Le} {form : LinForm}
    (hfeasible : RatFeasible rows) :
    RatFeasible (augmentedRows rows form) := by
  obtain ⟨a, hrows⟩ := hfeasible
  let idx := freshVar rows form
  let b := assignVar a idx (LinForm.eval form a)
  refine ⟨b, (augmentedRows_sat_iff rows form b).mpr ⟨?_, ?_⟩⟩
  · intro row hrow
    have heval :
        LinForm.eval row.form b =
          LinForm.eval row.form a := by
      apply eval_assignVar_of_fresh
      intro term hterm
      exact freshVar_ne_row_index hrow hterm
    rw [Le.sat, heval]
    exact hrows row hrow
  · change b idx = LinForm.eval form b
    rw [show b idx = LinForm.eval form a by simp [b, idx]]
    symm
    apply eval_assignVar_of_fresh
    intro term hterm
    exact freshVar_ne_form_index hterm

theorem integerRows_feasible_iff (rows : List Le) (intVars : List Nat) :
    RatFeasible (integerRows rows intVars) ↔ RatFeasible rows := by
  constructor
  · rintro ⟨a, hcanonical⟩
    have hprojected :
        ∀ row ∈ projectedRows rows intVars, Le.sat row a := by
      intro row hrow
      apply (canonicalRow_sat_iff row a).mp
      exact hcanonical (canonicalRow row)
        (List.mem_map.mpr ⟨row, hrow, rfl⟩)
    exact (feasible_eliminateMany_iff
      (continuousVars rows intVars) rows).mpr
        ⟨a, hprojected⟩
  · rintro ⟨a, hrows⟩
    obtain ⟨b, hprojected⟩ :=
      (feasible_eliminateMany_iff
        (continuousVars rows intVars) rows).mp
          ⟨a, hrows⟩
    refine ⟨b, ?_⟩
    intro canonical hcanonical
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hcanonical
    exact (canonicalRow_sat_iff row b).mpr (hprojected row hrow)

noncomputable def projectedAuxRows
    (rows : List Le) (form : LinForm) : List Le :=
  integerRows (augmentedRows rows form) [freshVar rows form]

theorem projectedAuxRows_feasible {rows : List Le} {form : LinForm}
    (hfeasible : RatFeasible rows) :
    RatFeasible (projectedAuxRows rows form) := by
  apply (integerRows_feasible_iff
    (augmentedRows rows form) [freshVar rows form]).mpr
  exact augmentedRows_feasible hfeasible

theorem projectedAuxRows_canonical (rows : List Le) (form : LinForm) :
    OneVarCanonical (freshVar rows form)
      (projectedAuxRows rows form) := by
  exact integerRows_oneVarCanonical
    (augmentedRows rows form) (freshVar rows form)

theorem projectedAuxRows_bounded {rows : List Le} {form : LinForm}
    {bound : ℚ}
    (hvalid :
      ∀ a, (∀ row ∈ rows, Le.sat row a) →
        LinForm.eval form a ≤ bound) :
    ∀ a, (∀ row ∈ projectedAuxRows rows form, Le.sat row a) →
      a (freshVar rows form) ≤ bound := by
  intro a hcanonical
  let augmented := augmentedRows rows form
  let idx := freshVar rows form
  have hprojected :
      ∀ row ∈ projectedRows augmented [idx], Le.sat row a := by
    intro row hrow
    apply (canonicalRow_sat_iff row a).mp
    exact hcanonical (canonicalRow row)
      (List.mem_map.mpr ⟨row, hrow, rfl⟩)
  obtain ⟨b, haugmented, hagree⟩ :=
    eliminateMany_complete_agree
      (continuousVars augmented [idx]) [idx] augmented a
      (continuousVars_disjoint _ _) hprojected
  have hlinked :
      (∀ row ∈ rows, Le.sat row b) ∧
        b idx = LinForm.eval form b := by
    exact (augmentedRows_sat_iff rows form b).mp haugmented
  have hbound := hvalid b hlinked.1
  rw [← hlinked.2, hagree idx (by simp)] at hbound
  exact hbound

def upperRatio (idx : Nat) (row : Le) : ℚ :=
  row.rhs / coeffAt idx row.form

theorem sat_iff_le_upperRatio {idx : Nat} {row : Le} {q : ℚ}
    (hform : row.form = [⟨idx, q⟩]) (hq : 0 < q)
    (a : Valuation) :
    Le.sat row a ↔ a idx ≤ upperRatio idx row := by
  rw [Le.sat, hform]
  simp only [LinForm.eval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [upperRatio, hform]
  simp only [coeffAt, ite_true, add_zero]
  constructor
  · intro h
    apply (le_div_iff₀ hq).mpr
    simpa [mul_comm] using h
  · intro h
    have := (le_div_iff₀ hq).mp h
    simpa [mul_comm] using this

theorem upperRows_nonempty_of_bounded {idx : Nat} {rows : List Le}
    {bound : ℚ}
    (hcanonical : OneVarCanonical idx rows)
    (hfeasible : RatFeasible rows)
    (hbounded :
      ∀ a, (∀ row ∈ rows, Le.sat row a) → a idx ≤ bound) :
    upperRows idx rows ≠ [] := by
  rintro hupper
  obtain ⟨a, hrows⟩ := hfeasible
  let value : ℚ := max (a idx) (bound + 1)
  let b := assignVar a idx value
  have hvalue : a idx ≤ value := le_max_left _ _
  have hsatB : ∀ row ∈ rows, Le.sat row b := by
    intro row hrow
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
  have hb := hbounded b hsatB
  have hlarge : bound + 1 ≤ value := le_max_right _ _
  have hbValue : b idx = value := by simp [b]
  rw [hbValue] at hb
  linarith

theorem exists_supporting_upper_row {idx : Nat} {rows : List Le}
    {bound : ℚ}
    (hcanonical : OneVarCanonical idx rows)
    (hfeasible : RatFeasible rows)
    (hbounded :
      ∀ a, (∀ row ∈ rows, Le.sat row a) → a idx ≤ bound) :
    ∃ row q,
      row ∈ rows ∧
      0 < q ∧
      row.form = [⟨idx, q⟩] ∧
      upperRatio idx row ≤ bound := by
  have hupperNonempty :=
    upperRows_nonempty_of_bounded hcanonical hfeasible hbounded
  have hupperExists :
      ∃ row, row ∈ upperRows idx rows :=
    List.exists_mem_of_ne_nil _ hupperNonempty
  let candidates := (upperRows idx rows).toFinset
  have hcandidates : candidates.Nonempty := by
    obtain ⟨row, hrow⟩ := hupperExists
    exact ⟨row, by simp [candidates, hrow]⟩
  obtain ⟨best, hbestCandidate, hminimal⟩ :=
    Finset.exists_min_image candidates (upperRatio idx) hcandidates
  have hbestUpper : best ∈ upperRows idx rows := by
    simpa [candidates] using hbestCandidate
  have hbestRow : best ∈ rows :=
    List.mem_of_mem_filter hbestUpper
  have hbestCoeff : 0 < coeffAt idx best.form :=
    of_decide_eq_true (List.mem_filter.mp hbestUpper).2
  rcases hcanonical best hbestRow with hzero | ⟨q, hq, hform⟩
  · simp [hzero] at hbestCoeff
  · have hqPos : 0 < q := by
      simpa [hform, coeffAt] using hbestCoeff
    refine ⟨best, q, hbestRow, hqPos, hform, ?_⟩
    by_contra hnot
    have hboundLt : bound < upperRatio idx best :=
      lt_of_not_ge hnot
    obtain ⟨a, hrows⟩ := hfeasible
    have haBound : a idx ≤ bound := hbounded a hrows
    let value : ℚ :=
      (bound + upperRatio idx best) / 2
    let b := assignVar a idx value
    have haValue : a idx ≤ value := by
      dsimp [value]
      linarith
    have hvalueBest : value < upperRatio idx best := by
      dsimp [value]
      linarith
    have hsatB : ∀ row ∈ rows, Le.sat row b := by
      intro row hrow
      rcases hcanonical row hrow with hrowZero | ⟨r, hr, hrowForm⟩
      · change LinForm.eval row.form b ≤ row.rhs
        rw [hrowZero]
        have hsat := hrows row hrow
        change LinForm.eval row.form a ≤ row.rhs at hsat
        rw [hrowZero] at hsat
        simpa [LinForm.eval] using hsat
      · by_cases hrPos : 0 < r
        · have hrowUpper : row ∈ upperRows idx rows := by
            simp [upperRows, hrow, hrowForm, coeffAt, hrPos]
          have hrowCandidate : row ∈ candidates := by
            simp [candidates, hrowUpper]
          have hbestLe :
              upperRatio idx best ≤ upperRatio idx row :=
            hminimal row hrowCandidate
          apply (sat_iff_le_upperRatio hrowForm hrPos b).mpr
          have hbValue : b idx = value := by simp [b]
          rw [hbValue]
          exact le_trans (le_of_lt hvalueBest) hbestLe
        · have hrNonpos : r ≤ 0 := le_of_not_gt hrPos
          change LinForm.eval row.form b ≤ row.rhs
          rw [hrowForm]
          have hsat := hrows row hrow
          change LinForm.eval row.form a ≤ row.rhs at hsat
          rw [hrowForm] at hsat
          simp only [LinForm.eval, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero] at hsat ⊢
          change r * b idx ≤ row.rhs
          simpa [b] using
            le_trans
              (mul_le_mul_of_nonpos_left haValue hrNonpos) hsat
    have hb := hbounded b hsatB
    have hbValue : b idx = value := by simp [b]
    rw [hbValue] at hb
    dsimp [value] at hb
    linarith

/-- Scale a combination whose references are rows rather than indices. -/
def scaleLeComb (q : ℚ) (comb : List (ℚ × Le)) :
    List (ℚ × Le) :=
  comb.map fun p => (q * p.1, p.2)

def leCombEval (comb : List (ℚ × Le)) (a : Valuation) : ℚ :=
  (comb.map fun p => p.1 * LinForm.eval p.2.form a).sum

def leCombRhs (comb : List (ℚ × Le)) : ℚ :=
  (comb.map fun p => p.1 * p.2.rhs).sum

@[simp]
theorem leCombEval_append (left right : List (ℚ × Le))
    (a : Valuation) :
    leCombEval (left ++ right) a =
      leCombEval left a + leCombEval right a := by
  simp [leCombEval]

@[simp]
theorem leCombRhs_append (left right : List (ℚ × Le)) :
    leCombRhs (left ++ right) =
      leCombRhs left + leCombRhs right := by
  simp [leCombRhs]

@[simp]
theorem leCombEval_scale (q : ℚ) (comb : List (ℚ × Le))
    (a : Valuation) :
    leCombEval (scaleLeComb q comb) a =
      q * leCombEval comb a := by
  induction comb with
  | nil => simp [scaleLeComb, leCombEval]
  | cons p comb ih =>
      change q * p.1 * LinForm.eval p.2.form a +
          leCombEval (scaleLeComb q comb) a =
        q * (p.1 * LinForm.eval p.2.form a +
          leCombEval comb a)
      rw [ih]
      ring

@[simp]
theorem leCombRhs_scale (q : ℚ) (comb : List (ℚ × Le)) :
    leCombRhs (scaleLeComb q comb) =
      q * leCombRhs comb := by
  induction comb with
  | nil => simp [scaleLeComb, leCombRhs]
  | cons p comb ih =>
      change q * p.1 * p.2.rhs +
          leCombRhs (scaleLeComb q comb) =
        q * (p.1 * p.2.rhs + leCombRhs comb)
      rw [ih]
      ring

/-- Provenance of a projected row through the two auxiliary linking rows and
the original system. -/
structure AugmentedDerived
    (rows : List Le) (form : LinForm) (row : Le) where
  originalComb : List (ℚ × Le)
  lowerWeight : ℚ
  upperWeight : ℚ
  originalNonnegative : ∀ p ∈ originalComb, 0 ≤ p.1
  lowerNonnegative : 0 ≤ lowerWeight
  upperNonnegative : 0 ≤ upperWeight
  originalRows : ∀ p ∈ originalComb, p.2 ∈ rows
  eval_eq : ∀ a,
    leCombEval originalComb a +
        lowerWeight *
          LinForm.eval
            (lowerLink (freshVar rows form) form).form a +
        upperWeight *
          LinForm.eval
            (upperLink (freshVar rows form) form).form a =
      LinForm.eval row.form a
  rhs_eq : leCombRhs originalComb = row.rhs

theorem augmentedDerived_of_mem {rows : List Le} {form : LinForm}
    {row : Le} (hrow : row ∈ augmentedRows rows form) :
    Nonempty (AugmentedDerived rows form row) := by
  simp only [augmentedRows, List.mem_cons] at hrow
  rcases hrow with rfl | rfl | hrow
  · refine ⟨
      { originalComb := []
        lowerWeight := 1
        upperWeight := 0
        originalNonnegative := by simp
        lowerNonnegative := by norm_num
        upperNonnegative := by norm_num
        originalRows := by simp
        eval_eq := ?_
        rhs_eq := by simp [leCombRhs, lowerLink] }⟩
    intro a
    simp [leCombEval]
  · refine ⟨
      { originalComb := []
        lowerWeight := 0
        upperWeight := 1
        originalNonnegative := by simp
        lowerNonnegative := by norm_num
        upperNonnegative := by norm_num
        originalRows := by simp
        eval_eq := ?_
        rhs_eq := by simp [leCombRhs, upperLink] }⟩
    intro a
    simp [leCombEval]
  · refine ⟨
      { originalComb := [(1, row)]
        lowerWeight := 0
        upperWeight := 0
        originalNonnegative := ?_
        lowerNonnegative := by norm_num
        upperNonnegative := by norm_num
        originalRows := ?_
        eval_eq := ?_
        rhs_eq := ?_ }⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      norm_num
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact hrow
    · intro a
      simp [leCombEval]
    · simp [leCombRhs]

def AugmentedDerived.combine {rows : List Le} {form : LinForm}
    {left right : Le}
    (hleft : AugmentedDerived rows form left)
    (hright : AugmentedDerived rows form right)
    {qleft qright : ℚ}
    (hqleft : 0 ≤ qleft) (hqright : 0 ≤ qright) :
    AugmentedDerived rows form
      (LeanVIPR.Cert.combine
        [(qleft, left), (qright, right)]) := by
  let originalComb :=
    scaleLeComb qleft hleft.originalComb ++
      scaleLeComb qright hright.originalComb
  refine
    { originalComb := originalComb
      lowerWeight :=
        qleft * hleft.lowerWeight +
          qright * hright.lowerWeight
      upperWeight :=
        qleft * hleft.upperWeight +
          qright * hright.upperWeight
      originalNonnegative := ?_
      lowerNonnegative := ?_
      upperNonnegative := ?_
      originalRows := ?_
      eval_eq := ?_
      rhs_eq := ?_ }
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨candidate, hcandidate, rfl⟩ :=
        List.mem_map.mp hp
      exact mul_nonneg hqleft
        (hleft.originalNonnegative candidate hcandidate)
    · obtain ⟨candidate, hcandidate, rfl⟩ :=
        List.mem_map.mp hp
      exact mul_nonneg hqright
        (hright.originalNonnegative candidate hcandidate)
  · exact add_nonneg
      (mul_nonneg hqleft hleft.lowerNonnegative)
      (mul_nonneg hqright hright.lowerNonnegative)
  · exact add_nonneg
      (mul_nonneg hqleft hleft.upperNonnegative)
      (mul_nonneg hqright hright.upperNonnegative)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨candidate, hcandidate, rfl⟩ :=
        List.mem_map.mp hp
      exact hleft.originalRows candidate hcandidate
    · obtain ⟨candidate, hcandidate, rfl⟩ :=
        List.mem_map.mp hp
      exact hright.originalRows candidate hcandidate
  · intro a
    simp only [originalComb, leCombEval_append, leCombEval_scale]
    rw [show LinForm.eval
        (LeanVIPR.Cert.combine
          [(qleft, left), (qright, right)]).form a =
        qleft * LinForm.eval left.form a +
          qright * LinForm.eval right.form a by
      simp [LeanVIPR.Cert.combine, eval_combineForm]]
    rw [← hleft.eval_eq a, ← hright.eval_eq a]
    ring
  · simp only [originalComb, leCombRhs_append, leCombRhs_scale]
    rw [hleft.rhs_eq, hright.rhs_eq]
    simp [LeanVIPR.Cert.combine]

theorem augmentedDerived_cancelPair {rows : List Le}
    {form : LinForm} {idx : Nat} {lower upper : Le}
    (hlower : Nonempty (AugmentedDerived rows form lower))
    (hupper : Nonempty (AugmentedDerived rows form upper))
    (hlowerCoeff : coeffAt idx lower.form < 0)
    (hupperCoeff : 0 < coeffAt idx upper.form) :
    Nonempty
      (AugmentedDerived rows form
        (cancelPair idx lower upper)) := by
  obtain ⟨hlower⟩ := hlower
  obtain ⟨hupper⟩ := hupper
  exact ⟨hupper.combine hlower
    (neg_nonneg.mpr (le_of_lt hlowerCoeff))
    (le_of_lt hupperCoeff)⟩

theorem eliminate_preserves_augmentedDerived
    {base rows : List Le} {form : LinForm} {idx : Nat}
    (hrows :
      ∀ row ∈ rows,
        Nonempty (AugmentedDerived base form row)) :
    ∀ row ∈ eliminate idx rows,
      Nonempty (AugmentedDerived base form row) := by
  intro row hrow
  rcases List.mem_append.mp hrow with hrow | hrow
  · exact hrows row (List.mem_of_mem_filter hrow)
  · obtain ⟨lower, hlower, hrow⟩ :=
      List.mem_flatMap.mp hrow
    obtain ⟨upper, hupper, rfl⟩ :=
      List.mem_map.mp hrow
    exact augmentedDerived_cancelPair
      (hrows lower (List.mem_of_mem_filter hlower))
      (hrows upper (List.mem_of_mem_filter hupper))
      (of_decide_eq_true (List.mem_filter.mp hlower).2)
      (of_decide_eq_true (List.mem_filter.mp hupper).2)

theorem eliminateMany_preserves_augmentedDerived
    {base rows : List Le} {form : LinForm}
    (vars : List Nat)
    (hrows :
      ∀ row ∈ rows,
        Nonempty (AugmentedDerived base form row)) :
    ∀ row ∈ eliminateMany vars rows,
      Nonempty (AugmentedDerived base form row) := by
  induction vars generalizing rows with
  | nil => exact hrows
  | cons idx rest ih =>
      exact ih (eliminate_preserves_augmentedDerived hrows)

theorem projectedRow_augmentedDerived {rows : List Le}
    {form : LinForm} {row : Le}
    (hrow :
      row ∈ projectedRows (augmentedRows rows form)
        [freshVar rows form]) :
    Nonempty (AugmentedDerived rows form row) := by
  exact eliminateMany_preserves_augmentedDerived
    (continuousVars (augmentedRows rows form)
      [freshVar rows form])
    (fun candidate hcandidate =>
      augmentedDerived_of_mem hcandidate)
    row hrow

theorem AugmentedDerived.originalComb_eval_basis_zero
    {rows : List Le} {form : LinForm} {row : Le}
    (derived : AugmentedDerived rows form row) :
    leCombEval derived.originalComb
        (basisValuation (freshVar rows form)) = 0 := by
  unfold leCombEval
  apply List.sum_eq_zero
  intro value hvalue
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hvalue
  have heval :
      LinForm.eval p.2.form
          (basisValuation (freshVar rows form)) = 0 := by
    rw [eval_basisValuation]
    apply coeffAt_eq_zero_of_index_absent
    intro term hterm
    exact freshVar_ne_row_index (derived.originalRows p hp) hterm
  rw [heval]
  ring

theorem AugmentedDerived.weight_difference
    {rows : List Le} {form : LinForm} {row : Le}
    (derived : AugmentedDerived rows form row) {q : ℚ}
    (hcanonical :
      (canonicalRow row).form =
        [⟨freshVar rows form, q⟩]) :
    derived.lowerWeight - derived.upperWeight = q := by
  let idx := freshVar rows form
  let basis := basisValuation idx
  have hformZero : LinForm.eval form basis = 0 := by
    rw [eval_basisValuation]
    apply coeffAt_eq_zero_of_index_absent
    intro term hterm
    exact freshVar_ne_form_index hterm
  have hrowEval : LinForm.eval row.form basis = q := by
    rw [← canonicalForm_eval row.form basis]
    have hcanonical' :
        canonicalForm row.form = [⟨idx, q⟩] := by
      simpa [canonicalRow, idx] using hcanonical
    rw [hcanonical']
    simp [LinForm.eval, basis, basisValuation]
  have heq := derived.eval_eq basis
  rw [derived.originalComb_eval_basis_zero,
    lowerLink_eval, upperLink_eval, hformZero, hrowEval] at heq
  simp [basis, basisValuation, idx] at heq
  linarith

theorem AugmentedDerived.originalComb_eval
    {rows : List Le} {form : LinForm} {row : Le}
    (derived : AugmentedDerived rows form row) {q : ℚ}
    (hcanonical :
      (canonicalRow row).form =
        [⟨freshVar rows form, q⟩])
    (a : Valuation) :
    leCombEval derived.originalComb a =
      q * LinForm.eval form a := by
  have hrowEval :
      LinForm.eval row.form a =
        q * a (freshVar rows form) := by
    rw [← canonicalForm_eval row.form a]
    have hcanonical' :
        canonicalForm row.form =
          [⟨freshVar rows form, q⟩] := by
      simpa [canonicalRow] using hcanonical
    rw [hcanonical']
    simp [LinForm.eval]
  have heq := derived.eval_eq a
  rw [lowerLink_eval, upperLink_eval, hrowEval] at heq
  have hweight := derived.weight_difference hcanonical
  calc
    leCombEval derived.originalComb a =
        q * a (freshVar rows form) -
          derived.lowerWeight *
            (a (freshVar rows form) - LinForm.eval form a) -
          derived.upperWeight *
            (LinForm.eval form a - a (freshVar rows form)) := by
      linarith
    _ = q * LinForm.eval form a := by
      rw [← hweight]
      ring

/-- Every rational inequality valid for a nonempty rational polyhedron is a
nonnegative combination of its defining rows, up to weakening its bound. -/
theorem validInequality_complete :
    ValidInequalityComplete := by
  intro rows form bound hfeasible hvalid
  obtain ⟨best, q, hbest, hq, hbestForm, hratio⟩ :=
    exists_supporting_upper_row
      (projectedAuxRows_canonical rows form)
      (projectedAuxRows_feasible hfeasible)
      (projectedAuxRows_bounded hvalid)
  unfold projectedAuxRows integerRows at hbest
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hbest
  obtain ⟨derived⟩ := projectedRow_augmentedDerived hraw
  let comb := scaleLeComb (1 / q) derived.originalComb
  have hscaleNonnegative : 0 ≤ 1 / q :=
    le_of_lt (div_pos zero_lt_one hq)
  have hcoeff :
      coeffAt (freshVar rows form) (canonicalRow raw).form = q := by
    rw [hbestForm]
    simp [coeffAt]
  have hratio' : raw.rhs / q ≤ bound := by
    unfold upperRatio at hratio
    change raw.rhs /
        coeffAt (freshVar rows form) (canonicalRow raw).form ≤ bound at hratio
    rwa [hcoeff] at hratio
  refine ⟨comb, ?_, ?_, ?_, ?_⟩
  · intro p hp
    change p ∈ scaleLeComb (1 / q) derived.originalComb at hp
    obtain ⟨candidate, hcandidate, rfl⟩ := List.mem_map.mp hp
    exact mul_nonneg hscaleNonnegative
      (derived.originalNonnegative candidate hcandidate)
  · intro p hp
    change p ∈ scaleLeComb (1 / q) derived.originalComb at hp
    obtain ⟨candidate, hcandidate, rfl⟩ := List.mem_map.mp hp
    exact derived.originalRows candidate hcandidate
  · apply RefTreeCompile.formEqReal_of_ratEvalEq
    intro a
    rw [eval_combineForm]
    change leCombEval comb a = LinForm.eval form a
    rw [show leCombEval comb a =
        (1 / q) * leCombEval derived.originalComb a by
      simp [comb]]
    rw [derived.originalComb_eval hbestForm]
    field_simp
  · change leCombRhs comb ≤ bound
    rw [show leCombRhs comb =
        (1 / q) * leCombRhs derived.originalComb by
      simp [comb]]
    rw [derived.rhs_eq]
    simpa [div_eq_mul_inv, mul_comm] using hratio'

/-- After discharging valid-inequality Farkas completeness, semantic finite CG
rank is the only remaining hypothesis for full VIPR proof-system completeness. -/
theorem proofSystem_complete_of_semanticRank
    (hrank :
      ∀ (rows : List Le) (intVars : List Nat),
        RowsOnIntVars intVars rows →
        IntegerProjection.NoIntSolution intVars rows →
        Nonempty (SemanticRankRefutation intVars rows)) :
    ProofSystemComplete := by
  apply ChvatalGomory.proofSystem_complete_of_finiteCG
  exact ChvatalGomory.finiteCGComplete_of_semanticRank
    validInequality_complete hrank

end LeanVIPR.Completeness.ValidInequalityCompleteness
