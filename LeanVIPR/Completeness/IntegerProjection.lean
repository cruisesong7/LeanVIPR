module

public import LeanVIPR.Completeness.ViprCompleteness

@[expose] public section

/-!
# Projecting continuous variables before integer reasoning

Fourier--Motzkin elimination removes every variable not declared integral.
The resulting sparse forms are canonicalized through `Finsupp`, deleting
cancelled and zero terms.  Thus every remaining syntactic term is on a declared
integer variable, as required by VIPR's rounding rule.
-/

namespace LeanVIPR.Completeness.IntegerProjection

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.FourierMotzkin LeanVIPR.Completeness.ViprCompleteness
  LeanVIPR.Cert.ViprSystem

/-- Canonical sparse form with one nonzero term per semantic coefficient. -/
noncomputable def canonicalForm (form : LinForm) : LinForm :=
  (toFinsupp form).support.toList.map fun idx =>
    ⟨idx, toFinsupp form idx⟩

theorem canonicalForm_eval (form : LinForm) (a : Valuation) :
    LinForm.eval (canonicalForm form) a = LinForm.eval form a := by
  conv_rhs => rw [eval_eq_finsupp_sum]
  simp [canonicalForm, LinForm.eval, Finsupp.sum]

noncomputable def canonicalRow (row : Le) : Le :=
  ⟨canonicalForm row.form, row.rhs⟩

theorem canonicalRow_sat_iff (row : Le) (a : Valuation) :
    Le.sat (canonicalRow row) a ↔ Le.sat row a := by
  simp only [Le.sat, canonicalRow, canonicalForm_eval]

theorem mem_canonicalForm {form : LinForm} {term : Term}
    (hterm : term ∈ canonicalForm form) :
    term.coeff = coeffAt term.idx form ∧ term.coeff ≠ 0 := by
  obtain ⟨idx, hidx, htermEq⟩ := List.mem_map.mp hterm
  subst term
  have hne : toFinsupp form idx ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hidx)
  exact ⟨by simp, hne⟩

/-- Variable indices occurring in the input but not declared integral. -/
def continuousVars (rows : List Le) (intVars : List Nat) : List Nat :=
  (rowVars rows).filter fun idx => decide (idx ∉ intVars)

/-- Rational projection onto the declared integer coordinates. -/
def projectedRows (rows : List Le) (intVars : List Nat) : List Le :=
  eliminateMany (continuousVars rows intVars) rows

/-- Canonical projected rows used by pure-integer cutting-plane reasoning. -/
noncomputable def integerRows (rows : List Le) (intVars : List Nat) : List Le :=
  (projectedRows rows intVars).map canonicalRow

def NoIntSolution (intVars : List Nat) (rows : List Le) : Prop :=
  ∀ a : Valuation,
    (∀ idx ∈ intVars, IsIntVal (a idx)) →
    (∀ row ∈ rows, Le.sat row a) →
    False

def RowsOnIntVars (intVars : List Nat) (rows : List Le) : Prop :=
  ∀ row ∈ rows, ∀ term ∈ row.form, term.idx ∈ intVars

theorem coeffAt_ne_zero_has_term {idx : Nat} {form : LinForm}
    (hcoeff : coeffAt idx form ≠ 0) :
    ∃ term ∈ form, term.idx = idx := by
  induction form with
  | nil =>
      simp [coeffAt] at hcoeff
  | cons term form ih =>
      by_cases hidx : term.idx = idx
      · exact ⟨term, by simp, hidx⟩
      · have htail : coeffAt idx form ≠ 0 := by
          simpa [coeffAt, hidx] using hcoeff
        obtain ⟨candidate, hcandidate, hcidx⟩ := ih htail
        exact ⟨candidate, by simp [hcandidate], hcidx⟩

theorem coeffAt_ne_zero_mem_rowVars {rows : List Le} {intVars : List Nat}
    {row : Le}
    (hrow : row ∈ eliminateMany (continuousVars rows intVars) rows)
    {idx : Nat} (hcoeff : coeffAt idx row.form ≠ 0) :
    idx ∈ rowVars rows := by
  obtain ⟨term, hterm, hidx⟩ := coeffAt_ne_zero_has_term hcoeff
  have hsupport :=
    eliminateMany_supported (continuousVars rows intVars)
      (rowsSupported_rowVars rows) row hrow term hterm
  simpa [hidx] using hsupport

theorem integerRows_integral (rows : List Le) (intVars : List Nat) :
    RowsOnIntVars intVars (integerRows rows intVars) := by
  intro canonical hcanonical term hterm
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hcanonical
  have hdata := mem_canonicalForm hterm
  by_contra hnotInt
  have hrowVar :
      term.idx ∈ rowVars rows :=
    coeffAt_ne_zero_mem_rowVars hraw (by
      rw [← hdata.1]
      exact hdata.2)
  have hcontinuous :
      term.idx ∈ continuousVars rows intVars := by
    simp [continuousVars, hrowVar, hnotInt]
  have hzero :=
    eliminateMany_coeff_zero_of_mem hcontinuous raw hraw
  exact hdata.2 (hdata.1.trans hzero)

/-- Iterated rational elimination can extend a projected valuation without
changing any coordinate disjoint from the eliminated variables. -/
theorem eliminateMany_complete_agree :
    ∀ (eliminated kept : List Nat) (rows : List Le) (a : Valuation),
      (∀ idx ∈ eliminated, idx ∉ kept) →
      (∀ row ∈ eliminateMany eliminated rows, Le.sat row a) →
      ∃ b : Valuation,
        (∀ row ∈ rows, Le.sat row b) ∧
        ∀ idx ∈ kept, b idx = a idx := by
  intro eliminated
  induction eliminated with
  | nil =>
      intro kept rows a _ hrows
      exact ⟨a, hrows, by simp⟩
  | cons idx eliminated ih =>
      intro kept rows a hdisjoint hprojected
      have htail : ∀ j ∈ eliminated, j ∉ kept := by
        intro j hj
        exact hdisjoint j (by simp [hj])
      obtain ⟨b, hb, hagree⟩ :=
        ih kept (eliminate idx rows) a htail hprojected
      obtain ⟨x, hrows⟩ := eliminate_complete hb
      refine ⟨assignVar b idx x, hrows, ?_⟩
      intro j hj
      rw [assignVar_of_ne (Ne.symm fun heq => ?_)]
      · exact hagree j hj
      · subst j
        exact hdisjoint idx (by simp) hj

theorem continuousVars_disjoint (rows : List Le) (intVars : List Nat) :
    ∀ idx ∈ continuousVars rows intVars, idx ∉ intVars := by
  intro idx hidx
  simpa [continuousVars] using (List.mem_filter.mp hidx).2

theorem isIntReal_of_isIntVal {q : ℚ} (h : IsIntVal q) :
    IsIntReal (q : ℝ) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, by norm_num⟩

theorem integerRows_noIntSolution {base : List SLe}
    {intVars : List Nat}
    (hrows : RowsWellFormed base)
    (hinfeasible : SemanticallyInfeasible base intVars) :
    NoIntSolution intVars
      (integerRows (normalizedLeRows base) intVars) := by
  intro a hint hinteger
  have hprojected :
      ∀ row ∈ projectedRows (normalizedLeRows base) intVars,
        Le.sat row a := by
    intro row hrow
    apply (canonicalRow_sat_iff row a).mp
    exact hinteger (canonicalRow row) (List.mem_map.mpr ⟨row, hrow, rfl⟩)
  obtain ⟨b, hnormalized, hagree⟩ :=
    eliminateMany_complete_agree
      (continuousVars (normalizedLeRows base) intVars)
      intVars (normalizedLeRows base) a
      (continuousVars_disjoint _ _) hprojected
  apply hinfeasible (ratToReal b)
  · intro idx hidx
    change IsIntReal ((b idx : ℚ) : ℝ)
    rw [hagree idx hidx]
    exact isIntReal_of_isIntVal (hint idx hidx)
  · apply (satReal_normalizeRows hrows).mp
    intro row hrow
    have hsense : row.sense = 'L' := by
      unfold normalizeRows at hrow
      obtain ⟨source, _, hsource⟩ := List.mem_flatMap.mp hrow
      exact normalizeRow_sense hsource
    have hrat : Le.sat row.toLe b := by
      apply hnormalized row.toLe
      exact List.mem_map.mpr ⟨row, hrow, rfl⟩
    simp only [satReal, hsense, ite_true]
    rw [evalReal_ratToReal]
    change (LinForm.eval row.form b : ℝ) ≤ (row.rhs : ℝ)
    exact_mod_cast hrat

end LeanVIPR.Completeness.IntegerProjection
