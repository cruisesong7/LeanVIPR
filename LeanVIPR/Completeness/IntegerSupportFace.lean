module

public import LeanVIPR.Completeness.IntegerObjective

@[expose] public section

/-!
# Integral support faces of the integer hull

For an integer-valued form validly bounded on a nonempty rational
mixed-integer set, the preceding finite-generation argument supplies an
integral maximizer.  Its objective value is an integer, so tightening the
original inequality to that value gives a valid integral support row whose
equality face contains an integer point.
-/

namespace LeanVIPR.Completeness.IntegerSupportFace

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.IntegerObjective
  LeanVIPR.Completeness.RecessionObjective

/-- A semantically integer-valued LeanVIPR form evaluates to a rational
integer on every finite integral valuation. -/
theorem finiteEval_isIntVal_of_formIntegralReal
    {intVars : List Nat} {form : LinForm}
    (hintegral : FormIntegralReal intVars form)
    {point : FiniteValuation intVars.toFinset}
    (hpoint : FiniteIntegral point) :
    IsIntVal
      (finiteEval intVars.toFinset form point) := by
  unfold finiteEval
  apply formIntegralReal_ratToReal hintegral
  intro idx hidx
  have hmem : idx ∈ intVars.toFinset := by
    simpa only [List.mem_toFinset] using hidx
  simpa [extendValuation, hmem] using
    hpoint ⟨idx, hmem⟩

/-- The target form with its right-hand side tightened to an integral support
value. -/
def supportRow (target : Le) (value : ℤ) : Le :=
  ⟨target.form, (value : ℚ)⟩

/-- Data of an exact integral support face for one integer-valid target. -/
structure SupportWitness
    (intVars : List Nat) (rows : List Le) (target : Le) where
  maximizer : FiniteValuation intVars.toFinset
  value : ℤ
  maximizer_mem :
    maximizer ∈ integerPoints intVars.toFinset rows
  maximizer_eq :
    finiteEval intVars.toFinset target.form maximizer =
      (value : ℚ)
  support_valid :
    ∀ point ∈ integerPoints intVars.toFinset rows,
      finiteEval intVars.toFinset target.form point ≤
        (value : ℚ)
  support_le_target : (value : ℚ) ≤ target.rhs

theorem SupportWitness.maximizer_sat
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    FiniteSat intVars.toFinset
      (supportRow target witness.value) witness.maximizer := by
  change
    finiteEval intVars.toFinset target.form witness.maximizer ≤
      (witness.value : ℚ)
  exact witness.maximizer_eq.le

theorem SupportWitness.maximizer_tight
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    finiteEval intVars.toFinset
        (supportRow target witness.value).form witness.maximizer =
      (supportRow target witness.value).rhs :=
  witness.maximizer_eq

theorem SupportWitness.supportRow_valid
    {intVars : List Nat} {rows : List Le} {target : Le}
    (witness : SupportWitness intVars rows target) :
    ∀ point ∈ integerPoints intVars.toFinset rows,
      FiniteSat intVars.toFinset
        (supportRow target witness.value) point :=
  witness.support_valid

/-- A nonempty integer-point set and an integer-valid bound determine an exact
integral support row and a tight integral point. -/
theorem exists_supportWitness
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hpoint :
      (integerPoints intVars.toFinset rows).Nonempty)
    (hintegral :
      FormIntegralReal intVars target.form)
    (hvalid :
      ∀ point ∈ integerPoints intVars.toFinset rows,
        finiteEval intVars.toFinset target.form point ≤ target.rhs) :
    Nonempty (SupportWitness intVars rows target) := by
  obtain
      ⟨maximizer, hmaximizer, hmaximum, htarget⟩ :=
    exists_integerPoint_maximizer_of_valid hpoint hvalid
  obtain ⟨value, hvalue⟩ :=
    finiteEval_isIntVal_of_formIntegralReal
      hintegral hmaximizer.2
  refine
    ⟨
      { maximizer := maximizer
        value := value
        maximizer_mem := hmaximizer
        maximizer_eq := hvalue
        support_valid := ?_
        support_le_target := ?_ }⟩
  · intro point hpoint
    rw [← hvalue]
    exact hmaximum point hpoint
  · rw [← hvalue]
    exact htarget

/-- LeanVIPR's pointwise integer-validity premise directly yields the support
witness once the integer feasible set is nonempty. -/
theorem exists_supportWitness_of_integer_valid
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hpoint :
      (integerPoints intVars.toFinset rows).Nonempty)
    (hintegral :
      FormIntegralReal intVars target.form)
    (hvalid :
      ∀ a : Valuation,
        (∀ idx ∈ intVars, IsIntVal (a idx)) →
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a) :
    Nonempty (SupportWitness intVars rows target) :=
  exists_supportWitness hpoint hintegral
    (finite_valid_of_integer_valid hvalid)

end LeanVIPR.Completeness.IntegerSupportFace
