module

public import LeanVIPR.Completeness.PolyhedralProjection
public import LeanVIPR.Completeness.ValidInequalityCompleteness

@[expose] public section

/-!
# Finite integral targets for the integer hull

The finite rational halfspace description of the integer hull can be scaled
row by row to integral left-hand sides and rounded down.  The resulting rows
remain valid on integral points and, when the integer hull is empty, remain
jointly rationally infeasible.
-/

namespace LeanVIPR.Completeness.IntegerHullTargets

open LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
  LeanVIPR.Completeness.ChvatalGomory
  LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.FinitePolyhedron
  LeanVIPR.Completeness.FiniteRankCriterion
  LeanVIPR.Completeness.FourierMotzkin
  LeanVIPR.Completeness.IntegerProjection
  LeanVIPR.Completeness.PolyhedralProjection
  LeanVIPR.Completeness.ValidInequalityCompleteness
  LeanVIPR.Completeness.ViprCompleteness

/-- A positive natural scale integralizing every coefficient of one row. -/
noncomputable def integralScale (row : Le) : Nat :=
  Classical.choose (exists_form_integral_scale row.form)

theorem integralScale_pos (row : Le) :
    0 < integralScale row :=
  (Classical.choose_spec
    (exists_form_integral_scale row.form)).1

theorem integralScale_coeff
    (row : Le) {term : Term} (hterm : term ∈ row.form) :
    IsIntVal ((integralScale row : ℚ) * term.coeff) :=
  (Classical.choose_spec
    (exists_form_integral_scale row.form)).2 term hterm

/-- Scale a row to an integral left-hand side and round its upper bound down. -/
noncomputable def integralTarget (row : Le) : Le :=
  ⟨LinForm.scale (integralScale row : ℚ) row.form,
    ((⌊(integralScale row : ℚ) * row.rhs⌋ : ℤ) : ℚ)⟩

theorem integralTarget_rhs_isIntVal (row : Le) :
    IsIntVal (integralTarget row).rhs :=
  ⟨⌊(integralScale row : ℚ) * row.rhs⌋, rfl⟩

theorem integralTarget_supported
    {support : Finset Nat} {row : Le}
    (hrow : FormSupported support row.form) :
    FormSupported support (integralTarget row).form := by
  intro term hterm
  obtain ⟨source, hsource, hidx⟩ :=
    mem_scale_index hterm
  rw [hidx]
  exact hrow source hsource

theorem integralTarget_coeff
    (row : Le) {term : Term}
    (hterm : term ∈ (integralTarget row).form) :
    IsIntVal term.coeff := by
  change
    term ∈
      LinForm.scale (integralScale row : ℚ) row.form
    at hterm
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp hterm
  exact integralScale_coeff row hsource

theorem integralTarget_sat_of_sat
    {intVars : List Nat} {row : Le} {a : Valuation}
    (hsupported :
      ∀ term ∈ row.form, term.idx ∈ intVars)
    (hintegral :
      ∀ idx ∈ intVars, IsIntVal (a idx))
    (hsat : Le.sat row a) :
    Le.sat (integralTarget row) a := by
  have hevalIntegral :
      IsIntVal
        (LinForm.eval
          (LinForm.scale (integralScale row : ℚ) row.form) a) := by
    apply LinForm.eval_isInt
    intro term hterm
    obtain ⟨source, hsource, hidx⟩ :=
      mem_scale_index hterm
    constructor
    · exact integralTarget_coeff row hterm
    · rw [hidx]
      exact hintegral source.idx (hsupported source hsource)
  have hscaled :
      Le.sat
        ⟨LinForm.scale (integralScale row : ℚ) row.form,
          (integralScale row : ℚ) * row.rhs⟩ a := by
    change
      LinForm.eval
          (LinForm.scale (integralScale row : ℚ) row.form) a ≤
        (integralScale row : ℚ) * row.rhs
    rw [LinForm.eval_scale]
    exact
      mul_le_mul_of_nonneg_left hsat
        (by positivity)
  exact
    rnd_sound
      (LinForm.scale (integralScale row : ℚ) row.form)
      ((integralScale row : ℚ) * row.rhs)
      a hevalIntegral hscaled

theorem sat_of_integralTarget_sat
    {row : Le} {a : Valuation}
    (hsat : Le.sat (integralTarget row) a) :
    Le.sat row a := by
  have hfloor :
      (((⌊(integralScale row : ℚ) * row.rhs⌋ : ℤ) : ℚ)) ≤
        (integralScale row : ℚ) * row.rhs :=
    Int.floor_le _
  change
    LinForm.eval
        (LinForm.scale (integralScale row : ℚ) row.form) a ≤
      (((⌊(integralScale row : ℚ) * row.rhs⌋ : ℤ) : ℚ))
    at hsat
  rw [LinForm.eval_scale] at hsat
  have hscale :
      (0 : ℚ) < (integralScale row : ℚ) := by
    exact_mod_cast integralScale_pos row
  exact le_of_mul_le_mul_left (hsat.trans hfloor) hscale

/-- A finite list of integralized integer-hull rows. -/
noncomputable def integralTargets (rows : List Le) : List Le :=
  rows.map integralTarget

theorem integralTargets_supported
    {vars : Finset Nat} {rows : List Le}
    (hrows : FinitePolyhedron.RowsSupported vars rows) :
    FinitePolyhedron.RowsSupported vars (integralTargets rows) := by
  intro target htarget term hterm
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp htarget
  exact integralTarget_supported (hrows row hrow) term hterm

theorem ratInfeasible_integralTargets
    {rows : List Le}
    (hinfeasible : RatInfeasible rows) :
    RatInfeasible (integralTargets rows) := by
  intro a htargets
  apply hinfeasible a
  intro row hrow
  apply sat_of_integralTarget_sat
  exact
    htargets (integralTarget row)
      (List.mem_map.mpr ⟨row, hrow, rfl⟩)

/-- Termwise integral coefficients on declared integer variables imply the
semantic integer-valuedness required by the VIPR rounding rule. -/
theorem formIntegralReal_of_terms
    {intVars : List Nat} {form : LinForm}
    (hterms :
      ∀ term ∈ form,
        IsIntVal term.coeff ∧ term.idx ∈ intVars) :
    FormIntegralReal intVars form := by
  intro a hintegral
  induction form with
  | nil =>
      exact ⟨0, by simp [evalReal]⟩
  | cons term tail ih =>
      obtain ⟨⟨coefficient, hcoefficient⟩, hidx⟩ :=
        hterms term (by simp)
      obtain ⟨value, hvalue⟩ :=
        hintegral term.idx hidx
      obtain ⟨tailValue, htailValue⟩ :=
        ih fun candidate hcandidate =>
          hterms candidate (by simp [hcandidate])
      refine
        ⟨coefficient * value + tailValue, ?_⟩
      change
        (tail.map
          (fun candidate =>
            (candidate.coeff : ℝ) * a candidate.idx)).sum =
          (tailValue : ℝ)
        at htailValue
      simp only [evalReal, List.map_cons, List.sum_cons]
      rw [hcoefficient, hvalue, htailValue]
      push_cast
      ring

theorem integralTarget_formIntegralReal
    {intVars : List Nat} {row : Le}
    (hsupported :
      ∀ term ∈ row.form, term.idx ∈ intVars) :
    FormIntegralReal intVars (integralTarget row).form := by
  apply formIntegralReal_of_terms
  intro term hterm
  constructor
  · exact integralTarget_coeff row hterm
  · obtain ⟨source, hsource, hidx⟩ :=
      mem_scale_index hterm
    rw [hidx]
    exact hsupported source hsource

/-- Empty integer hulls admit finite, integral-left-hand-side, rationally
infeasible row descriptions. -/
theorem exists_finite_integral_integerHull_targets
    {intVars : List Nat} {rows : List Le}
    (hrows : RowsOnIntVars intVars rows)
    (hno : NoIntSolution intVars rows) :
    ∃ targets : List Le,
      RatInfeasible targets ∧
      RowsOnIntVars intVars targets ∧
      (∀ target ∈ targets,
        FormIntegralReal intVars target.form) ∧
      (∀ target ∈ targets,
        IsIntVal target.rhs) ∧
      ∀ target ∈ targets, ∀ a : Valuation,
        (∀ idx ∈ intVars, IsIntVal (a idx)) →
        (∀ row ∈ rows, Le.sat row a) →
        Le.sat target a := by
  have hfiniteNo :
      FiniteNoIntSolution intVars.toFinset rows :=
    (noIntSolution_iff_finite hrows).mp hno
  obtain ⟨hullRows, hhullSupported, hhull⟩ :=
    exists_finite_integerHull_rows intVars.toFinset rows
  have hhullEmpty :
      integerHull intVars.toFinset rows = ∅ :=
    (integerHull_empty_iff intVars.toFinset rows).2 hfiniteNo
  have hhullInfeasible :
      RatInfeasible hullRows := by
    intro a hsat
    have hfinite :
        restrictValuation (vars := intVars.toFinset) a ∈
          polyhedron intVars.toFinset hullRows := by
      intro row hrow
      unfold FiniteSat
      rw [finiteEval_restrict
        (hhullSupported row hrow)]
      exact hsat row hrow
    have hinHull :
        restrictValuation (vars := intVars.toFinset) a ∈
          integerHull intVars.toFinset rows := by
      rw [hhull]
      exact hfinite
    rw [hhullEmpty] at hinHull
    exact hinHull
  let targets := integralTargets hullRows
  refine
    ⟨targets, ratInfeasible_integralTargets hhullInfeasible,
      ?_, ?_, ?_, ?_⟩
  · intro target htarget term hterm
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp htarget
    have htermSupport :=
      integralTarget_supported
        (hhullSupported row hrow) term hterm
    simpa only [List.mem_toFinset] using htermSupport
  · intro target htarget
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp htarget
    apply integralTarget_formIntegralReal
    intro term hterm
    have htermSupport := hhullSupported row hrow term hterm
    simpa only [List.mem_toFinset] using htermSupport
  · intro target htarget
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp htarget
    exact integralTarget_rhs_isIntVal row
  · intro target htarget a hintegral hsat
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp htarget
    apply integralTarget_sat_of_sat
    · intro term hterm
      have htermSupport := hhullSupported row hrow term hterm
      simpa only [List.mem_toFinset] using htermSupport
    · exact hintegral
    · have hpoint :
          restrictValuation (vars := intVars.toFinset) a ∈
            integerPoints intVars.toFinset rows := by
        constructor
        · intro source hsource
          unfold FiniteSat
          rw [finiteEval_restrict
            (rowsSupported_toFinset hrows source hsource)]
          exact hsat source hsource
        · intro idx
          exact
            hintegral idx
              (by simpa only [List.mem_toFinset] using idx.property)
      have hinHull :
          restrictValuation (vars := intVars.toFinset) a ∈
            integerHull intVars.toFinset rows :=
        subset_convexHull ℚ
          (integerPoints intVars.toFinset rows) hpoint
      rw [hhull] at hinHull
      have hrowSat := hinHull row hrow
      unfold FiniteSat at hrowSat
      rw [finiteEval_restrict
        (hhullSupported row hrow)] at hrowSat
      exact hrowSat

/-- Operational form of the remaining classical finite-CG-rank theorem:
there is one finitely described semantic closure sequence in which every
integral inequality valid on the integer points eventually appears. -/
def IntegerValidClosureComplete : Prop :=
  ∀ (rows : List Le) (intVars : List Nat),
    RowsOnIntVars intVars rows →
    ∃ operator : ClosureOperator intVars,
      ∀ target : Le,
        FormIntegralReal intVars target.form →
        (∀ a : Valuation,
          (∀ idx ∈ intVars, IsIntVal (a idx)) →
          (∀ row ∈ rows, Le.sat row a) →
          Le.sat target a) →
        ∃ rank,
          target ∈ operator.iterate rows rank

theorem semanticRank_complete_of_integerValidClosure
    (hclosure : IntegerValidClosureComplete) :
    ∀ (rows : List Le) (intVars : List Nat),
      RowsOnIntVars intVars rows →
      NoIntSolution intVars rows →
      Nonempty (SemanticRankRefutation intVars rows) := by
  intro rows intVars hrows hno
  obtain
      ⟨targets, hinfeasible, _, hintegral, _, hvalid⟩ :=
    exists_finite_integral_integerHull_targets hrows hno
  obtain ⟨operator, heventual⟩ :=
    hclosure rows intVars hrows
  apply
    operator.refutation_of_eventually_infeasible
      rows targets hinfeasible
  intro target htarget
  exact
    heventual target
      (hintegral target htarget)
      (hvalid target htarget)

/-- The classical finite-CG-rank theorem closes the already verified
compilation chain and yields full VIPR proof-system completeness. -/
theorem proofSystem_complete_of_integerValidClosure
    (hclosure : IntegerValidClosureComplete) :
    ProofSystemComplete := by
  apply proofSystem_complete_of_semanticRank
  exact semanticRank_complete_of_integerValidClosure hclosure

end LeanVIPR.Completeness.IntegerHullTargets
