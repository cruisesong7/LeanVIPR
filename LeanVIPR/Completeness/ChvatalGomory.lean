module

public import LeanVIPR.Completeness.GeneralCompleteness

@[expose] public section

/-!
# Chvátal--Gomory derivations at the VIPR proof-system level

An arbitrary CG cut may become integral only after coefficients with the same
variable are aggregated.  VIPR's declarative `rnd` rule permits exactly this:
the combined form need only be semantically integer-valued, and the stated
form need only denote the same linear function.

This module therefore models finite CG derivations directly against
`RndValid`, rather than through the more restrictive syntactic `RefTree.derive`
constructor.  It proves that a finite CG derivation ending in rational
infeasibility compiles to a declaratively valid VIPR proof.  The only remaining
global mathematical obligation is existence of such a finite derivation.
-/

namespace LeanVIPR.Completeness.ChvatalGomory

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.IntegerProjection LeanVIPR.Completeness.NormalizationCompile
  LeanVIPR.Completeness.ProjectionCompile LeanVIPR.Completeness.RefTreeCompile
  LeanVIPR.Completeness.ViprCompleteness LeanVIPR.Cert.ViprSystem

/-- One Chvátal--Gomory cut from the currently available `≤` rows. -/
structure Cut (intVars : List Nat) (rows : List Le) (target : Le) where
  comb : List (ℚ × Le)
  nonnegative : ∀ p ∈ comb, 0 ≤ p.1
  rows : ∀ p ∈ comb, p.2 ∈ rows
  formEq : FormEqReal (combineForm comb) target.form
  integral : FormIntegralReal intVars (combineForm comb)
  rhs : ((⌊(combine comb).rhs⌋ : ℤ) : ℚ) ≤ target.rhs

/-- A finite sequence of CG cuts.  Newly derived rows are prepended to the
logical row context, while the concrete VIPR replay pool grows by appending. -/
inductive Derivation (intVars : List Nat) : List Le → List Le → Type
  | done (rows : List Le) : Derivation intVars rows rows
  | cut {rows final : List Le} (target : Le)
      (valid : Cut intVars rows target)
      (rest : Derivation intVars (target :: rows) final) :
      Derivation intVars rows final

/-- A finite CG derivation whose final rational relaxation is infeasible. -/
structure Refutation (intVars : List Nat) (rows : List Le) where
  finalRows : List Le
  derivation : Derivation intVars rows finalRows
  infeasible : RatInfeasible finalRows

/-- The exact remaining finite-rank statement after rational projection. -/
def FiniteCGComplete : Prop :=
  ∀ (rows : List Le) (intVars : List Nat),
    RowsOnIntVars intVars rows →
    IntegerProjection.NoIntSolution intVars rows →
    Nonempty (Refutation intVars rows)

def RatFeasible (rows : List Le) : Prop :=
  ∃ a : Valuation, ∀ row ∈ rows, Le.sat row a

/-- A representation-independent CG cut: an integer-valued rational form has
a rational upper bound on the current relaxation, and the bound is rounded
down. -/
structure SemanticCut (intVars : List Nat) (rows : List Le) (target : Le) where
  bound : ℚ
  integral : FormIntegralReal intVars target.form
  valid : ∀ a, (∀ row ∈ rows, Le.sat row a) →
    LinForm.eval target.form a ≤ bound
  rhs_eq : target.rhs = ((⌊bound⌋ : ℤ) : ℚ)

/-- A semantic cut remains valid after strengthening its row context. -/
def SemanticCut.weaken
    {intVars : List Nat} {rows larger : List Le} {target : Le}
    (cut : SemanticCut intVars rows target)
    (hrows : ∀ row ∈ rows, row ∈ larger) :
    SemanticCut intVars larger target where
  bound := cut.bound
  integral := cut.integral
  valid a hlarger :=
    cut.valid a fun row hrow => hlarger row (hrows row hrow)
  rhs_eq := cut.rhs_eq

/-- Farkas completeness for valid rational inequalities, stated in exactly the
form needed to turn a semantic CG cut into a VIPR combination. -/
def ValidInequalityComplete : Prop :=
  ∀ (rows : List Le) (form : LinForm) (bound : ℚ),
    RatFeasible rows →
    (∀ a, (∀ row ∈ rows, Le.sat row a) →
      LinForm.eval form a ≤ bound) →
    ∃ comb : List (ℚ × Le),
      (∀ p ∈ comb, 0 ≤ p.1) ∧
      (∀ p ∈ comb, p.2 ∈ rows) ∧
      FormEqReal (combineForm comb) form ∧
      (combine comb).rhs ≤ bound

noncomputable def SemanticCut.toCut
    {intVars : List Nat} {rows : List Le} {target : Le}
    (hvalid : ValidInequalityComplete)
    (hfeasible : RatFeasible rows)
    (cut : SemanticCut intVars rows target) :
    Cut intVars rows target := by
  let comb :=
    Classical.choose
      (hvalid rows target.form cut.bound hfeasible cut.valid)
  have hwitness :=
    Classical.choose_spec
      (hvalid rows target.form cut.bound hfeasible cut.valid)
  obtain ⟨hnonnegative, hrows, hform, hrhs⟩ := hwitness
  refine
    { comb := comb
      nonnegative := hnonnegative
      rows := hrows
      formEq := hform
      integral := ?_
      rhs := ?_ }
  · intro a hint
    obtain ⟨z, hz⟩ := cut.integral a hint
    exact ⟨z, (hform a).trans hz⟩
  · rw [cut.rhs_eq]
    exact_mod_cast Int.floor_mono hrhs

/-- A cut remains valid when more rows become available. -/
def Cut.weaken {intVars : List Nat} {rows larger : List Le} {target : Le}
    (cut : Cut intVars rows target)
    (hrows : ∀ row ∈ rows, row ∈ larger) :
    Cut intVars larger target where
  comb := cut.comb
  nonnegative := cut.nonnegative
  rows p hp := hrows p.2 (cut.rows p hp)
  formEq := cut.formEq
  integral := cut.integral
  rhs := cut.rhs

/-- Prepend a list of newly derived rows in derivation order. -/
def prependTargets : List Le → List Le → List Le
  | [], rows => rows
  | target :: targets, rows =>
      prependTargets targets (target :: rows)

@[simp]
theorem prependTargets_nil (rows : List Le) :
    prependTargets [] rows = rows := rfl

@[simp]
theorem prependTargets_cons (target : Le) (targets rows : List Le) :
    prependTargets (target :: targets) rows =
      prependTargets targets (target :: rows) := rfl

theorem prependTargets_eq_reverse_append (targets rows : List Le) :
    prependTargets targets rows = targets.reverse ++ rows := by
  induction targets generalizing rows with
  | nil => rfl
  | cons target targets ih =>
      rw [prependTargets_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- A finite CG-closure round: every target is justified from the same current
relaxation, rather than from earlier targets in the round. -/
structure Round (intVars : List Nat) (rows : List Le) where
  targets : List Le
  valid : ∀ target ∈ targets, Nonempty (Cut intVars rows target)

def Round.finalRows {intVars : List Nat} {rows : List Le}
    (round : Round intVars rows) : List Le :=
  prependTargets round.targets rows

noncomputable def deriveTargets {intVars : List Nat}
    (base current : List Le)
    (hbase : ∀ row ∈ base, row ∈ current) :
    (targets : List Le) →
    (∀ target ∈ targets, Nonempty (Cut intVars base target)) →
    Derivation intVars current (prependTargets targets current)
  | [], _ => .done current
  | target :: targets, hcuts => by
      let cut :=
        Classical.choice (hcuts target (by simp))
      let lifted :=
        cut.weaken hbase
      have hbase' :
          ∀ row ∈ base, row ∈ target :: current := by
        intro row hrow
        exact List.mem_cons_of_mem _ (hbase row hrow)
      let rest :=
        deriveTargets base (target :: current) hbase'
          targets
          (fun candidate hcandidate =>
            hcuts candidate (by simp [hcandidate]))
      exact .cut target lifted rest

/-- A finite closure round expands to sequentially checkable CG steps. -/
noncomputable def Round.toDerivation {intVars : List Nat}
    {rows : List Le} (round : Round intVars rows) :
    Derivation intVars rows round.finalRows :=
  deriveTargets rows rows (fun _ hrow => hrow) round.targets round.valid

/-- Sequential composition of finite CG derivations. -/
def Derivation.trans {intVars : List Nat} {first middle final : List Le} :
    Derivation intVars first middle →
    Derivation intVars middle final →
    Derivation intVars first final
  | .done _, tail => tail
  | .cut target hcut rest, tail =>
      .cut target hcut (rest.trans tail)

/-- Finitely many CG-closure rounds. -/
inductive RankDerivation (intVars : List Nat) : List Le → List Le → Type
  | done (rows : List Le) : RankDerivation intVars rows rows
  | round {rows final : List Le} (head : Round intVars rows)
      (tail : RankDerivation intVars head.finalRows final) :
      RankDerivation intVars rows final

noncomputable def RankDerivation.toDerivation
    {intVars : List Nat} {first final : List Le} :
    RankDerivation intVars first final →
    Derivation intVars first final
  | .done _ => .done first
  | .round head tail =>
      head.toDerivation.trans tail.toDerivation

/-- A finite-rank witness whose last rational relaxation is empty. -/
structure RankRefutation (intVars : List Nat) (rows : List Le) where
  finalRows : List Le
  derivation : RankDerivation intVars rows finalRows
  infeasible : RatInfeasible finalRows

noncomputable def RankRefutation.toRefutation
    {intVars : List Nat} {rows : List Le}
    (refutation : RankRefutation intVars rows) :
    Refutation intVars rows where
  finalRows := refutation.finalRows
  derivation := refutation.derivation.toDerivation
  infeasible := refutation.infeasible

/-- The conventional finite-round formulation implies the sequential
certificate formulation consumed by the VIPR compiler. -/
theorem finiteCGComplete_of_rankRefutations
    (h :
      ∀ (rows : List Le) (intVars : List Nat),
        RowsOnIntVars intVars rows →
        IntegerProjection.NoIntSolution intVars rows →
        Nonempty (RankRefutation intVars rows)) :
    FiniteCGComplete := by
  intro rows intVars hrows hno
  obtain ⟨refutation⟩ := h rows intVars hrows hno
  exact ⟨refutation.toRefutation⟩

/-- One finitely described semantic CG-closure round.  Feasibility is retained
because valid-inequality Farkas completeness needs a nonempty relaxation; an
already empty relaxation terminates the rank witness instead. -/
structure SemanticRound (intVars : List Nat) (rows : List Le) where
  feasible : RatFeasible rows
  targets : List Le
  valid : ∀ target ∈ targets, SemanticCut intVars rows target

def SemanticRound.finalRows {intVars : List Nat} {rows : List Le}
    (round : SemanticRound intVars rows) : List Le :=
  prependTargets round.targets rows

noncomputable def SemanticRound.toRound
    {intVars : List Nat} {rows : List Le}
    (hvalid : ValidInequalityComplete)
    (round : SemanticRound intVars rows) :
    Round intVars rows where
  targets := round.targets
  valid target htarget :=
    ⟨(round.valid target htarget).toCut hvalid round.feasible⟩

@[simp]
theorem SemanticRound.toRound_finalRows
    {intVars : List Nat} {rows : List Le}
    (hvalid : ValidInequalityComplete)
    (round : SemanticRound intVars rows) :
    (round.toRound hvalid).finalRows = round.finalRows := rfl

/-- A finite sequence of semantically defined CG-closure rounds. -/
inductive SemanticRankDerivation
    (intVars : List Nat) : List Le → List Le → Type
  | done (rows : List Le) : SemanticRankDerivation intVars rows rows
  | round {rows final : List Le}
      (head : SemanticRound intVars rows)
      (tail : SemanticRankDerivation intVars head.finalRows final) :
      SemanticRankDerivation intVars rows final

/-- Concatenate two finite semantic CG-rank derivations. -/
def SemanticRankDerivation.trans
    {intVars : List Nat} {first middle final : List Le} :
    SemanticRankDerivation intVars first middle →
    SemanticRankDerivation intVars middle final →
    SemanticRankDerivation intVars first final
  | .done _, suffix => suffix
  | .round head tail, suffix => .round head (tail.trans suffix)

noncomputable def SemanticRankDerivation.toRankDerivation
    {intVars : List Nat} {first final : List Le}
    (hvalid : ValidInequalityComplete) :
    SemanticRankDerivation intVars first final →
    RankDerivation intVars first final
  | .done _ => .done first
  | .round head tail =>
      .round (head.toRound hvalid) (tail.toRankDerivation hvalid)

/-- A semantic finite-rank witness ending in an empty rational relaxation. -/
structure SemanticRankRefutation
    (intVars : List Nat) (rows : List Le) where
  finalRows : List Le
  derivation : SemanticRankDerivation intVars rows finalRows
  infeasible : RatInfeasible finalRows

/-- Prefix a semantic rank refutation by an earlier finite derivation. -/
def SemanticRankRefutation.prepend
    {intVars : List Nat} {first middle : List Le}
    (initial : SemanticRankDerivation intVars first middle)
    (refutation : SemanticRankRefutation intVars middle) :
    SemanticRankRefutation intVars first where
  finalRows := refutation.finalRows
  derivation := initial.trans refutation.derivation
  infeasible := refutation.infeasible

/-- Reaching a row context that contains a rationally infeasible finite
subsystem is already a semantic finite-rank refutation. -/
def SemanticRankRefutation.of_infeasible_subset
    {intVars : List Nat} {first final targets : List Le}
    (derivation : SemanticRankDerivation intVars first final)
    (hinfeasible : RatInfeasible targets)
    (hsubset : ∀ row ∈ targets, row ∈ final) :
    SemanticRankRefutation intVars first where
  finalRows := final
  derivation := derivation
  infeasible := by
    intro a hfinal
    exact hinfeasible a fun row hrow =>
      hfinal row (hsubset row hrow)

noncomputable def SemanticRankRefutation.toRankRefutation
    {intVars : List Nat} {rows : List Le}
    (hvalid : ValidInequalityComplete)
    (refutation : SemanticRankRefutation intVars rows) :
    RankRefutation intVars rows where
  finalRows := refutation.finalRows
  derivation := refutation.derivation.toRankDerivation hvalid
  infeasible := refutation.infeasible

/-- The classical semantic finite-rank theorem plus valid-inequality Farkas
completeness implies the concrete finite CG certificate theorem. -/
theorem finiteCGComplete_of_semanticRank
    (hvalid : ValidInequalityComplete)
    (hrank :
      ∀ (rows : List Le) (intVars : List Nat),
        RowsOnIntVars intVars rows →
        IntegerProjection.NoIntSolution intVars rows →
        Nonempty (SemanticRankRefutation intVars rows)) :
    FiniteCGComplete := by
  apply finiteCGComplete_of_rankRefutations
  intro rows intVars hrows hno
  obtain ⟨refutation⟩ := hrank rows intVars hrows hno
  exact ⟨refutation.toRankRefutation hvalid⟩

def cutStep {intVars : List Nat} {rows : List Le} {target : Le}
    {pool : SPool} (ctx : PoolContext rows pool)
    (cut : Cut intVars rows target) : SStep :=
  ⟨asSLe target, .rnd (indexedComb ctx cut.comb)⟩

theorem cutStep_formEq {intVars : List Nat} {rows : List Le}
    {target : Le} {pool : SPool} (ctx : PoolContext rows pool)
    (cut : Cut intVars rows target) :
    FormEqReal
      (scomb (resolve pool (indexedComb ctx cut.comb))).form
      target.form := by
  have hcombined :
      FormEqReal
        (scomb (resolve pool (indexedComb ctx cut.comb))).form
        (combineForm cut.comb) := by
    apply formEqReal_of_ratEvalEq
    intro a
    rw [scomb_eval,
      resolvedIndexed_eval ctx cut.comb cut.rows a,
      eval_combineForm]
  intro a
  exact (hcombined a).trans (cut.formEq a)

theorem cutStep_integral {intVars : List Nat} {rows : List Le}
    {target : Le} {pool : SPool} (ctx : PoolContext rows pool)
    (cut : Cut intVars rows target) :
    FormIntegralReal intVars
      (scomb (resolve pool (indexedComb ctx cut.comb))).form := by
  have hcombined :
      FormEqReal
        (scomb (resolve pool (indexedComb ctx cut.comb))).form
        (combineForm cut.comb) := by
    apply formEqReal_of_ratEvalEq
    intro a
    rw [scomb_eval,
      resolvedIndexed_eval ctx cut.comb cut.rows a,
      eval_combineForm]
  intro a hint
  obtain ⟨z, hz⟩ := cut.integral a hint
  exact ⟨z, (hcombined a).trans hz⟩

theorem cutStep_rhs {intVars : List Nat} {rows : List Le}
    {target : Le} {pool : SPool} (ctx : PoolContext rows pool)
    (cut : Cut intVars rows target) :
    ((⌊(scomb (resolve pool (indexedComb ctx cut.comb))).rhs⌋ : ℤ) : ℚ) ≤
      target.rhs := by
  rw [scomb_rhs, resolvedIndexed_rhs ctx cut.comb cut.rows]
  exact cut.rhs

theorem cutStep_valid {intVars : List Nat} {rows : List Le}
    {target : Le} {pool : SPool} (ctx : PoolContext rows pool)
    (cut : Cut intVars rows target) :
    StepValid intVars pool (cutStep ctx cut) := by
  refine ⟨indexedComb_referencesPast ctx cut.rows, ?_⟩
  change RndValid intVars (asSLe target)
    (resolve pool (indexedComb ctx cut.comb))
  refine ⟨cutStep_formEq ctx cut, cutStep_integral ctx cut, ?_⟩
  exact Or.inl
    ⟨rfl, indexedComb_suitable ctx cut.nonnegative cut.rows,
      cutStep_rhs ctx cut⟩

theorem cutStep_asm_empty {intVars : List Nat} {rows : List Le}
    {target : Le} {pool : SPool} (ctx : PoolContext rows pool)
    (hempty : ∀ row ∈ rows, spoolAsm pool (ctx.index row) = ∅)
    (cut : Cut intVars rows target) :
    (sentryOf pool (cutStep ctx cut)).2 = ∅ := by
  simp only [cutStep, sentryOf]
  ext assumption
  constructor
  · intro hassumption
    obtain ⟨p, hp, hassumption⟩ :=
      mem_collectAsms_iff.mp hassumption
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hempty q.2 (cut.rows q hq)] at hassumption
    simp at hassumption
  · simp

/-- Compilation of a high-level CG derivation into indexed VIPR `rnd` steps. -/
structure Compilation {intVars : List Nat} {initial final : List Le}
    {pool : SPool} (ctx : PoolContext initial pool) where
  steps : List SStep
  valid : DerivationValid intVars pool steps
  finalPool : SPool
  replay_eq : sfreplay pool steps = finalPool
  finalCtx : PoolContext final finalPool
  finalEmpty :
    ∀ row ∈ final,
      spoolAsm finalPool (finalCtx.index row) = ∅

noncomputable def compile {intVars : List Nat} {initial final : List Le}
    {pool : SPool} (ctx : PoolContext initial pool)
    (hempty : ∀ row ∈ initial, spoolAsm pool (ctx.index row) = ∅) :
    Derivation intVars initial final →
      @Compilation intVars initial final pool ctx
  | .done _ =>
      { steps := []
        valid := trivial
        finalPool := pool
        replay_eq := rfl
        finalCtx := ctx
        finalEmpty := hempty }
  | .cut target cut rest => by
      let step := cutStep ctx cut
      let nextPool := pool ++ [sentryOf pool step]
      let nextCtx : PoolContext (target :: initial) nextPool :=
        ctx.push target step rfl
      have hnextEmpty :
          ∀ row ∈ target :: initial,
            spoolAsm nextPool (nextCtx.index row) = ∅ := by
        intro row hrow
        by_cases heq : row = target
        · subst row
          simp only [nextCtx, PoolContext.push, ite_true]
          rw [spoolAsm_append_last]
          exact cutStep_asm_empty ctx hempty cut
        · have htail : row ∈ initial := by
            rcases List.mem_cons.mp hrow with hhead | htail
            · exact absurd hhead heq
            · exact htail
          have hindex :
              nextCtx.index row = ctx.index row := by
            simp [nextCtx, PoolContext.push, heq]
          rw [hindex]
          rw [spoolAsm_append_of_lt pool [sentryOf pool step]
            (ctx.index row) (ctx.index_lt row htail)]
          exact hempty row htail
      let tail := compile nextCtx hnextEmpty rest
      refine
        { steps := step :: tail.steps
          valid := ?_
          finalPool := tail.finalPool
          replay_eq := ?_
          finalCtx := tail.finalCtx
          finalEmpty := tail.finalEmpty }
      · exact ⟨cutStep_valid ctx cut, tail.valid⟩
      · change sfreplay nextPool tail.steps = tail.finalPool
        exact tail.replay_eq

theorem leafStep_asm_empty {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool)
    (hempty : ∀ row ∈ rows, spoolAsm pool (ctx.index row) = ∅)
    (comb : List (ℚ × Le))
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    (sentryOf pool (leafStep ctx comb)).2 = ∅ := by
  simp only [leafStep, sentryOf]
  ext assumption
  constructor
  · intro hassumption
    obtain ⟨p, hp, hassumption⟩ :=
      mem_collectAsms_iff.mp hassumption
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hempty q.2 (hrows q hq)] at hassumption
    simp at hassumption
  · simp

/-- A finite CG refutation over the projected integer rows gives a closed
declaratively valid VIPR proof over the original mixed-sense constraints. -/
theorem refutation_proof_complete {base : List SLe}
    {intVars : List Nat}
    (refutation :
      Refutation intVars
        (integerRows (normalizedLeRows base) intVars)) :
    HasViprRefutation base intVars := by
  let projected := compileProjectedRows base intVars
  let compiled :=
    compile projected.ctx projected.ctx_empty refutation.derivation
  let cert :=
    Classical.choice
      (rationalFarkas_complete_le refutation.infeasible)
  let comb := resolveLe refutation.finalRows cert.comb
  let finalStep := leafStep compiled.finalCtx comb
  let steps := projected.steps ++ compiled.steps ++ [finalStep]
  have hleaf :
      RefTree.Valid (fun _ => True) refutation.finalRows (.leaf comb) := by
    exact cert.refTreeValid (fun _ => True)
  have hFinalValid :
      StepValid intVars compiled.finalPool finalStep := by
    exact leafStep_valid compiled.finalCtx hleaf
  have hCompiledReplay :
      sfreplay projected.pool compiled.steps =
        compiled.finalPool := compiled.replay_eq
  have hReplay :
      sfreplay (sinitPool base) steps =
        compiled.finalPool ++
          [sentryOf compiled.finalPool finalStep] := by
    rw [show steps =
      projected.steps ++ (compiled.steps ++ [finalStep]) by
        simp [steps, List.append_assoc]]
    rw [sfreplay_append, projected.replay_eq]
    rw [sfreplay_append, hCompiledReplay]
    rfl
  refine ⟨steps, ?_, ?_⟩
  · rw [show steps =
      projected.steps ++ (compiled.steps ++ [finalStep]) by
        simp [steps, List.append_assoc]]
    apply derivationValid_append projected.valid
    rw [projected.replay_eq]
    apply derivationValid_append compiled.valid
    rw [hCompiledReplay]
    exact ⟨hFinalValid, trivial⟩
  · let finalEntry := sentryOf compiled.finalPool finalStep
    refine ⟨finalEntry, ?_, ?_, ?_⟩
    · rw [hReplay]
      simp [finalEntry]
    · exact leafStep_asm_empty compiled.finalCtx compiled.finalEmpty
        comb hleaf.2.1
    · exact leafStep_absurd (intVars := intVars) compiled.finalCtx hleaf

/-- Finite CG rank implies full declarative VIPR proof-system completeness. -/
theorem proofSystem_complete_of_finiteCG
    (hcg : FiniteCGComplete) :
    ProofSystemComplete := by
  intro base intVars hrows hinfeasible
  let rows := integerRows (normalizedLeRows base) intVars
  have hOnIntVars : RowsOnIntVars intVars rows := by
    exact integerRows_integral (normalizedLeRows base) intVars
  have hNoSolution :
      IntegerProjection.NoIntSolution intVars rows := by
    exact integerRows_noIntSolution hrows hinfeasible
  obtain ⟨refutation⟩ :=
    hcg rows intVars hOnIntVars hNoSolution
  exact refutation_proof_complete refutation

end LeanVIPR.Completeness.ChvatalGomory
