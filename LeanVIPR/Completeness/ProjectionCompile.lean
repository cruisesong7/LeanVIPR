module

public import LeanVIPR.Completeness.IntegerProjection
public import LeanVIPR.Completeness.NormalizationCompile

@[expose] public section

/-!
# Compiling continuous-variable projection into VIPR `lin` steps

Every Fourier--Motzkin projection row is a nonnegative combination of the
normalized input rows.  This module emits those combinations as ordinary VIPR
`lin` steps, stating canonical sparse forms so subsequent integer rounding
mentions only declared integer variables.
-/

namespace LeanVIPR.Completeness.ProjectionCompile

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.IntegerProjection LeanVIPR.Completeness.NormalizationCompile
  LeanVIPR.Completeness.RefTreeCompile LeanVIPR.Completeness.ViprCompleteness
  LeanVIPR.Cert.ViprSystem

/-- A direct nonnegative linear derivation of one target row. -/
structure Origin (source : List Le) (target : Le) where
  comb : List (ℚ × Le)
  nonnegative : ∀ p ∈ comb, 0 ≤ p.1
  rows : ∀ p ∈ comb, p.2 ∈ source
  eval_eq : ∀ a,
    (comb.map fun p => p.1 * LinForm.eval p.2.form a).sum =
      LinForm.eval target.form a
  rhs_eq : (comb.map fun p => p.1 * p.2.rhs).sum = target.rhs

theorem resolveLe_rows {source : List Le} {comb : List (ℚ × Nat)}
    (hreferences : ∀ p ∈ comb, p.2 < source.length) :
    ∀ p ∈ resolveLe source comb, p.2 ∈ source := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hlt := hreferences q hq
  rw [List.getD_eq_getElem source default hlt]
  exact List.getElem_mem hlt

theorem projectedOrigin_of_mem {source : List Le} {intVars : List Nat}
    {target : Le} (htarget : target ∈ integerRows source intVars) :
    Nonempty (Origin source target) := by
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp htarget
  have hderived :
      Nonempty (Derived source raw) :=
    eliminateMany_preserves_derived
      (continuousVars source intVars)
      (fun row hrow => derived_of_mem hrow) raw hraw
  obtain ⟨derived⟩ := hderived
  let comb := resolveLe source derived.comb
  refine ⟨
    { comb := comb
      nonnegative := ?_
      rows := ?_
      eval_eq := ?_
      rhs_eq := ?_ }⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact derived.nonnegative q hq
  · exact resolveLe_rows derived.referencesPast
  · intro a
    rw [← eval_combineForm, resolveLe_eval, derived.eval_eq]
    simpa [canonicalRow] using (canonicalForm_eval raw.form a).symm
  ·
    change (combine (resolveLe source derived.comb)).rhs = raw.rhs
    rw [resolveLe_rhs, derived.rhs_eq]

def projectionStep {source : List Le} {target : Le}
    {pool : SPool} (ctx : PoolContext source pool)
    (origin : Origin source target) : SStep :=
  ⟨asSLe target, .lin (indexedComb ctx origin.comb)⟩

theorem projectionStep_valid {source : List Le} {target : Le}
    {pool : SPool} {intVars : List Nat}
    (ctx : PoolContext source pool) (origin : Origin source target) :
    StepValid intVars pool (projectionStep ctx origin) := by
  refine ⟨indexedComb_referencesPast ctx origin.rows, ?_⟩
  change LinValid (asSLe target)
    (resolve pool (indexedComb ctx origin.comb))
  right
  refine ⟨?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
  · apply formEqReal_of_ratEvalEq
    intro a
    rw [scomb_eval,
      resolvedIndexed_eval ctx origin.comb origin.rows a,
      origin.eval_eq a]
    rfl
  · exact indexedComb_suitable ctx origin.nonnegative origin.rows
  · rw [scomb_rhs,
      resolvedIndexed_rhs ctx origin.comb origin.rows,
      origin.rhs_eq]
    exact le_rfl

theorem projectionStep_asm_empty {source : List Le} {target : Le}
    {pool : SPool} (ctx : PoolContext source pool)
    (hsourceEmpty :
      ∀ row ∈ source, spoolAsm pool (ctx.index row) = ∅)
    (origin : Origin source target) :
    (sentryOf pool (projectionStep ctx origin)).2 = ∅ := by
  simp only [projectionStep, sentryOf]
  ext assumption
  constructor
  · intro hassumption
    obtain ⟨p, hp, hassumption⟩ :=
      mem_collectAsms_iff.mp hassumption
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hsourceEmpty q.2 (origin.rows q hq)] at hassumption
    simp at hassumption
  · simp

/-- Extension of a running pool by a list of projected rows. -/
structure Extension (source targets : List Le) (intVars : List Nat)
    (pool : SPool) (sourceCtx : PoolContext source pool) where
  steps : List SStep
  valid : DerivationValid intVars pool steps
  finalPool : SPool
  replay_eq : sfreplay pool steps = finalPool
  ctx : PoolContext targets finalPool
  ctx_empty :
    ∀ row ∈ targets,
      spoolAsm finalPool (ctx.index row) = ∅

noncomputable def compileRows {source : List Le} {intVars : List Nat}
    {pool : SPool} (sourceCtx : PoolContext source pool)
    (hsourceEmpty :
      ∀ row ∈ source, spoolAsm pool (sourceCtx.index row) = ∅) :
    ∀ targets : List Le,
      (∀ target ∈ targets, Nonempty (Origin source target)) →
      Extension source targets intVars pool sourceCtx
  | [], _ =>
      { steps := []
        valid := trivial
        finalPool := pool
        replay_eq := rfl
        ctx :=
          { index := fun _ => 0
            index_lt := by simp
            row_eq := by simp }
        ctx_empty := by simp }
  | target :: targets, horigins => by
      let tail := @compileRows source intVars pool sourceCtx
        hsourceEmpty targets
        (fun candidate hcandidate =>
          horigins candidate (by simp [hcandidate]))
      let replayedSourceCtx : PoolContext source tail.finalPool :=
        { index := sourceCtx.index
          index_lt := by
            intro row hrow
            rw [← tail.replay_eq]
            have hlt :=
              (sourceCtx.replay tail.steps).index_lt row hrow
            rw [PoolContext.replay_index] at hlt
            exact hlt
          row_eq := by
            intro row hrow
            rw [← tail.replay_eq]
            have heq :=
              (sourceCtx.replay tail.steps).row_eq row hrow
            rw [PoolContext.replay_index] at heq
            exact heq }
      let origin := Classical.choice (horigins target (by simp))
      let step := projectionStep replayedSourceCtx origin
      have hStep : StepValid intVars tail.finalPool step :=
        projectionStep_valid replayedSourceCtx origin
      let ctx : PoolContext (target :: targets)
          (tail.finalPool ++ [sentryOf tail.finalPool step]) :=
        tail.ctx.push target step rfl
      refine
        { steps := tail.steps ++ [step]
          valid := ?_
          finalPool :=
            tail.finalPool ++ [sentryOf tail.finalPool step]
          replay_eq := ?_
          ctx := ctx
          ctx_empty := ?_ }
      · apply derivationValid_append tail.valid
        rw [tail.replay_eq]
        exact ⟨hStep, trivial⟩
      · rw [sfreplay_append, tail.replay_eq]
        rfl
      · intro candidate hcandidate
        by_cases heq : candidate = target
        · subst candidate
          simp only [ctx, PoolContext.push, ite_true]
          rw [spoolAsm_append_last]
          apply projectionStep_asm_empty replayedSourceCtx
          · intro row hrow
            have hindex :
                replayedSourceCtx.index row =
                  sourceCtx.index row := by
              rfl
            have hreplay :
                spoolAsm tail.finalPool
                    (replayedSourceCtx.index row) =
                  spoolAsm pool (sourceCtx.index row) := by
              rw [hindex, ← tail.replay_eq]
              exact spoolAsm_sfreplay_of_lt pool tail.steps
                (sourceCtx.index row)
                (sourceCtx.index_lt row hrow)
            rw [hreplay]
            exact hsourceEmpty row hrow
        · have htail : candidate ∈ targets := by
            rcases List.mem_cons.mp hcandidate with hhead | htail
            · exact absurd hhead heq
            · exact htail
          have hindex :
              ctx.index candidate = tail.ctx.index candidate := by
            simp [ctx, PoolContext.push, heq]
          rw [hindex]
          rw [spoolAsm_append_of_lt tail.finalPool
            [sentryOf tail.finalPool step] (tail.ctx.index candidate)
            (tail.ctx.index_lt candidate htail)]
          exact tail.ctx_empty candidate htail

/-- Derive all canonical projected rows after the mixed-sense normalization
prefix. -/
noncomputable def compileProjectedRows (base : List SLe)
    (intVars : List Nat) :
    NormalizationCompile.Compilation base
      (integerRows (normalizedLeRows base) intVars) intVars := by
  let normalized := compileNormalizedRows base intVars
  let extension :=
    @compileRows (normalizedLeRows base) intVars normalized.pool
      normalized.ctx normalized.ctx_empty
      (integerRows (normalizedLeRows base) intVars)
      (fun target htarget => projectedOrigin_of_mem htarget)
  let steps := normalized.steps ++ extension.steps
  refine
    { steps := steps
      valid := ?_
      pool := extension.finalPool
      replay_eq := ?_
      ctx := extension.ctx
      ctx_empty := extension.ctx_empty }
  · apply derivationValid_append normalized.valid
    rw [normalized.replay_eq]
    exact extension.valid
  · rw [show steps = normalized.steps ++ extension.steps by rfl]
    rw [sfreplay_append, normalized.replay_eq, extension.replay_eq]

/-- A valid pure-integer refutation tree over the projected rows yields a flat,
closed VIPR proof over the original mixed-sense constraints. -/
theorem projectedRefTree_proof_complete {base : List SLe}
    {intVars : List Nat} {tree : RefTree}
    (hvalid :
      RefTree.Valid (fun idx => idx ∈ intVars)
        (integerRows (normalizedLeRows base) intVars) tree) :
    ∃ steps, ProofValid intVars base steps := by
  let projected := compileProjectedRows base intVars
  let rows := integerRows (normalizedLeRows base) intVars
  let padded := padLeaves rows tree
  have hPaddedValid :
      RefTree.Valid (fun idx => idx ∈ intVars) rows padded :=
    padLeaves_valid _ rows tree hvalid
  let compiled :=
    compileTree projected.ctx padded hPaddedValid
      (padLeaves_cover rows tree)
  let steps := projected.steps ++ compiled.steps
  have hReplay :
      sfreplay (sinitPool base) steps =
        sfreplay projected.pool compiled.steps := by
    rw [show steps = projected.steps ++ compiled.steps by rfl]
    rw [sfreplay_append, projected.replay_eq]
  refine ⟨steps, ?_, ?_⟩
  · apply derivationValid_append projected.valid
    rw [projected.replay_eq]
    exact compiled.valid
  · let finalEntry :=
      (sfreplay projected.pool compiled.steps).getD
        compiled.finalIndex sdflt
    refine ⟨finalEntry, ?_, ?_, ?_⟩
    · rw [hReplay]
      exact compiled.final_last
    · ext assumption
      constructor
      · intro hassumption
        have hassumption' :
            assumption ∈
              spoolAsm (sfreplay projected.pool compiled.steps)
                compiled.finalIndex :=
          hassumption
        obtain ⟨row, hrow, hrowAsm⟩ :=
          compiled.assumptions_supported assumption hassumption'
        rw [projected.ctx_empty row hrow] at hrowAsm
        simp at hrowAsm
      · simp
    · exact compiled.final_labsurd.absurd

end LeanVIPR.Completeness.ProjectionCompile
