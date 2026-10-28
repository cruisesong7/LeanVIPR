module

public import LeanVIPR.Completeness.RefTreeCompile

@[expose] public section

/-!
# Compiling normalized rows from original sensed constraints

The mathematical completeness argument works over `≤` rows.  A real VIPR
problem may contain `L`, `G`, and `E` constraints.  This module derives every
row of `normalizedLeRows base` from its original sensed row by one signed
`lin` step, then supplies a `PoolContext` for the refutation-tree compiler.
-/

namespace LeanVIPR.Completeness.NormalizationCompile

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness
  LeanVIPR.Completeness.RefTreeCompile LeanVIPR.Completeness.ViprCompleteness
  LeanVIPR.Cert.ViprSystem

private theorem initial_spoolRow_eq_getD (base : List SLe) {idx : Nat}
    (hidx : idx < base.length) :
    spoolRow (sinitPool base) idx = base.getD idx default := by
  unfold spoolRow sinitPool
  rw [List.getD_eq_getElem _ _ (by simpa using hidx)]
  rw [List.getD_eq_getElem _ _ hidx]
  simp

private theorem initial_spoolAsm_empty (base : List SLe) (idx : Nat) :
    spoolAsm (sinitPool base) idx = ∅ := by
  by_cases hidx : idx < base.length
  · unfold spoolAsm sinitPool
    rw [List.getD_eq_getElem _ _ (by simpa using hidx)]
    simp
  · unfold spoolAsm sinitPool
    rw [List.getD_eq_default _ _ (by simpa using hidx)]
    rfl

def normalizationStep {base : List SLe} {row : Le}
    (origin : NormalizedOrigin base row) : SStep :=
  ⟨asSLe row, .lin [(origin.sign, origin.source)]⟩

theorem normalizationStep_valid {base : List SLe} {row : Le}
    (origin : NormalizedOrigin base row) (intVars : List Nat)
    (priorSteps : List SStep) :
    StepValid intVars (sfreplay (sinitPool base) priorSteps)
      (normalizationStep origin) := by
  let pool := sfreplay (sinitPool base) priorSteps
  have hbaseLength : (sinitPool base).length = base.length := by
    simp [sinitPool]
  have hsourceBase : origin.source < (sinitPool base).length := by
    simpa [hbaseLength] using origin.source_lt
  have hsource : origin.source < pool.length :=
    lt_of_lt_of_le hsourceBase
      (length_le_sfreplay (sinitPool base) priorSteps)
  have hrow :
      spoolRow pool origin.source =
        base.getD origin.source default := by
    rw [spoolRow_sfreplay_of_lt (sinitPool base) priorSteps
      origin.source hsourceBase]
    exact initial_spoolRow_eq_getD base origin.source_lt
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    rw [hp]
    exact hsource
  · change LinValid (asSLe row)
      [(origin.sign, spoolRow pool origin.source)]
    rw [hrow]
    right
    refine ⟨?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · apply formEqReal_of_ratEvalEq
      intro a
      simpa [asSLe, scomb, combine, combineForm, SLe.toLe,
        LinForm.eval_append, LinForm.eval_scale] using
        (origin.eval_eq a).symm
    · intro p hp
      simp only [List.mem_singleton] at hp
      rw [hp]
      exact origin.suitable
    · simpa [asSLe, scomb, combine, SLe.toLe] using
        le_of_eq origin.rhs_eq.symm

theorem normalizationStep_asm_empty {base : List SLe} {row : Le}
    (origin : NormalizedOrigin base row) (priorSteps : List SStep) :
    (sentryOf (sfreplay (sinitPool base) priorSteps)
      (normalizationStep origin)).2 = ∅ := by
  let pool := sfreplay (sinitPool base) priorSteps
  have hsourceBase : origin.source < (sinitPool base).length := by
    simpa [sinitPool] using origin.source_lt
  have hasm :
      spoolAsm pool origin.source =
        spoolAsm (sinitPool base) origin.source :=
    spoolAsm_sfreplay_of_lt (sinitPool base) priorSteps
      origin.source hsourceBase
  simp only [normalizationStep, sentryOf, collectAsms, Finset.union_empty]
  rw [hasm, initial_spoolAsm_empty]

structure Compilation (base : List SLe) (rows : List Le)
    (intVars : List Nat) where
  steps : List SStep
  valid : DerivationValid intVars (sinitPool base) steps
  pool : SPool
  replay_eq : sfreplay (sinitPool base) steps = pool
  ctx : PoolContext rows pool
  ctx_empty :
    ∀ row ∈ rows,
      spoolAsm pool (ctx.index row) = ∅

noncomputable def compileRows (base : List SLe) (intVars : List Nat) :
    ∀ rows : List Le,
      (∀ row ∈ rows, Nonempty (NormalizedOrigin base row)) →
      Compilation base rows intVars
  | [], _ =>
      { steps := []
        valid := trivial
        pool := sinitPool base
        replay_eq := rfl
        ctx :=
          { index := fun _ => 0
            index_lt := by simp
            row_eq := by simp }
        ctx_empty := by simp }
  | row :: rows, horigins => by
      let tail := compileRows base intVars rows fun candidate hcandidate =>
        horigins candidate (by simp [hcandidate])
      let origin := Classical.choice (horigins row (by simp))
      let step := normalizationStep origin
      have hStep : StepValid intVars tail.pool step := by
        rw [← tail.replay_eq]
        exact normalizationStep_valid origin intVars tail.steps
      let steps := tail.steps ++ [step]
      let pool := tail.pool ++ [sentryOf tail.pool step]
      have hReplay :
          sfreplay (sinitPool base) steps = pool := by
        rw [sfreplay_append, tail.replay_eq]
        rfl
      have hValid : DerivationValid intVars (sinitPool base) steps := by
        apply derivationValid_append tail.valid
        rw [tail.replay_eq]
        exact ⟨hStep, trivial⟩
      let ctx : PoolContext (row :: rows) pool :=
        tail.ctx.push row step rfl
      refine
        { steps := steps
          valid := hValid
          pool := pool
          replay_eq := hReplay
          ctx := ctx
          ctx_empty := ?_ }
      intro candidate hcandidate
      by_cases heq : candidate = row
      · subst candidate
        simp only [ctx, PoolContext.push, ite_true]
        rw [spoolAsm_append_last]
        rw [← tail.replay_eq]
        exact normalizationStep_asm_empty origin tail.steps
      · have htail : candidate ∈ rows := by
          rcases List.mem_cons.mp hcandidate with hhead | htail
          · exact absurd hhead heq
          · exact htail
        have hindex : ctx.index candidate = tail.ctx.index candidate := by
          simp [ctx, PoolContext.push, heq]
        rw [hindex]
        rw [spoolAsm_append_of_lt tail.pool [sentryOf tail.pool step]
          (tail.ctx.index candidate) (tail.ctx.index_lt candidate htail)]
        exact tail.ctx_empty candidate htail

noncomputable def compileNormalizedRows (base : List SLe)
    (intVars : List Nat) :
    Compilation base (normalizedLeRows base) intVars :=
  compileRows base intVars (normalizedLeRows base) fun row hrow =>
    @normalizedOrigin_of_mem base row hrow

/-- A refutation tree over normalized `≤` rows compiles to a closed VIPR proof
over the original sensed rows. -/
theorem normalizedRefTree_proof_complete {base : List SLe}
    {intVars : List Nat} {tree : RefTree}
    (hvalid :
      RefTree.Valid (fun idx => idx ∈ intVars)
        (normalizedLeRows base) tree) :
    ∃ steps, ProofValid intVars base steps := by
  let normalized := compileNormalizedRows base intVars
  let padded := padLeaves (normalizedLeRows base) tree
  have hPaddedValid :
      RefTree.Valid (fun idx => idx ∈ intVars)
        (normalizedLeRows base) padded :=
    padLeaves_valid _ (normalizedLeRows base) tree hvalid
  let compiled :=
    compileTree normalized.ctx padded hPaddedValid
      (padLeaves_cover (normalizedLeRows base) tree)
  let steps := normalized.steps ++ compiled.steps
  have hReplay :
      sfreplay (sinitPool base) steps =
        sfreplay normalized.pool compiled.steps := by
    rw [show steps = normalized.steps ++ compiled.steps by rfl]
    rw [sfreplay_append, normalized.replay_eq]
  refine ⟨steps, ?_, ?_⟩
  · apply derivationValid_append normalized.valid
    rw [normalized.replay_eq]
    exact compiled.valid
  · let finalEntry :=
      (sfreplay normalized.pool compiled.steps).getD
        compiled.finalIndex sdflt
    refine ⟨finalEntry, ?_, ?_, ?_⟩
    · rw [hReplay]
      exact compiled.final_last
    · ext t
      constructor
      · intro ht
        have ht' :
            t ∈ spoolAsm (sfreplay normalized.pool compiled.steps)
              compiled.finalIndex := ht
        obtain ⟨row, hrow, htRow⟩ :=
          compiled.assumptions_supported t ht'
        rw [normalized.ctx_empty row hrow] at htRow
        simp at htRow
      · simp
    · exact compiled.final_labsurd.absurd

/-- A rational integer value remains integral after embedding into the reals. -/
theorem isIntReal_ratToReal {q : ℚ} (h : IsIntVal q) :
    IsIntReal (q : ℝ) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, by norm_num⟩

/-- Semantic infeasibility of a well-formed sensed system implies rational
infeasibility after normalization, provided the interval specifications cover
all declared integer variables. -/
theorem noIntSolution_normalizedLeRows {base : List SLe}
    {intVars : List Nat} {specs : List BoundedCompleteness.Interval}
    (hrows : RowsWellFormed base)
    (hcover :
      ∀ j ∈ intVars,
        ∃ s ∈ specs, s.idx = j)
    (hinfeasible : SemanticallyInfeasible base intVars) :
    BoundedCompleteness.NoIntSolution specs
      (normalizedLeRows base) := by
  intro a hint hnormalized
  apply hinfeasible (ratToReal a)
  · intro j hj
    obtain ⟨s, hs, hsj⟩ := hcover j hj
    rw [← hsj]
    exact isIntReal_ratToReal (hint s hs)
  · apply (satReal_normalizeRows hrows).mp
    intro d hd
    have hdSense : d.sense = 'L' := by
      unfold normalizeRows at hd
      obtain ⟨c, _, hdc⟩ := List.mem_flatMap.mp hd
      exact normalizeRow_sense hdc
    have hrat : Le.sat d.toLe a := by
      apply hnormalized d.toLe
      exact List.mem_map.mpr ⟨d, hd, rfl⟩
    simp only [satReal, hdSense, ite_true]
    rw [evalReal_ratToReal]
    change (LinForm.eval d.form a : ℝ) ≤ (d.rhs : ℝ)
    exact_mod_cast hrat

/-- Every semantically infeasible well-formed rational MILP whose declared
integer variables have explicit finite integral bounds admits a closed VIPR
proof over its original sensed constraints. -/
theorem bounded_proof_complete {base : List SLe}
    {intVars : List Nat} (specs : List BoundedCompleteness.Interval)
    (hrows : RowsWellFormed base)
    (hIsInt : ∀ s ∈ specs, s.idx ∈ intVars)
    (hcover :
      ∀ j ∈ intVars,
        ∃ s ∈ specs, s.idx = j)
    (hBounds :
      BoundedCompleteness.BoundsPresent
        (normalizedLeRows base) specs)
    (hinfeasible : SemanticallyInfeasible base intVars) :
    ∃ steps, ProofValid intVars base steps := by
  obtain ⟨tree, hvalid⟩ :=
    BoundedCompleteness.bounded_refTree_complete
      (fun idx => idx ∈ intVars) specs (normalizedLeRows base)
      hIsInt hBounds
      (noIntSolution_normalizedLeRows hrows hcover hinfeasible)
  exact normalizedRefTree_proof_complete hvalid

end LeanVIPR.Completeness.NormalizationCompile
