module

public import LeanVIPR.Completeness.BoundedCompleteness
public import LeanVIPR.Completeness.ViprCompleteness

@[expose] public section

/-!
# Preparing refutation trees for concrete VIPR replay

A Farkas leaf may omit a branch row whose multiplier is zero.  Semantically
that is harmless, but VIPR's `uns` bookkeeping can discharge a branch
assumption only when the assumption occurs in the branch result's open set.

`padLeaves` appends a zero-multiplier reference to every row visible at each
leaf.  It preserves validity and makes all path assumptions explicit without
changing the derived contradiction.
-/

namespace LeanVIPR.Completeness.RefTreeCompile

open LeanVIPR.Cert LeanVIPR.Completeness.ViprCompleteness LeanVIPR.Cert.ViprSystem

/-- Add zero references to every row visible at each leaf. -/
def padLeaves : List Le → RefTree → RefTree
  | rows, .leaf comb =>
      .leaf (comb ++ rows.map fun row => (0, row))
  | rows, .split idx k lower upper =>
      .split idx k
        (padLeaves (leLower idx (k : ℚ) :: rows) lower)
        (padLeaves (leUpper idx (k : ℚ) :: rows) upper)
  | rows, .derive comb rnd sub =>
      .derive comb rnd (padLeaves (deriveRow comb rnd :: rows) sub)

/-- Every leaf of a padded tree explicitly references all rows visible there. -/
def LeavesCover : List Le → RefTree → Prop
  | rows, .leaf comb => ∀ row ∈ rows, (0, row) ∈ comb
  | rows, .split idx k lower upper =>
      LeavesCover (leLower idx (k : ℚ) :: rows) lower ∧
      LeavesCover (leUpper idx (k : ℚ) :: rows) upper
  | rows, .derive comb rnd sub =>
      LeavesCover (deriveRow comb rnd :: rows) sub

theorem padLeaves_cover (rows : List Le) (tree : RefTree) :
    LeavesCover rows (padLeaves rows tree) := by
  induction tree generalizing rows with
  | leaf comb =>
      intro row hrow
      apply List.mem_append.mpr
      right
      exact List.mem_map.mpr ⟨row, hrow, rfl⟩
  | split idx k lower upper ihLower ihUpper =>
      exact ⟨ihLower _, ihUpper _⟩
  | derive comb rnd sub ih =>
      exact ih _

theorem padLeaves_noDerive (rows : List Le) (tree : RefTree) :
    tree.NoDerive → (padLeaves rows tree).NoDerive := by
  induction tree generalizing rows with
  | leaf comb =>
      intro _
      trivial
  | split idx k lower upper ihLower ihUpper =>
      rintro ⟨hLower, hUpper⟩
      exact ⟨ihLower _ hLower, ihUpper _ hUpper⟩
  | derive comb rnd sub ih =>
      intro h
      exact False.elim h

theorem map_zero_eval_sum (rows : List Le) (a : Valuation) :
    ((rows.map fun row => (0, row)).map
      (fun p => p.1 * LinForm.eval p.2.form a)).sum = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change 0 * LinForm.eval row.form a +
          ((rows.map fun row => (0, row)).map
            (fun p => p.1 * LinForm.eval p.2.form a)).sum = 0
      rw [ih]
      simp

theorem map_zero_rhs_sum (rows : List Le) :
    ((rows.map fun row => (0, row)).map fun p => p.1 * p.2.rhs).sum = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change 0 * row.rhs +
          ((rows.map fun row => (0, row)).map fun p => p.1 * p.2.rhs).sum = 0
      rw [ih]
      simp

/-- Padding leaves with zero coefficients preserves declarative tree validity. -/
theorem padLeaves_valid (isInt : Nat → Prop) :
    ∀ (rows : List Le) (tree : RefTree),
      RefTree.Valid isInt rows tree →
      RefTree.Valid isInt rows (padLeaves rows tree) := by
  intro rows tree
  induction tree generalizing rows with
  | leaf comb =>
      rintro ⟨hnonnegative, hrows, hzero, hnegative⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hnonnegative p hp
        · obtain ⟨row, _, rfl⟩ := List.mem_map.mp hp
          norm_num
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hrows p hp
        · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
          exact hrow
      · intro a
        rw [List.map_append, List.sum_append, hzero, map_zero_eval_sum]
        simp
      · rw [List.map_append, List.sum_append, map_zero_rhs_sum]
        simpa using hnegative
  | split idx k lower upper ihLower ihUpper =>
      rintro ⟨hInt, hLower, hUpper⟩
      exact ⟨hInt, ihLower _ hLower, ihUpper _ hUpper⟩
  | derive comb rnd sub ih =>
      rintro ⟨hnonnegative, hrows, hintegral, hsub⟩
      exact ⟨hnonnegative, hrows, hintegral, ih _ hsub⟩

/-- Any valid tree has an equivalent valid form whose leaves explicitly carry
every branch assumption on their path. -/
theorem exists_padded_valid_tree {isInt : Nat → Prop} {rows : List Le}
    {tree : RefTree} (hvalid : RefTree.Valid isInt rows tree) :
    ∃ padded,
      RefTree.Valid isInt rows padded ∧
      LeavesCover rows padded :=
  ⟨padLeaves rows tree, padLeaves_valid isInt rows tree hvalid,
    padLeaves_cover rows tree⟩

/-! ## Compiling a Farkas leaf -/

def asSLe (row : Le) : SLe :=
  ⟨'L', row.form, row.rhs⟩

/-- A mapping from direct rows in a refutation tree to entries of the running VIPR pool. -/
structure PoolContext (rows : List Le) (pool : SPool) where
  index : Le → Nat
  index_lt : ∀ row ∈ rows, index row < pool.length
  row_eq : ∀ row ∈ rows, spoolRow pool (index row) = asSLe row

theorem spoolRow_append_of_lt (pool extra : SPool) (i : Nat) (h : i < pool.length) :
    spoolRow (pool ++ extra) i = spoolRow pool i := by
  unfold spoolRow
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ h]
  rw [List.getElem_append_left h]

theorem spoolAsm_append_of_lt (pool extra : SPool) (i : Nat) (h : i < pool.length) :
    spoolAsm (pool ++ extra) i = spoolAsm pool i := by
  unfold spoolAsm
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ h]
  rw [List.getElem_append_left h]

theorem spoolRow_append_last (pool : SPool) (e : SLe × SAsm) :
    spoolRow (pool ++ [e]) pool.length = e.1 := by
  unfold spoolRow
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem spoolAsm_append_last (pool : SPool) (e : SLe × SAsm) :
    spoolAsm (pool ++ [e]) pool.length = e.2 := by
  unfold spoolAsm
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def PoolContext.weaken {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (extra : SPool) :
    PoolContext rows (pool ++ extra) where
  index := ctx.index
  index_lt row hrow := by
    have := ctx.index_lt row hrow
    simp
    omega
  row_eq row hrow := by
    rw [spoolRow_append_of_lt pool extra (ctx.index row) (ctx.index_lt row hrow)]
    exact ctx.row_eq row hrow

theorem sentryOf_fst (pool : SPool) (s : SStep) :
    (sentryOf pool s).1 = s.stated := by
  cases s with
  | mk stated reason =>
      cases reason <;> rfl

noncomputable def PoolContext.push {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (row : Le) (s : SStep)
    (hstated : s.stated = asSLe row) :
    PoolContext (row :: rows) (pool ++ [sentryOf pool s]) where
  index candidate := if candidate = row then pool.length else ctx.index candidate
  index_lt candidate hcandidate := by
    split
    · simp
    · have htail : candidate ∈ rows := by
        rcases List.mem_cons.mp hcandidate with hhead | htail
        · contradiction
        · exact htail
      have := ctx.index_lt candidate htail
      simp
      omega
  row_eq candidate hcandidate := by
    split <;> rename_i heq
    · subst candidate
      rw [spoolRow_append_last, sentryOf_fst, hstated]
    · have htail : candidate ∈ rows := by
        rcases List.mem_cons.mp hcandidate with hhead | htail
        · contradiction
        · exact htail
      rw [spoolRow_append_of_lt pool [sentryOf pool s] (ctx.index candidate)
        (ctx.index_lt candidate htail)]
      exact ctx.row_eq candidate htail

def PoolContext.replay {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) :
    (steps : List SStep) → PoolContext rows (sfreplay pool steps)
  | [] => ctx
  | step :: steps =>
      (ctx.weaken [sentryOf pool step]).replay steps

theorem mem_collectAsms_iff {pool : SPool} {comb : List (ℚ × Nat)} {t : SLe} :
    t ∈ collectAsms pool comb ↔
      ∃ p ∈ comb, t ∈ spoolAsm pool p.2 := by
  induction comb with
  | nil => simp [collectAsms]
  | cons p ps ih =>
      simp only [collectAsms, Finset.mem_union, ih]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, by simp, ht⟩
        · exact ⟨q, by simp [hq], ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩

/-- Every open assumption is contributed by a row represented by the context. -/
def AssumptionsSupported {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (asms : SAsm) : Prop :=
  ∀ t ∈ asms, ∃ row ∈ rows, t ∈ spoolAsm pool (ctx.index row)

/-- Every context row's open assumptions occur in the result assumption set. -/
def AssumptionsCover {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (asms : SAsm) : Prop :=
  ∀ row ∈ rows, spoolAsm pool (ctx.index row) ⊆ asms

theorem assumptionsSupported_weaken_iff {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (extra : SPool) (asms : SAsm) :
    AssumptionsSupported (ctx.weaken extra) asms ↔
      AssumptionsSupported ctx asms := by
  constructor
  · intro h t ht
    obtain ⟨row, hrow, htRow⟩ := h t ht
    refine ⟨row, hrow, ?_⟩
    change t ∈ spoolAsm (pool ++ extra) (ctx.index row) at htRow
    rw [spoolAsm_append_of_lt pool extra (ctx.index row) (ctx.index_lt row hrow)] at htRow
    exact htRow
  · intro h t ht
    obtain ⟨row, hrow, htRow⟩ := h t ht
    refine ⟨row, hrow, ?_⟩
    change t ∈ spoolAsm (pool ++ extra) (ctx.index row)
    rw [spoolAsm_append_of_lt pool extra (ctx.index row) (ctx.index_lt row hrow)]
    exact htRow

def indexedComb {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le)) :
    List (ℚ × Nat) :=
  comb.map fun p => (p.1, ctx.index p.2)

def leafStep {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le)) : SStep :=
  let indices := indexedComb ctx comb
  let resolved := resolve pool indices
  ⟨⟨'L', (scomb resolved).form, (scomb resolved).rhs⟩, .lin indices⟩

theorem resolvedIndexed_eval {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le))
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) (a : Valuation) :
    ((resolve pool (indexedComb ctx comb)).map
      (fun p => p.1 * LinForm.eval p.2.form a)).sum =
      (comb.map fun p => p.1 * LinForm.eval p.2.form a).sum := by
  induction comb with
  | nil => rfl
  | cons p comb ih =>
      change p.1 * LinForm.eval (spoolRow pool (ctx.index p.2)).form a +
          ((resolve pool (indexedComb ctx comb)).map
            (fun q => q.1 * LinForm.eval q.2.form a)).sum =
        p.1 * LinForm.eval p.2.form a +
          (comb.map fun q => q.1 * LinForm.eval q.2.form a).sum
      rw [ctx.row_eq p.2 (hrows p (by simp))]
      change p.1 * LinForm.eval p.2.form a +
          ((resolve pool (indexedComb ctx comb)).map
            (fun q => q.1 * LinForm.eval q.2.form a)).sum =
        p.1 * LinForm.eval p.2.form a +
          (comb.map fun q => q.1 * LinForm.eval q.2.form a).sum
      rw [ih (fun q hq => hrows q (by simp [hq]))]

theorem resolvedIndexed_rhs {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le))
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    ((resolve pool (indexedComb ctx comb)).map fun p => p.1 * p.2.rhs).sum =
      (comb.map fun p => p.1 * p.2.rhs).sum := by
  induction comb with
  | nil => rfl
  | cons p comb ih =>
      change p.1 * (spoolRow pool (ctx.index p.2)).rhs +
          ((resolve pool (indexedComb ctx comb)).map fun q => q.1 * q.2.rhs).sum =
        p.1 * p.2.rhs + (comb.map fun q => q.1 * q.2.rhs).sum
      rw [ctx.row_eq p.2 (hrows p (by simp))]
      change p.1 * p.2.rhs +
          ((resolve pool (indexedComb ctx comb)).map fun q => q.1 * q.2.rhs).sum =
        p.1 * p.2.rhs + (comb.map fun q => q.1 * q.2.rhs).sum
      rw [ih (fun q hq => hrows q (by simp [hq]))]

theorem indexedComb_referencesPast {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) {comb : List (ℚ × Le)}
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    ∀ p ∈ indexedComb ctx comb, p.2 < pool.length := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ctx.index_lt q.2 (hrows q hq)

theorem indexedComb_suitable {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) {comb : List (ℚ × Le)}
    (hnonnegative : ∀ p ∈ comb, 0 ≤ p.1)
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    SuitableLe (resolve pool (indexedComb ctx comb)) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  rw [ctx.row_eq r.2 (hrows r hr)]
  simp only [asSLe, senseSignReal, ite_true]
  norm_num
  exact hnonnegative r hr

/-- A valid refutation-tree leaf becomes one declaratively valid VIPR `lin` step. -/
theorem leafStep_valid {rows : List Le} {pool : SPool} {intVars : List Nat}
    (ctx : PoolContext rows pool) {comb : List (ℚ × Le)}
    (hvalid : RefTree.Valid (fun idx => idx ∈ intVars) rows (.leaf comb)) :
    StepValid intVars pool (leafStep ctx comb) := by
  obtain ⟨hnonnegative, hrows, hzero, hnegative⟩ := hvalid
  refine ⟨indexedComb_referencesPast ctx hrows, ?_⟩
  change LinValid _ (resolve pool (indexedComb ctx comb))
  refine Or.inl (Or.inl ⟨indexedComb_suitable ctx hnonnegative hrows, ?_, ?_⟩)
  · apply formZeroReal_of_ratEvalZero
    intro a
    rw [scomb_eval, resolvedIndexed_eval ctx comb hrows a, hzero]
  · rw [scomb_rhs, resolvedIndexed_rhs ctx comb hrows]
    exact hnegative

theorem leafStep_absurd {rows : List Le} {pool : SPool} {intVars : List Nat}
    (ctx : PoolContext rows pool) {comb : List (ℚ × Le)}
    (hvalid : RefTree.Valid (fun idx => idx ∈ intVars) rows (.leaf comb)) :
    Absurd (leafStep ctx comb).stated := by
  obtain ⟨_, hrows, hzero, hnegative⟩ := hvalid
  change Absurd
    ⟨'L', (scomb (resolve pool (indexedComb ctx comb))).form,
      (scomb (resolve pool (indexedComb ctx comb))).rhs⟩
  constructor
  · apply formZeroReal_of_ratEvalZero
    intro a
    rw [scomb_eval, resolvedIndexed_eval ctx comb hrows a, hzero]
  · exact Or.inl ⟨rfl, by
      rw [scomb_rhs, resolvedIndexed_rhs ctx comb hrows]
      exact hnegative⟩

def LAbsurd (row : SLe) : Prop :=
  FormZeroReal row.form ∧ row.sense = 'L' ∧ row.rhs < 0

theorem LAbsurd.absurd {row : SLe} (h : LAbsurd row) : Absurd row :=
  ⟨h.1, Or.inl ⟨h.2.1, h.2.2⟩⟩

theorem leafStep_labsurd {rows : List Le} {pool : SPool} {intVars : List Nat}
    (ctx : PoolContext rows pool) {comb : List (ℚ × Le)}
    (hvalid : RefTree.Valid (fun idx => idx ∈ intVars) rows (.leaf comb)) :
    LAbsurd (leafStep ctx comb).stated := by
  obtain ⟨_, hrows, hzero, hnegative⟩ := hvalid
  change LAbsurd
    ⟨'L', (scomb (resolve pool (indexedComb ctx comb))).form,
      (scomb (resolve pool (indexedComb ctx comb))).rhs⟩
  refine ⟨?_, rfl, ?_⟩
  · apply formZeroReal_of_ratEvalZero
    intro a
    rw [scomb_eval, resolvedIndexed_eval ctx comb hrows a, hzero]
  · rw [scomb_rhs, resolvedIndexed_rhs ctx comb hrows]
    exact hnegative

theorem formEqReal_of_ratEvalEq {left right : LinForm}
    (h : ∀ a : Valuation, left.eval a = right.eval a) :
    FormEqReal left right := by
  let diff := left ++ LinForm.scale (-1) right
  have hzero : ∀ a : Valuation, diff.eval a = 0 := by
    intro a
    simp [diff, h a]
  have hzeroReal : FormZeroReal diff :=
    formZeroReal_of_ratEvalZero hzero
  intro a
  have := hzeroReal a
  simp [diff, evalReal_append, evalReal_scale] at this
  linarith

def deriveIndices {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le)) :
    List (ℚ × Nat) :=
  indexedComb ctx comb ++ rows.map fun row => (0, ctx.index row)

def linDeriveStep {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le)) : SStep :=
  ⟨asSLe (combine comb), .lin (deriveIndices ctx comb)⟩

theorem zeroIndices_eval (rows : List Le) (pool : SPool)
    (index : Le → Nat) (a : Valuation) :
    ((resolve pool (rows.map fun row => (0, index row))).map
      (fun p => p.1 * p.2.form.eval a)).sum = 0 := by
  simp [resolve, Function.comp_def]

theorem zeroIndices_rhsSum (rows : List Le) (pool : SPool)
    (index : Le → Nat) :
    ((resolve pool (rows.map fun row => (0, index row))).map
      fun p => p.1 * p.2.rhs).sum = 0 := by
  simp [resolve, Function.comp_def]

theorem derive_scomb_eval {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le))
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) (a : Valuation) :
    (scomb (resolve pool (deriveIndices ctx comb))).form.eval a =
      (combine comb).form.eval a := by
  rw [scomb_eval]
  simp only [deriveIndices, resolve, List.map_append, List.sum_append]
  have hmain := resolvedIndexed_eval ctx comb hrows a
  simp only [resolve] at hmain
  have hzero := zeroIndices_eval rows pool ctx.index a
  simp only [resolve] at hzero
  rw [hmain, hzero]
  simpa [combine] using (eval_combineForm comb a).symm

theorem derive_scomb_rhs {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le))
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    (scomb (resolve pool (deriveIndices ctx comb))).rhs =
      (combine comb).rhs := by
  rw [scomb_rhs]
  simp only [deriveIndices, resolve, List.map_append, List.sum_append]
  have hmain := resolvedIndexed_rhs ctx comb hrows
  simp only [resolve] at hmain
  have hzero := zeroIndices_rhsSum rows pool ctx.index
  simp only [resolve] at hzero
  rw [hmain, hzero]
  simp [combine]

theorem linDeriveStep_valid {rows : List Le} {pool : SPool}
    {intVars : List Nat} (ctx : PoolContext rows pool)
    {comb : List (ℚ × Le)}
    (hnonnegative : ∀ p ∈ comb, 0 ≤ p.1)
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    StepValid intVars pool (linDeriveStep ctx comb) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact indexedComb_referencesPast ctx hrows p hp
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
      exact ctx.index_lt row hrow
  change LinValid (asSLe (combine comb))
    (resolve pool (deriveIndices ctx comb))
  right
  refine ⟨?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
  · apply formEqReal_of_ratEvalEq
    intro a
    exact derive_scomb_eval ctx comb hrows a
  · intro p hp
    simp only [deriveIndices, resolve, List.map_append] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact indexedComb_suitable ctx hnonnegative hrows p hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hq
      rw [ctx.row_eq row hrow]
      simp [asSLe, senseSignReal]
  · rw [derive_scomb_rhs ctx comb hrows]
    rfl

private theorem evalReal_isInt_of_terms (f : LinForm) (a : RealValuation)
    (h : ∀ t ∈ f, IsIntVal t.coeff ∧ IsIntReal (a t.idx)) :
    IsIntReal (evalReal f a) := by
  induction f with
  | nil => exact ⟨0, by simp [evalReal]⟩
  | cons t ts ih =>
      obtain ⟨⟨c, hc⟩, ⟨v, hv⟩⟩ := h t (by simp)
      obtain ⟨m, hm⟩ := ih (fun u hu => h u (by simp [hu]))
      refine ⟨c * v + m, ?_⟩
      change (t.coeff : ℝ) * a t.idx + evalReal ts a = ((c * v + m : ℤ) : ℝ)
      rw [hc, hv, hm]
      push_cast
      ring

theorem combineForm_integralReal {intVars : List Nat}
    {comb : List (ℚ × Le)}
    (hterms : ∀ t ∈ combineForm comb,
      IsIntVal t.coeff ∧ t.idx ∈ intVars) :
    FormIntegralReal intVars (combineForm comb) := by
  intro a hint
  exact evalReal_isInt_of_terms _ a fun t ht =>
    ⟨(hterms t ht).1, hint t.idx (hterms t ht).2⟩

def roundDeriveStep (sourceIndex : Nat) (comb : List (ℚ × Le)) : SStep :=
  ⟨asSLe (deriveRow comb true), .rnd [(1, sourceIndex)]⟩

theorem roundDeriveStep_valid {pool : SPool} {intVars : List Nat}
    {sourceIndex : Nat} {comb : List (ℚ × Le)}
    (hsource : sourceIndex < pool.length)
    (hrow : spoolRow pool sourceIndex = asSLe (combine comb))
    (hterms : ∀ t ∈ combineForm comb,
      IsIntVal t.coeff ∧ t.idx ∈ intVars) :
    StepValid intVars pool (roundDeriveStep sourceIndex comb) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    rw [hp]
    exact hsource
  · change RndValid intVars (asSLe (deriveRow comb true))
      [(1, spoolRow pool sourceIndex)]
    rw [hrow]
    refine ⟨?_, ?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · intro a
      simp [deriveRow, scomb, combine, combineForm, asSLe, SLe.toLe,
        evalReal_scale]
    · intro a hint
      have h := combineForm_integralReal hterms a hint
      simpa [scomb, combine, combineForm, asSLe, SLe.toLe,
        evalReal_scale] using h
    · intro p hp
      simp only [List.mem_singleton] at hp
      rw [hp]
      simp [asSLe, senseSignReal]
    · simp [deriveRow, scomb, combine, asSLe, SLe.toLe]

/-! ## Split assumptions -/

def lowerBound (idx : Nat) (k : ℤ) : SLe :=
  ⟨'L', [⟨idx, 1⟩], (k : ℚ)⟩

def upperBound (idx : Nat) (k : ℤ) : SLe :=
  ⟨'G', [⟨idx, 1⟩], ((k + 1 : ℤ) : ℚ)⟩

def asmStep (bound : SLe) : SStep :=
  ⟨bound, .asm⟩

theorem asmStep_valid (intVars : List Nat) (pool : SPool) (bound : SLe) :
    StepValid intVars pool (asmStep bound) := by
  exact ⟨trivial, trivial⟩

@[simp] theorem lowerBound_eq_asSLe (idx : Nat) (k : ℤ) :
    lowerBound idx k = asSLe (leLower idx (k : ℚ)) := by
  rfl

theorem complementary_bounds {intVars : List Nat} {idx : Nat} (k : ℤ)
    (hidx : idx ∈ intVars) :
    ComplementaryBounds intVars (lowerBound idx k) (upperBound idx k) := by
  refine Or.inl ⟨rfl, rfl, ?_, ?_, ⟨k, rfl⟩, ?_⟩
  · intro a
    rfl
  · intro a hint
    simpa [lowerBound, evalReal] using hint idx hidx
  · simp [lowerBound, upperBound]

def normalizeUpperStep (asmIndex : Nat) (idx : Nat) (k : ℤ) : SStep :=
  ⟨asSLe (leUpper idx (k : ℚ)), .lin [(-1, asmIndex)]⟩

theorem normalizeUpperStep_valid {intVars : List Nat} {pool : SPool}
    {asmIndex idx : Nat} {k : ℤ}
    (hindex : asmIndex < pool.length)
    (hrow : spoolRow pool asmIndex = upperBound idx k) :
    StepValid intVars pool (normalizeUpperStep asmIndex idx k) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    rw [hp]
    exact hindex
  · change LinValid (asSLe (leUpper idx (k : ℚ)))
      [(-1, spoolRow pool asmIndex)]
    rw [hrow]
    right
    constructor
    · intro a
      simp [scomb, combine, combineForm, asSLe, leUpper, upperBound,
        evalReal, LinForm.scale, SLe.toLe]
    · left
      refine ⟨rfl, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        rw [hp]
        simp [upperBound, senseSignReal]
      · simp [scomb, combine, asSLe, upperBound, leUpper, SLe.toLe]

def contradictionRow : SLe :=
  ⟨'L', [], -1⟩

def unsStep (loResult loBound hiResult hiBound : Nat) : SStep :=
  ⟨contradictionRow, .uns loResult loBound hiResult hiBound⟩

theorem contradictionRow_labsurd : LAbsurd contradictionRow := by
  refine ⟨?_, rfl, by simp [contradictionRow]⟩
  intro a
  rfl

theorem unsStep_valid {intVars : List Nat} {pool : SPool}
    {loResult loBound hiResult hiBound : Nat}
    (hloResult : loResult < pool.length)
    (hloBound : loBound < pool.length)
    (hhiResult : hiResult < pool.length)
    (hhiBound : hiBound < pool.length)
    (hloAbsurd : LAbsurd (spoolRow pool loResult))
    (hhiAbsurd : LAbsurd (spoolRow pool hiResult))
    (hbounds : ComplementaryBounds intVars
      (spoolRow pool loBound) (spoolRow pool hiBound))
    (hloMem : spoolRow pool loBound ∈ spoolAsm pool loResult)
    (hhiMem : spoolRow pool hiBound ∈ spoolAsm pool hiResult) :
    StepValid intVars pool (unsStep loResult loBound hiResult hiBound) := by
  refine ⟨⟨hloResult, hloBound, hhiResult, hhiBound⟩, ?_⟩
  exact ⟨Or.inl hloAbsurd.absurd, Or.inl hhiAbsurd.absurd,
    hbounds, hloMem, hhiMem⟩

theorem lowerContext_bound_asm {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (idx : Nat) (k : ℤ) :
    let step := asmStep (lowerBound idx k)
    let pushed := ctx.push (leLower idx (k : ℚ)) step rfl
    spoolAsm (pool ++ [sentryOf pool step])
      (pushed.index (leLower idx (k : ℚ))) = {lowerBound idx k} := by
  simp only [PoolContext.push, ite_true]
  rw [spoolAsm_append_last]
  simp [asmStep, sentryOf]

theorem lowerContext_bound_mem {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (idx : Nat) (k : ℤ) :
    let step := asmStep (lowerBound idx k)
    let pushed := ctx.push (leLower idx (k : ℚ)) step rfl
    lowerBound idx k ∈
      spoolAsm (pool ++ [sentryOf pool step])
        (pushed.index (leLower idx (k : ℚ))) := by
  simp only [PoolContext.push, ite_true]
  rw [spoolAsm_append_last]
  simp [asmStep, sentryOf]

theorem upperContext_bound_asm {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (asmIndex idx : Nat) (k : ℤ)
    (hasm : spoolAsm pool asmIndex = {upperBound idx k}) :
    let step := normalizeUpperStep asmIndex idx k
    let pushed := ctx.push (leUpper idx (k : ℚ)) step rfl
    spoolAsm (pool ++ [sentryOf pool step])
      (pushed.index (leUpper idx (k : ℚ))) = {upperBound idx k} := by
  simp only [PoolContext.push, ite_true]
  rw [spoolAsm_append_last]
  simp [normalizeUpperStep, sentryOf, collectAsms, hasm]

theorem upperContext_bound_mem {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (asmIndex idx : Nat) (k : ℤ)
    (hasm : spoolAsm pool asmIndex = {upperBound idx k}) :
    let step := normalizeUpperStep asmIndex idx k
    let pushed := ctx.push (leUpper idx (k : ℚ)) step rfl
    upperBound idx k ∈
      spoolAsm (pool ++ [sentryOf pool step])
        (pushed.index (leUpper idx (k : ℚ))) := by
  simp only [PoolContext.push, ite_true]
  rw [spoolAsm_append_last]
  simp [normalizeUpperStep, sentryOf, collectAsms, hasm]

theorem erase_supported_push {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (row : Le) (step : SStep)
    (hstated : step.stated = asSLe row) (bound : SLe)
    (hnew : spoolAsm (pool ++ [sentryOf pool step])
      ((ctx.push row step hstated).index row) = {bound})
    {asms : SAsm}
    (hsupported : AssumptionsSupported (ctx.push row step hstated) asms) :
    AssumptionsSupported ctx (asms.erase bound) := by
  intro t ht
  have htne : t ≠ bound := (Finset.mem_erase.mp ht).1
  obtain ⟨candidate, hcandidate, htSource⟩ :=
    hsupported t (Finset.mem_of_mem_erase ht)
  by_cases heq : candidate = row
  · subst candidate
    rw [hnew] at htSource
    exact absurd (Finset.mem_singleton.mp htSource) htne
  · have htail : candidate ∈ rows := by
      rcases List.mem_cons.mp hcandidate with hhead | htail
      · exact absurd hhead heq
      · exact htail
    refine ⟨candidate, htail, ?_⟩
    have hindex :
        (ctx.push row step hstated).index candidate = ctx.index candidate := by
      simp [PoolContext.push, heq]
    rw [hindex] at htSource
    rw [spoolAsm_append_of_lt pool [sentryOf pool step]
      (ctx.index candidate) (ctx.index_lt candidate htail)] at htSource
    exact htSource

theorem supported_push_of_new_supported {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (row : Le) (step : SStep)
    (hstated : step.stated = asSLe row)
    (hnew : AssumptionsSupported ctx
      (spoolAsm (pool ++ [sentryOf pool step])
        ((ctx.push row step hstated).index row)))
    {asms : SAsm}
    (hsupported : AssumptionsSupported (ctx.push row step hstated) asms) :
    AssumptionsSupported ctx asms := by
  intro t ht
  obtain ⟨candidate, hcandidate, htSource⟩ := hsupported t ht
  by_cases heq : candidate = row
  · subst candidate
    exact hnew t htSource
  · have htail : candidate ∈ rows := by
      rcases List.mem_cons.mp hcandidate with hhead | htail
      · exact absurd hhead heq
      · exact htail
    refine ⟨candidate, htail, ?_⟩
    have hindex :
        (ctx.push row step hstated).index candidate = ctx.index candidate := by
      simp [PoolContext.push, heq]
    rw [hindex] at htSource
    rw [spoolAsm_append_of_lt pool [sentryOf pool step]
      (ctx.index candidate) (ctx.index_lt candidate htail)] at htSource
    exact htSource

theorem linDerive_assumptions_supported {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le))
    (hrows : ∀ p ∈ comb, p.2 ∈ rows) :
    AssumptionsSupported ctx
      (sentryOf pool (linDeriveStep ctx comb)).2 := by
  intro t ht
  change t ∈ collectAsms pool (deriveIndices ctx comb) at ht
  obtain ⟨p, hp, ht⟩ := mem_collectAsms_iff.mp ht
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨q.2, hrows q hq, ht⟩
  · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
    exact ⟨row, hrow, ht⟩

theorem linDerive_assumptions_cover {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le)) :
    AssumptionsCover ctx (sentryOf pool (linDeriveStep ctx comb)).2 := by
  intro row hrow t ht
  change t ∈ collectAsms pool (deriveIndices ctx comb)
  apply mem_collectAsms_iff.mpr
  refine ⟨(0, ctx.index row), ?_, ht⟩
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨row, hrow, rfl⟩

theorem roundDerive_assumptions_eq {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (comb : List (ℚ × Le)) :
    let linStep := linDeriveStep ctx comb
    let linPool := pool ++ [sentryOf pool linStep]
    let roundStep := roundDeriveStep pool.length comb
    (sentryOf linPool roundStep).2 = (sentryOf pool linStep).2 := by
  simp [roundDeriveStep, sentryOf, collectAsms, spoolAsm_append_last]

/-! ## Compiled subderivations -/

structure Compilation (intVars : List Nat) (rows : List Le) (pool : SPool)
    (ctx : PoolContext rows pool) where
  steps : List SStep
  finalIndex : Nat
  valid : DerivationValid intVars pool steps
  final_lt : finalIndex < (sfreplay pool steps).length
  final_last :
    (sfreplay pool steps).getLast? =
      some ((sfreplay pool steps).getD finalIndex sdflt)
  final_labsurd : LAbsurd (spoolRow (sfreplay pool steps) finalIndex)
  assumptions_supported :
    AssumptionsSupported ctx (spoolAsm (sfreplay pool steps) finalIndex)
  assumptions_cover :
    AssumptionsCover ctx (spoolAsm (sfreplay pool steps) finalIndex)

structure SupportedCompilation (intVars : List Nat) (rows : List Le) (pool : SPool)
    (ctx : PoolContext rows pool) where
  steps : List SStep
  finalIndex : Nat
  valid : DerivationValid intVars pool steps
  final_lt : finalIndex < (sfreplay pool steps).length
  final_last :
    (sfreplay pool steps).getLast? =
      some ((sfreplay pool steps).getD finalIndex sdflt)
  final_labsurd : LAbsurd (spoolRow (sfreplay pool steps) finalIndex)
  assumptions_supported :
    AssumptionsSupported ctx (spoolAsm (sfreplay pool steps) finalIndex)

def Compilation.toSupported {intVars : List Nat} {rows : List Le}
    {pool : SPool} {ctx : PoolContext rows pool}
    (compiled : Compilation intVars rows pool ctx) :
    SupportedCompilation intVars rows pool ctx where
  steps := compiled.steps
  finalIndex := compiled.finalIndex
  valid := compiled.valid
  final_lt := compiled.final_lt
  final_last := compiled.final_last
  final_labsurd := compiled.final_labsurd
  assumptions_supported := compiled.assumptions_supported

theorem sfreplay_append (pool : SPool) (first second : List SStep) :
    sfreplay pool (first ++ second) =
      sfreplay (sfreplay pool first) second := by
  induction first generalizing pool with
  | nil => rfl
  | cons step steps ih =>
      change sfreplay (pool ++ [sentryOf pool step]) (steps ++ second) =
        sfreplay (sfreplay (pool ++ [sentryOf pool step]) steps) second
      exact ih (pool ++ [sentryOf pool step])

theorem derivationValid_append {intVars : List Nat} {pool : SPool}
    {first second : List SStep}
    (hfirst : DerivationValid intVars pool first)
    (hsecond : DerivationValid intVars (sfreplay pool first) second) :
    DerivationValid intVars pool (first ++ second) := by
  induction first generalizing pool with
  | nil => exact hsecond
  | cons step steps ih =>
      obtain ⟨hstep, hrest⟩ := hfirst
      exact ⟨hstep, ih hrest hsecond⟩

theorem length_le_sfreplay (pool : SPool) (steps : List SStep) :
    pool.length ≤ (sfreplay pool steps).length := by
  induction steps generalizing pool with
  | nil => exact le_rfl
  | cons step steps ih =>
      exact le_trans (by simp) (ih (pool ++ [sentryOf pool step]))

theorem spoolRow_sfreplay_of_lt (pool : SPool) (steps : List SStep)
    (i : Nat) (h : i < pool.length) :
    spoolRow (sfreplay pool steps) i = spoolRow pool i := by
  induction steps generalizing pool with
  | nil => rfl
  | cons step steps ih =>
      change spoolRow (sfreplay (pool ++ [sentryOf pool step]) steps) i =
        spoolRow pool i
      rw [ih (pool ++ [sentryOf pool step]) (by simp; omega)]
      exact spoolRow_append_of_lt pool [sentryOf pool step] i h

theorem spoolAsm_sfreplay_of_lt (pool : SPool) (steps : List SStep)
    (i : Nat) (h : i < pool.length) :
    spoolAsm (sfreplay pool steps) i = spoolAsm pool i := by
  induction steps generalizing pool with
  | nil => rfl
  | cons step steps ih =>
      change spoolAsm (sfreplay (pool ++ [sentryOf pool step]) steps) i =
        spoolAsm pool i
      rw [ih (pool ++ [sentryOf pool step]) (by simp; omega)]
      exact spoolAsm_append_of_lt pool [sentryOf pool step] i h

theorem PoolContext.replay_index {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (steps : List SStep) (row : Le) :
    (ctx.replay steps).index row = ctx.index row := by
  induction steps generalizing pool with
  | nil => rfl
  | cons step steps ih =>
      exact ih (ctx.weaken [sentryOf pool step])

theorem PoolContext.replay_asm {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (steps : List SStep)
    (row : Le) (hrow : row ∈ rows) :
    spoolAsm (sfreplay pool steps) ((ctx.replay steps).index row) =
      spoolAsm pool (ctx.index row) := by
  rw [ctx.replay_index steps row]
  exact spoolAsm_sfreplay_of_lt pool steps (ctx.index row) (ctx.index_lt row hrow)

theorem assumptionsSupported_replay_iff {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (steps : List SStep) (asms : SAsm) :
    AssumptionsSupported (ctx.replay steps) asms ↔
      AssumptionsSupported ctx asms := by
  constructor
  · intro h t ht
    obtain ⟨row, hrow, htRow⟩ := h t ht
    refine ⟨row, hrow, ?_⟩
    rw [PoolContext.replay_asm ctx steps row hrow] at htRow
    exact htRow
  · intro h t ht
    obtain ⟨row, hrow, htRow⟩ := h t ht
    refine ⟨row, hrow, ?_⟩
    rw [PoolContext.replay_asm ctx steps row hrow]
    exact htRow

noncomputable def compile_leaf {rows : List Le} {pool : SPool} {intVars : List Nat}
    (ctx : PoolContext rows pool) {comb : List (ℚ × Le)}
    (hvalid : RefTree.Valid (fun idx => idx ∈ intVars) rows (.leaf comb))
    (hcover : LeavesCover rows (.leaf comb)) :
    Compilation intVars rows pool ctx := by
  let step := leafStep ctx comb
  refine
    { steps := [step]
      finalIndex := pool.length
      valid := ?_
      final_lt := ?_
      final_last := ?_
      final_labsurd := ?_
      assumptions_supported := ?_
      assumptions_cover := ?_ }
  · exact ⟨leafStep_valid ctx hvalid, trivial⟩
  · simp [sfreplay]
  · simp [sfreplay, step]
  · rw [show sfreplay pool [step] = pool ++ [sentryOf pool step] by rfl]
    rw [spoolRow_append_last, sentryOf_fst]
    exact leafStep_labsurd ctx hvalid
  · intro t ht
    rw [show sfreplay pool [step] = pool ++ [sentryOf pool step] by rfl,
      spoolAsm_append_last] at ht
    change t ∈ collectAsms pool (indexedComb ctx comb) at ht
    obtain ⟨p, hp, ht⟩ := mem_collectAsms_iff.mp ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨q.2, hvalid.2.1 q hq, ht⟩
  · intro row hrow t ht
    rw [show sfreplay pool [step] = pool ++ [sentryOf pool step] by rfl,
      spoolAsm_append_last]
    change t ∈ collectAsms pool (indexedComb ctx comb)
    apply mem_collectAsms_iff.mpr
    refine ⟨(0, ctx.index row), ?_, ht⟩
    apply List.mem_map.mpr
    exact ⟨(0, row), hcover row hrow, rfl⟩

def sealIndices {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (finalIndex : Nat) :
    List (ℚ × Nat) :=
  (1, finalIndex) :: rows.map fun row => (0, ctx.index row)

def sealStep {rows : List Le} (pool : SPool)
    (ctx : PoolContext rows pool) (finalIndex : Nat) : SStep :=
  ⟨spoolRow pool finalIndex, .lin (sealIndices ctx finalIndex)⟩

theorem zeroIndices_evalReal (rows : List Le) (pool : SPool)
    (index : Le → Nat) (a : RealValuation) :
    ((resolve pool (rows.map fun row => (0, index row))).map
      (fun p => (p.1 : ℝ) * evalReal p.2.form a)).sum = 0 := by
  simp [resolve, Function.comp_def]

theorem zeroIndices_rhs (rows : List Le) (pool : SPool) (index : Le → Nat) :
    ((resolve pool (rows.map fun row => (0, index row))).map
      fun p => p.1 * p.2.rhs).sum = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, resolve, List.sum_cons, zero_mul, zero_add]
      exact ih

theorem seal_scomb_evalReal {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (finalIndex : Nat) (a : RealValuation) :
    evalReal (scomb (resolve pool (sealIndices ctx finalIndex))).form a =
      evalReal (spoolRow pool finalIndex).form a := by
  rw [evalReal_scomb]
  simp only [sealIndices, resolve, List.map_cons, List.sum_cons, Rat.cast_one, one_mul]
  have hz := zeroIndices_evalReal rows pool ctx.index a
  simp only [resolve] at hz
  rw [hz]
  ring

theorem seal_scomb_rhs {rows : List Le} {pool : SPool}
    (ctx : PoolContext rows pool) (finalIndex : Nat) :
    (scomb (resolve pool (sealIndices ctx finalIndex))).rhs =
    (spoolRow pool finalIndex).rhs := by
  rw [scomb_rhs]
  simp only [sealIndices, resolve, List.map_cons, List.sum_cons]
  change 1 * (spoolRow pool finalIndex).rhs +
      ((resolve pool (rows.map fun row => (0, ctx.index row))).map
        fun p => p.1 * p.2.rhs).sum =
    (spoolRow pool finalIndex).rhs
  rw [zeroIndices_rhs]
  ring

theorem sealStep_valid {rows : List Le} {pool : SPool} {intVars : List Nat}
    (ctx : PoolContext rows pool) {finalIndex : Nat}
    (hfinal : finalIndex < pool.length)
    (habsurd : LAbsurd (spoolRow pool finalIndex)) :
    StepValid intVars pool (sealStep pool ctx finalIndex) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    change p ∈ (1, finalIndex) :: rows.map (fun row => (0, ctx.index row)) at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hfinal
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
      exact ctx.index_lt row hrow
  · change LinValid (spoolRow pool finalIndex)
      (resolve pool (sealIndices ctx finalIndex))
    right
    refine ⟨?_, Or.inl ⟨habsurd.2.1, ?_, ?_⟩⟩
    · intro a
      exact seal_scomb_evalReal ctx finalIndex a
    · intro p hp
      simp only [sealIndices, resolve, List.map_cons] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      ·
        simp [habsurd.2.1, senseSignReal]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hq
        rw [ctx.row_eq row hrow]
        simp [asSLe, senseSignReal]
    · rw [seal_scomb_rhs]

noncomputable def sealSupportedCompilation {rows : List Le} {pool : SPool}
    {intVars : List Nat} {ctx : PoolContext rows pool}
    (compiled : SupportedCompilation intVars rows pool ctx) :
    Compilation intVars rows pool ctx := by
  let finalPool := sfreplay pool compiled.steps
  let finalCtx := ctx.replay compiled.steps
  let step := sealStep finalPool finalCtx compiled.finalIndex
  refine
    { steps := compiled.steps ++ [step]
      finalIndex := finalPool.length
      valid := ?_
      final_lt := ?_
      final_last := ?_
      final_labsurd := ?_
      assumptions_supported := ?_
      assumptions_cover := ?_ }
  · apply derivationValid_append compiled.valid
    exact ⟨sealStep_valid finalCtx compiled.final_lt compiled.final_labsurd, trivial⟩
  · rw [sfreplay_append]
    simp [finalPool, sfreplay]
  · rw [sfreplay_append]
    simp [finalPool, sfreplay, step]
  · rw [sfreplay_append]
    change LAbsurd
      (spoolRow (finalPool ++ [sentryOf finalPool step]) finalPool.length)
    rw [spoolRow_append_last, sentryOf_fst]
    exact compiled.final_labsurd
  · intro t ht
    rw [sfreplay_append] at ht
    change t ∈
      spoolAsm (finalPool ++ [sentryOf finalPool step]) finalPool.length at ht
    rw [spoolAsm_append_last] at ht
    change t ∈ collectAsms finalPool
      (sealIndices finalCtx compiled.finalIndex) at ht
    obtain ⟨p, hp, ht⟩ := mem_collectAsms_iff.mp ht
    change p ∈
      (1, compiled.finalIndex) ::
        rows.map (fun row => (0, finalCtx.index row)) at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact compiled.assumptions_supported t ht
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
      refine ⟨row, hrow, ?_⟩
      rw [PoolContext.replay_asm ctx compiled.steps row hrow] at ht
      exact ht
  · intro row hrow t ht
    rw [sfreplay_append]
    change t ∈
      spoolAsm (finalPool ++ [sentryOf finalPool step]) finalPool.length
    rw [spoolAsm_append_last]
    change t ∈ collectAsms finalPool
      (sealIndices finalCtx compiled.finalIndex)
    apply mem_collectAsms_iff.mpr
    refine ⟨(0, finalCtx.index row), ?_, ?_⟩
    · change (0, finalCtx.index row) ∈
        (1, compiled.finalIndex) ::
          rows.map (fun candidate => (0, finalCtx.index candidate))
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, hrow, rfl⟩)
    · rw [PoolContext.replay_asm ctx compiled.steps row hrow]
      exact ht

noncomputable def sealCompilation {rows : List Le} {pool : SPool}
    {intVars : List Nat} {ctx : PoolContext rows pool}
    (compiled : Compilation intVars rows pool ctx) :
    Compilation intVars rows pool ctx :=
  sealSupportedCompilation compiled.toSupported

noncomputable def compileTree {intVars : List Nat} :
    ∀ {rows : List Le} {pool : SPool}
      (ctx : PoolContext rows pool) (tree : RefTree),
      RefTree.Valid (fun idx => idx ∈ intVars) rows tree →
      LeavesCover rows tree →
      Compilation intVars rows pool ctx := by
  intro rows pool ctx tree hvalid hcover
  induction tree generalizing rows pool with
  | leaf comb =>
      exact compile_leaf ctx hvalid hcover
  | derive comb rnd sub ih =>
      obtain ⟨hnonnegative, hrows, hterms, hSubValid⟩ := hvalid
      cases rnd with
      | false =>
          let step := linDeriveStep ctx comb
          have hStep : StepValid intVars pool step :=
            linDeriveStep_valid ctx hnonnegative hrows
          let stepPool := pool ++ [sentryOf pool step]
          let row := deriveRow comb false
          have hStated : step.stated = asSLe row := by
            simp [step, row, linDeriveStep, deriveRow]
          let subCtx : PoolContext (row :: rows) stepPool :=
            ctx.push row step hStated
          let subCompiled := ih subCtx hSubValid hcover
          have hNewAsm :
              spoolAsm stepPool (subCtx.index row) =
                (sentryOf pool step).2 := by
            simp [stepPool, subCtx, PoolContext.push,
              spoolAsm_append_last]
          have hNewSupported :
              AssumptionsSupported ctx
                (spoolAsm stepPool (subCtx.index row)) := by
            rw [hNewAsm]
            exact linDerive_assumptions_supported ctx comb hrows
          refine
            { steps := step :: subCompiled.steps
              finalIndex := subCompiled.finalIndex
              valid := ⟨hStep, subCompiled.valid⟩
              final_lt := subCompiled.final_lt
              final_last := subCompiled.final_last
              final_labsurd := subCompiled.final_labsurd
              assumptions_supported := ?_
              assumptions_cover := ?_ }
          · exact supported_push_of_new_supported ctx row step hStated
              hNewSupported subCompiled.assumptions_supported
          · intro parentRow hParentRow t ht
            apply subCompiled.assumptions_cover row (by simp)
            rw [hNewAsm]
            exact linDerive_assumptions_cover ctx comb parentRow hParentRow ht
      | true =>
          let linStep := linDeriveStep ctx comb
          have hLinStep : StepValid intVars pool linStep :=
            linDeriveStep_valid ctx hnonnegative hrows
          let linPool := pool ++ [sentryOf pool linStep]
          let oldCtx : PoolContext rows linPool :=
            ctx.weaken [sentryOf pool linStep]
          let roundStep := roundDeriveStep pool.length comb
          have hSource : pool.length < linPool.length := by
            simp [linPool]
          have hSourceRow :
              spoolRow linPool pool.length = asSLe (combine comb) := by
            rw [show linPool = pool ++ [sentryOf pool linStep] by rfl]
            rw [spoolRow_append_last, sentryOf_fst]
            rfl
          have hRoundStep : StepValid intVars linPool roundStep :=
            roundDeriveStep_valid hSource hSourceRow (hterms rfl)
          let roundPool := linPool ++ [sentryOf linPool roundStep]
          let row := deriveRow comb true
          have hStated : roundStep.stated = asSLe row := rfl
          let subCtx : PoolContext (row :: rows) roundPool :=
            oldCtx.push row roundStep hStated
          let subCompiled := ih subCtx hSubValid hcover
          have hRoundAsm :
              (sentryOf linPool roundStep).2 =
                (sentryOf pool linStep).2 :=
            roundDerive_assumptions_eq ctx comb
          have hNewAsm :
              spoolAsm roundPool (subCtx.index row) =
                (sentryOf pool linStep).2 := by
            simp only [subCtx, PoolContext.push, ite_true]
            rw [show roundPool =
              linPool ++ [sentryOf linPool roundStep] by rfl]
            rw [spoolAsm_append_last, hRoundAsm]
          have hNewSupportedCtx :
              AssumptionsSupported ctx
                (spoolAsm roundPool (subCtx.index row)) := by
            rw [hNewAsm]
            exact linDerive_assumptions_supported ctx comb hrows
          have hNewSupportedOld :
              AssumptionsSupported oldCtx
                (spoolAsm roundPool (subCtx.index row)) :=
            (assumptionsSupported_weaken_iff ctx
              [sentryOf pool linStep] _).mpr hNewSupportedCtx
          refine
            { steps := linStep :: roundStep :: subCompiled.steps
              finalIndex := subCompiled.finalIndex
              valid := ⟨hLinStep, hRoundStep, subCompiled.valid⟩
              final_lt := subCompiled.final_lt
              final_last := subCompiled.final_last
              final_labsurd := subCompiled.final_labsurd
              assumptions_supported := ?_
              assumptions_cover := ?_ }
          · have hOld :=
              supported_push_of_new_supported oldCtx row roundStep hStated
                hNewSupportedOld subCompiled.assumptions_supported
            exact
              (assumptionsSupported_weaken_iff ctx
                [sentryOf pool linStep] _).mp hOld
          · intro parentRow hParentRow t ht
            apply subCompiled.assumptions_cover row (by simp)
            rw [hNewAsm]
            exact linDerive_assumptions_cover ctx comb parentRow hParentRow ht
  | split idx k lower upper ihLower ihUpper =>
      obtain ⟨hidx, hLowerValid, hUpperValid⟩ := hvalid
      obtain ⟨hLowerCover, hUpperCover⟩ := hcover
      let lowerStep := asmStep (lowerBound idx k)
      let lowerPool := pool ++ [sentryOf pool lowerStep]
      let lowerCtx : PoolContext (leLower idx (k : ℚ) :: rows) lowerPool :=
        ctx.push (leLower idx (k : ℚ)) lowerStep rfl
      let lowerCompiled :=
        ihLower lowerCtx hLowerValid hLowerCover
      let lowerPrefix := lowerStep :: lowerCompiled.steps
      have hLowerPrefix :
          DerivationValid intVars pool lowerPrefix :=
        ⟨asmStep_valid intVars pool (lowerBound idx k), lowerCompiled.valid⟩
      let afterLower := sfreplay pool lowerPrefix
      have hAfterLower :
          afterLower = sfreplay lowerPool lowerCompiled.steps := by
        rfl
      let afterLowerCtx := ctx.replay lowerPrefix
      let upperAsm := asmStep (upperBound idx k)
      let upperAsmIndex := afterLower.length
      let upperAsmPool := afterLower ++ [sentryOf afterLower upperAsm]
      let upperOldCtx : PoolContext rows upperAsmPool :=
        afterLowerCtx.weaken [sentryOf afterLower upperAsm]
      let upperNorm := normalizeUpperStep upperAsmIndex idx k
      have hUpperAsmIndex : upperAsmIndex < upperAsmPool.length := by
        simp [upperAsmIndex, upperAsmPool]
      have hUpperAsmRow :
          spoolRow upperAsmPool upperAsmIndex = upperBound idx k := by
        rw [show upperAsmIndex = afterLower.length by rfl]
        rw [show upperAsmPool =
          afterLower ++ [sentryOf afterLower upperAsm] by rfl]
        rw [spoolRow_append_last, sentryOf_fst]
        rfl
      have hUpperNorm :
          StepValid intVars upperAsmPool upperNorm :=
        normalizeUpperStep_valid hUpperAsmIndex hUpperAsmRow
      let upperPool := upperAsmPool ++ [sentryOf upperAsmPool upperNorm]
      let upperCtx : PoolContext (leUpper idx (k : ℚ) :: rows) upperPool :=
        upperOldCtx.push (leUpper idx (k : ℚ)) upperNorm rfl
      let upperCompiled :=
        ihUpper upperCtx hUpperValid hUpperCover
      let upperPrefix := upperAsm :: upperNorm :: upperCompiled.steps
      have hUpperPrefix :
          DerivationValid intVars afterLower upperPrefix :=
        ⟨asmStep_valid intVars afterLower (upperBound idx k),
          hUpperNorm, upperCompiled.valid⟩
      let afterUpper := sfreplay afterLower upperPrefix
      let lowerResult := lowerCompiled.finalIndex
      let lowerBoundIndex := pool.length
      let upperResult := upperCompiled.finalIndex
      let upperBoundIndex := upperAsmIndex
      have hLowerResult : lowerResult < afterUpper.length := by
        apply lt_of_lt_of_le lowerCompiled.final_lt
        exact length_le_sfreplay afterLower upperPrefix
      have hUpperResult : upperResult < afterUpper.length := by
        exact upperCompiled.final_lt
      have hLowerBoundIndex : lowerBoundIndex < afterUpper.length := by
        have hbase : lowerBoundIndex < lowerPool.length := by
          simp [lowerBoundIndex, lowerPool]
        have htail := length_le_sfreplay lowerPool
          (lowerCompiled.steps ++ upperPrefix)
        have heq :
            afterUpper =
              sfreplay lowerPool (lowerCompiled.steps ++ upperPrefix) := by
          change sfreplay afterLower upperPrefix =
            sfreplay lowerPool (lowerCompiled.steps ++ upperPrefix)
          rw [hAfterLower, sfreplay_append]
        rw [heq]
        exact lt_of_lt_of_le hbase htail
      have hUpperBoundIndex : upperBoundIndex < afterUpper.length := by
        have hbase : upperBoundIndex < upperAsmPool.length := hUpperAsmIndex
        have htail := length_le_sfreplay upperAsmPool
          (upperNorm :: upperCompiled.steps)
        have heq :
            afterUpper =
              sfreplay upperAsmPool (upperNorm :: upperCompiled.steps) := by
          rfl
        rw [heq]
        exact lt_of_lt_of_le hbase htail
      have hLowerAbsurd :
          LAbsurd (spoolRow afterUpper lowerResult) := by
        rw [spoolRow_sfreplay_of_lt afterLower upperPrefix
          lowerResult lowerCompiled.final_lt]
        exact lowerCompiled.final_labsurd
      have hUpperAbsurd :
          LAbsurd (spoolRow afterUpper upperResult) :=
        upperCompiled.final_labsurd
      have hLowerBoundRow :
          spoolRow afterUpper lowerBoundIndex = lowerBound idx k := by
        have heq :
            afterUpper =
              sfreplay lowerPool (lowerCompiled.steps ++ upperPrefix) := by
          change sfreplay afterLower upperPrefix =
            sfreplay lowerPool (lowerCompiled.steps ++ upperPrefix)
          rw [hAfterLower, sfreplay_append]
        rw [heq]
        rw [spoolRow_sfreplay_of_lt lowerPool
          (lowerCompiled.steps ++ upperPrefix) lowerBoundIndex (by
            simp [lowerBoundIndex, lowerPool])]
        rw [show lowerBoundIndex = pool.length by rfl]
        rw [show lowerPool = pool ++ [sentryOf pool lowerStep] by rfl]
        rw [spoolRow_append_last, sentryOf_fst]
        rfl
      have hUpperBoundRow :
          spoolRow afterUpper upperBoundIndex = upperBound idx k := by
        have heq :
            afterUpper =
              sfreplay upperAsmPool (upperNorm :: upperCompiled.steps) := by
          rfl
        rw [heq]
        rw [spoolRow_sfreplay_of_lt upperAsmPool
          (upperNorm :: upperCompiled.steps) upperBoundIndex hUpperAsmIndex]
        exact hUpperAsmRow
      have hBounds :
          ComplementaryBounds intVars
            (spoolRow afterUpper lowerBoundIndex)
            (spoolRow afterUpper upperBoundIndex) := by
        rw [hLowerBoundRow, hUpperBoundRow]
        exact complementary_bounds k hidx
      have hLowerMem :
          spoolRow afterUpper lowerBoundIndex ∈
            spoolAsm afterUpper lowerResult := by
        rw [hLowerBoundRow]
        rw [spoolAsm_sfreplay_of_lt afterLower upperPrefix
          lowerResult lowerCompiled.final_lt]
        apply lowerCompiled.assumptions_cover (leLower idx (k : ℚ)) (by simp)
        exact lowerContext_bound_mem ctx idx k
      have hUpperAsmAsms :
          spoolAsm upperAsmPool upperAsmIndex = {upperBound idx k} := by
        rw [show upperAsmIndex = afterLower.length by rfl]
        rw [show upperAsmPool =
          afterLower ++ [sentryOf afterLower upperAsm] by rfl]
        rw [spoolAsm_append_last]
        simp [upperAsm, asmStep, sentryOf]
      have hUpperMem :
          spoolRow afterUpper upperBoundIndex ∈
            spoolAsm afterUpper upperResult := by
        rw [hUpperBoundRow]
        apply upperCompiled.assumptions_cover (leUpper idx (k : ℚ)) (by simp)
        exact upperContext_bound_mem upperOldCtx upperAsmIndex idx k hUpperAsmAsms
      let uns :=
        unsStep lowerResult lowerBoundIndex upperResult upperBoundIndex
      have hUns : StepValid intVars afterUpper uns := by
        exact unsStep_valid hLowerResult hLowerBoundIndex hUpperResult
          hUpperBoundIndex hLowerAbsurd hUpperAbsurd hBounds hLowerMem hUpperMem
      have hLowerErased :
          AssumptionsSupported ctx
            ((spoolAsm afterUpper lowerResult).erase (lowerBound idx k)) := by
        have hbase :=
          erase_supported_push ctx (leLower idx (k : ℚ)) lowerStep rfl
            (lowerBound idx k) (lowerContext_bound_asm ctx idx k)
            lowerCompiled.assumptions_supported
        intro t ht
        rw [spoolAsm_sfreplay_of_lt afterLower upperPrefix
          lowerResult lowerCompiled.final_lt] at ht
        exact hbase t ht
      have hUpperErased :
          AssumptionsSupported ctx
            ((spoolAsm afterUpper upperResult).erase (upperBound idx k)) := by
        have hbase :
            AssumptionsSupported upperOldCtx
              ((spoolAsm afterUpper upperResult).erase (upperBound idx k)) :=
          erase_supported_push upperOldCtx (leUpper idx (k : ℚ)) upperNorm rfl
            (upperBound idx k)
            (upperContext_bound_asm upperOldCtx upperAsmIndex idx k
              hUpperAsmAsms)
            upperCompiled.assumptions_supported
        have hReplay :
            AssumptionsSupported afterLowerCtx
              ((spoolAsm afterUpper upperResult).erase (upperBound idx k)) :=
          (assumptionsSupported_weaken_iff afterLowerCtx
            [sentryOf afterLower upperAsm] _).mp hbase
        exact
          (assumptionsSupported_replay_iff ctx lowerPrefix _).mp hReplay
      let allPrefix := lowerPrefix ++ upperPrefix
      have hAllPrefix :
          DerivationValid intVars pool allPrefix :=
        derivationValid_append hLowerPrefix hUpperPrefix
      have hAllPool : sfreplay pool allPrefix = afterUpper := by
        change sfreplay pool (lowerPrefix ++ upperPrefix) = afterUpper
        rw [sfreplay_append]
      let raw : SupportedCompilation intVars rows pool ctx := by
        refine
          { steps := allPrefix ++ [uns]
            finalIndex := afterUpper.length
            valid := ?_
            final_lt := ?_
            final_last := ?_
            final_labsurd := ?_
            assumptions_supported := ?_ }
        · apply derivationValid_append hAllPrefix
          rw [hAllPool]
          exact ⟨hUns, trivial⟩
        · rw [sfreplay_append]
          rw [hAllPool]
          change afterUpper.length <
            (afterUpper ++ [sentryOf afterUpper uns]).length
          simp
        · rw [sfreplay_append]
          rw [hAllPool]
          simp [sfreplay, uns]
        · rw [sfreplay_append]
          rw [hAllPool]
          change LAbsurd
            (spoolRow (afterUpper ++ [sentryOf afterUpper uns])
              afterUpper.length)
          rw [spoolRow_append_last, sentryOf_fst]
          exact contradictionRow_labsurd
        · intro t ht
          rw [sfreplay_append] at ht
          rw [hAllPool] at ht
          change t ∈
            spoolAsm (afterUpper ++ [sentryOf afterUpper uns])
              afterUpper.length at ht
          rw [spoolAsm_append_last] at ht
          change t ∈
            (spoolAsm afterUpper lowerResult).erase
                (spoolRow afterUpper lowerBoundIndex) ∪
              (spoolAsm afterUpper upperResult).erase
                (spoolRow afterUpper upperBoundIndex) at ht
          rw [hLowerBoundRow, hUpperBoundRow] at ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact hLowerErased t ht
          · exact hUpperErased t ht
      exact sealSupportedCompilation raw

noncomputable def initialContext (rows : List Le) :
    PoolContext rows (sinitPool (rows.map asSLe)) where
  index row := rows.idxOf row
  index_lt row hrow := by
    simp only [sinitPool, List.length_map]
    exact List.idxOf_lt_length_of_mem hrow
  row_eq row hrow := by
    have hlt := List.idxOf_lt_length_of_mem hrow
    unfold spoolRow sinitPool
    rw [List.getD_eq_getElem _ _ (by
      simp only [List.length_map]
      exact hlt)]
    simp only [List.getElem_map]
    rw [List.getElem_idxOf hlt]

theorem initialContext_asm_empty (rows : List Le) (row : Le) (hrow : row ∈ rows) :
    spoolAsm (sinitPool (rows.map asSLe)) ((initialContext rows).index row) = ∅ := by
  have hlt := List.idxOf_lt_length_of_mem hrow
  unfold spoolAsm sinitPool initialContext
  rw [List.getD_eq_getElem _ _ (by
    simp only [List.length_map]
    exact hlt)]
  simp

/-- Every valid refutation tree compiles to a flat, closed VIPR proof. -/
theorem refTree_proof_complete {rows : List Le} {intVars : List Nat}
    {tree : RefTree}
    (hvalid : RefTree.Valid (fun idx => idx ∈ intVars) rows tree) :
    ∃ steps, ProofValid intVars (rows.map asSLe) steps := by
  let padded := padLeaves rows tree
  have hPaddedValid :
      RefTree.Valid (fun idx => idx ∈ intVars) rows padded :=
    padLeaves_valid _ rows tree hvalid
  let ctx := initialContext rows
  let compiled :=
    compileTree ctx padded hPaddedValid (padLeaves_cover rows tree)
  refine ⟨compiled.steps, compiled.valid, ?_⟩
  let finalPool := sfreplay (sinitPool (rows.map asSLe)) compiled.steps
  let finalEntry := finalPool.getD compiled.finalIndex sdflt
  refine ⟨finalEntry, compiled.final_last, ?_, ?_⟩
  · ext t
    constructor
    · intro ht
      have ht' : t ∈ spoolAsm finalPool compiled.finalIndex := ht
      obtain ⟨row, hrow, htRow⟩ := compiled.assumptions_supported t ht'
      rw [initialContext_asm_empty rows row hrow] at htRow
      simp at htRow
    · simp
  · exact compiled.final_labsurd.absurd

/-- Split-only trees are a specialization of the full compiler theorem. -/
theorem noDerive_proof_complete {rows : List Le} {intVars : List Nat}
    {tree : RefTree}
    (hvalid : RefTree.Valid (fun idx => idx ∈ intVars) rows tree)
    (_ : tree.NoDerive) :
    ∃ steps, ProofValid intVars (rows.map asSLe) steps :=
  refTree_proof_complete hvalid

/-- Explicitly bounded integer-infeasible systems admit concrete flat VIPR proofs. -/
theorem bounded_proof_complete (intVars : List Nat)
    (specs : List BoundedCompleteness.Interval) (rows : List Le)
    (hIsInt : ∀ s ∈ specs, s.idx ∈ intVars)
    (hBounds : BoundedCompleteness.BoundsPresent rows specs)
    (hinfeasible : BoundedCompleteness.NoIntSolution specs rows) :
    ∃ steps, ProofValid intVars (rows.map asSLe) steps := by
  obtain ⟨tree, hvalid, hNoDerive⟩ :=
    BoundedCompleteness.bounded_refTree_complete_noDerive
      (fun idx => idx ∈ intVars) specs rows hIsInt hBounds hinfeasible
  exact noDerive_proof_complete hvalid hNoDerive

end LeanVIPR.Completeness.RefTreeCompile
