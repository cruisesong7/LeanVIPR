module

public import LeanVIPR.Completeness.FarkasCompleteness
public import LeanVIPR.Cert.ViprSystemSound

@[expose] public section

/-!
# Completeness statements for the VIPR proof system

Soundness starts with a certificate and proves semantic validity.  Completeness
goes in the opposite direction: from semantic infeasibility, construct a finite
certificate.

The full MILP theorem has two mathematically distinct ingredients:

1. exact rational LP infeasibility admits rational Farkas multipliers;
2. mixed-integer infeasibility admits a finite branch-and-cut derivation whose
   leaves are such LP refutations.

The first compilation step is proved below: every explicit rational Farkas
witness is representable by a one-step, closed VIPR certificate.  Consequently,
any rational Farkas completeness theorem immediately yields completeness of the
VIPR LP fragment.  The finite mixed-integer branch-and-cut existence theorem is
named separately rather than silently assumed.
-/

namespace LeanVIPR.Completeness.ViprCompleteness

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness LeanVIPR.Completeness.FourierMotzkin
  LeanVIPR.Cert.ViprSystem

/-- A row uses one of the three senses admitted by the VIPR specification. -/
def ValidSense (c : SLe) : Prop :=
  c.sense = 'L' ∨ c.sense = 'G' ∨ c.sense = 'E'

/-- Every input row is a well-formed VIPR linear constraint. -/
def RowsWellFormed (base : List SLe) : Prop :=
  ∀ c ∈ base, ValidSense c

/-- Regard a row's form and right-hand side as a `≤` row. -/
def asLe (c : SLe) : SLe :=
  ⟨'L', c.form, c.rhs⟩

/-- Negate a row's form and right-hand side and regard the result as a `≤` row. -/
def negAsLe (c : SLe) : SLe :=
  ⟨'L', LinForm.scale (-1) c.form, -c.rhs⟩

/-- Normalize one well-formed mixed-sense row to one or two `≤` rows. -/
def normalizeRow (c : SLe) : List SLe :=
  if c.sense = 'L' then [asLe c]
  else if c.sense = 'G' then [negAsLe c]
  else if c.sense = 'E' then [asLe c, negAsLe c]
  else []

/-- Normalize a finite mixed-sense system to a finite `≤` system. -/
def normalizeRows (base : List SLe) : List SLe :=
  base.flatMap normalizeRow

/-- Sense-forgotten normalized rows consumed by rational Fourier--Motzkin elimination. -/
def normalizedLeRows (base : List SLe) : List Le :=
  (normalizeRows base).map SLe.toLe

/-- Provenance of one normalized `≤` row in an original sensed row. -/
structure NormalizedOrigin (base : List SLe) (row : Le) where
  source : Nat
  source_lt : source < base.length
  sign : ℚ
  eval_eq : ∀ a : Valuation,
    LinForm.eval row.form a =
      sign * LinForm.eval (base.getD source default).form a
  rhs_eq : row.rhs = sign * (base.getD source default).rhs
  suitable : (sign : ℝ) * senseSignReal (base.getD source default).sense ≤ 0

theorem normalizeRow_sense {c d : SLe} (hd : d ∈ normalizeRow c) : d.sense = 'L' := by
  simp only [normalizeRow] at hd
  split at hd
  · simp only [List.mem_singleton] at hd
    subst d
    rfl
  · split at hd
    · simp only [List.mem_singleton] at hd
      subst d
      rfl
    · split at hd
      · simp only [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst d
          rfl
        · rcases hd with hd | hd
          · subst d
            rfl
          · simp at hd
      · simp at hd

theorem normalizeRows_wellFormed (base : List SLe) : RowsWellFormed (normalizeRows base) := by
  intro d hd
  simp only [normalizeRows, List.mem_flatMap] at hd
  obtain ⟨c, _, hd⟩ := hd
  exact Or.inl (normalizeRow_sense hd)

theorem normalizedOrigin_of_mem {base : List SLe} {row : Le}
    (hrow : row ∈ normalizedLeRows base) :
    Nonempty (NormalizedOrigin base row) := by
  obtain ⟨normalized, hnormalized, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨sourceRow, hsourceMem, hnormalized⟩ :=
    List.mem_flatMap.mp (show normalized ∈ normalizeRows base from hnormalized)
  obtain ⟨source, hsourceLt, hsourceGet⟩ := List.mem_iff_getElem.mp hsourceMem
  have hgetD : base.getD source default = sourceRow := by
    rw [List.getD_eq_getElem base default hsourceLt, hsourceGet]
  by_cases hL : sourceRow.sense = 'L'
  · simp [normalizeRow, hL] at hnormalized
    subst normalized
    refine ⟨
      { source := source
        source_lt := hsourceLt
        sign := 1
        eval_eq := ?_
        rhs_eq := ?_
        suitable := ?_ }⟩
    · intro a
      rw [hgetD]
      simp [asLe, SLe.toLe]
    · rw [hgetD]
      simp [asLe, SLe.toLe]
    · rw [hgetD]
      simp [senseSignReal, hL]
  · by_cases hG : sourceRow.sense = 'G'
    · simp [normalizeRow, hG] at hnormalized
      subst normalized
      refine ⟨
        { source := source
          source_lt := hsourceLt
          sign := -1
          eval_eq := ?_
          rhs_eq := ?_
          suitable := ?_ }⟩
      · intro a
        rw [hgetD]
        simp [negAsLe, SLe.toLe, LinForm.eval_scale]
      · rw [hgetD]
        simp [negAsLe, SLe.toLe]
      · rw [hgetD]
        simp [senseSignReal, hG]
    · by_cases hE : sourceRow.sense = 'E'
      · have hcases :
            normalized = asLe sourceRow ∨ normalized = negAsLe sourceRow := by
          simpa [normalizeRow, hL, hG, hE] using hnormalized
        rcases hcases with rfl | rfl
        ·
          refine ⟨
            { source := source
              source_lt := hsourceLt
              sign := 1
              eval_eq := ?_
              rhs_eq := ?_
              suitable := ?_ }⟩
          · intro a
            rw [hgetD]
            simp [asLe, SLe.toLe]
          · rw [hgetD]
            simp [asLe, SLe.toLe]
          · rw [hgetD]
            simp [senseSignReal, hE]
        ·
          refine ⟨
            { source := source
              source_lt := hsourceLt
              sign := -1
              eval_eq := ?_
              rhs_eq := ?_
              suitable := ?_ }⟩
          · intro a
            rw [hgetD]
            simp [negAsLe, SLe.toLe, LinForm.eval_scale]
          · rw [hgetD]
            simp [negAsLe, SLe.toLe]
          · rw [hgetD]
            simp [senseSignReal, hE]
      · simp [normalizeRow, hL, hG, hE] at hnormalized

theorem satReal_normalizeRow {c : SLe} {a : RealValuation} (h : ValidSense c) :
    (∀ d ∈ normalizeRow c, satReal d a) ↔ satReal c a := by
  rcases h with hL | hG | hE
  · simp [normalizeRow, asLe, satReal, hL]
  · simp [normalizeRow, negAsLe, satReal, hG, evalReal_scale]
  · simp [normalizeRow, asLe, negAsLe, satReal, hE, evalReal_scale, le_antisymm_iff]

theorem satReal_normalizeRows {base : List SLe} {a : RealValuation}
    (hrows : RowsWellFormed base) :
    (∀ d ∈ normalizeRows base, satReal d a) ↔ ∀ c ∈ base, satReal c a := by
  induction base with
  | nil => simp [normalizeRows]
  | cons c cs ih =>
      have hc := hrows c (by simp)
      have hcs : RowsWellFormed cs := by
        intro d hd
        exact hrows d (by simp [hd])
      rw [show normalizeRows (c :: cs) = normalizeRow c ++ normalizeRows cs by rfl]
      constructor
      · intro h d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (satReal_normalizeRow hc).mp fun e he =>
            h e (List.mem_append.mpr (Or.inl he))
        · exact (ih hcs).mp (fun e he => h e (List.mem_append.mpr (Or.inr he))) d hd
      · intro h d hd
        have hcSat : satReal c a := h c (by simp)
        have hcsSat : ∀ e ∈ cs, satReal e a := by
          intro e he
          exact h e (by simp [he])
        rcases List.mem_append.mp hd with hd | hd
        · exact (satReal_normalizeRow hc).mpr hcSat d hd
        · exact (ih hcs).mpr hcsSat d hd

def SemanticallyInfeasible (base : List SLe) (intVars : List Nat) : Prop :=
  ∀ a : RealValuation,
    (∀ j ∈ intVars, IsIntReal (a j)) →
    (∀ c ∈ base, satReal c a) →
    False

theorem semanticallyInfeasible_normalizeRows {base : List SLe} {intVars : List Nat}
    (hrows : RowsWellFormed base) :
    SemanticallyInfeasible (normalizeRows base) intVars ↔
      SemanticallyInfeasible base intVars := by
  constructor
  · intro h a hint hbase
    exact h a hint ((satReal_normalizeRows hrows).mpr hbase)
  · intro h a hint hnorm
    exact h a hint ((satReal_normalizeRows hrows).mp hnorm)

/-- Embed an exact rational valuation into the real semantics. -/
def ratToReal (a : Valuation) : RealValuation :=
  fun idx => (a idx : ℝ)

theorem evalReal_ratToReal (f : LinForm) (a : Valuation) :
    evalReal f (ratToReal a) = (LinForm.eval f a : ℝ) := by
  induction f with
  | nil => simp [evalReal, LinForm.eval]
  | cons t f ih =>
      simp only [evalReal, LinForm.eval, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp [ratToReal]

/-- Real infeasibility implies rational infeasibility of the normalized `≤` system. -/
theorem ratInfeasible_normalizedLeRows {base : List SLe}
    (hrows : RowsWellFormed base)
    (hinfeasible : SemanticallyInfeasible base []) :
    RatInfeasible (normalizedLeRows base) := by
  intro a hnormalized
  apply hinfeasible (ratToReal a)
  · simp
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

/-- A rational basis valuation selecting one variable coefficient. -/
def basisValuation (idx : Nat) : Valuation :=
  fun j => if j = idx then 1 else 0

theorem eval_basisValuation (f : LinForm) (idx : Nat) :
    LinForm.eval f (basisValuation idx) = coeffAt idx f := by
  induction f with
  | nil => simp [LinForm.eval, coeffAt]
  | cons t f ih =>
      change t.coeff * basisValuation idx t.idx +
          LinForm.eval f (basisValuation idx) =
        coeffAt idx (t :: f)
      rw [ih]
      by_cases h : t.idx = idx
      · simp [basisValuation, coeffAt, h]
      · simp [basisValuation, coeffAt, h]

theorem evalReal_eq_finsupp_sum (f : LinForm) (a : RealValuation) :
    evalReal f a =
      (toFinsupp f).sum fun idx q => (q : ℝ) * a idx := by
  induction f with
  | nil => simp [evalReal, toFinsupp]
  | cons t f ih =>
      rw [show evalReal (t :: f) a =
        (t.coeff : ℝ) * a t.idx + evalReal f a by simp [evalReal]]
      rw [ih]
      rw [show toFinsupp (t :: f) =
        Finsupp.single t.idx t.coeff + toFinsupp f by rfl]
      rw [Finsupp.sum_add_index']
      · simp
      · intro idx
        simp
      · intro idx q₁ q₂
        push_cast
        ring

theorem formZeroReal_of_ratEvalZero {f : LinForm}
    (hzero : ∀ a : Valuation, LinForm.eval f a = 0) :
    FormZeroReal f := by
  have hcoeff : ∀ idx, coeffAt idx f = 0 := by
    intro idx
    rw [← eval_basisValuation]
    exact hzero (basisValuation idx)
  have hfinsupp : toFinsupp f = 0 := by
    ext idx
    simp [hcoeff idx]
  intro a
  rw [evalReal_eq_finsupp_sum, hfinsupp]
  simp

def HasViprRefutation (base : List SLe) (intVars : List Nat) : Prop :=
  ∃ steps : List SStep, ProofValid intVars base steps

/-- The desired semantic completeness statement for VIPR infeasibility proofs. -/
def ProofSystemComplete : Prop :=
  ∀ (base : List SLe) (intVars : List Nat),
    RowsWellFormed base →
    SemanticallyInfeasible base intVars →
    HasViprRefutation base intVars

/-- An exact rational Farkas witness over the initial VIPR pool.  Multipliers may
be signed because suitability is interpreted using each row's sense. -/
structure RationalFarkasWitness (base : List SLe) where
  comb : List (ℚ × Nat)
  referencesPast : ∀ p ∈ comb, p.2 < base.length
  suitable : SuitableLe (resolve (sinitPool base) comb)
  zero : FormZeroReal (scomb (resolve (sinitPool base) comb)).form
  negative : (scomb (resolve (sinitPool base) comb)).rhs < 0

noncomputable def certificateOrigin (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base))
    (p : {p // p ∈ cert.comb}) :
    NormalizedOrigin base ((normalizedLeRows base).getD p.val.2 default) :=
  Classical.choice (normalizedOrigin_of_mem (by
    have hp := cert.referencesPast p.val p.property
    rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp))

noncomputable def mapFarkasComb (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base)) :
    List (ℚ × Nat) :=
  cert.comb.attach.map fun p =>
    let origin := certificateOrigin base cert p
    (p.val.1 * origin.sign, origin.source)

private theorem initial_spoolRow_eq_getD (base : List SLe) {i : Nat}
    (hi : i < base.length) :
    spoolRow (sinitPool base) i = base.getD i default := by
  rw [show spoolRow (sinitPool base) i = ((sinitPool base).getD i sdflt).1 by rfl]
  rw [List.getD_eq_getElem _ _ (by simpa [sinitPool] using hi)]
  rw [List.getD_eq_getElem base default hi]
  simp [sinitPool]

theorem mapFarkasComb_referencesPast (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base)) :
    ∀ p ∈ mapFarkasComb base cert, p.2 < base.length := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact (certificateOrigin base cert q).source_lt

theorem mapFarkasComb_suitable (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base)) :
    SuitableLe (resolve (sinitPool base) (mapFarkasComb base cert)) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
  let origin := certificateOrigin base cert r
  rw [initial_spoolRow_eq_getD base origin.source_lt]
  change (((r.val.1 * origin.sign : ℚ) : ℝ) *
    senseSignReal (base.getD origin.source default).sense) ≤ 0
  rw [Rat.cast_mul, mul_assoc]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact_mod_cast cert.nonnegative r.val r.property
  · exact origin.suitable

theorem mapFarkasComb_eval (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base)) (a : Valuation) :
    LinForm.eval
        (scomb (resolve (sinitPool base) (mapFarkasComb base cert))).form a =
      indexedEval (normalizedLeRows base) cert.comb a := by
  rw [scomb_eval]
  unfold resolve mapFarkasComb
  simp only [List.map_map]
  rw [show indexedEval (normalizedLeRows base) cert.comb a =
      (cert.comb.attach.map fun p =>
        p.val.1 * LinForm.eval
          ((normalizedLeRows base).getD p.val.2 default).form a).sum by
    unfold indexedEval
    exact congrArg List.sum
      (List.attach_map_val
        (l := cert.comb)
        (f := fun p => p.1 *
          LinForm.eval ((normalizedLeRows base).getD p.2 default).form a)).symm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  dsimp only [Function.comp_apply]
  let origin := certificateOrigin base cert p
  change (p.val.1 * origin.sign) *
      LinForm.eval (spoolRow (sinitPool base) origin.source).form a =
    p.val.1 * LinForm.eval
      ((normalizedLeRows base).getD p.val.2 default).form a
  rw [initial_spoolRow_eq_getD base origin.source_lt]
  rw [origin.eval_eq a]
  ring

theorem mapFarkasComb_rhs (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base)) :
    (scomb (resolve (sinitPool base) (mapFarkasComb base cert))).rhs =
      indexedRhs (normalizedLeRows base) cert.comb := by
  rw [scomb_rhs]
  unfold resolve mapFarkasComb
  simp only [List.map_map]
  rw [show indexedRhs (normalizedLeRows base) cert.comb =
      (cert.comb.attach.map fun p =>
        p.val.1 * ((normalizedLeRows base).getD p.val.2 default).rhs).sum by
    unfold indexedRhs
    exact congrArg List.sum
      (List.attach_map_val
        (l := cert.comb)
        (f := fun p => p.1 * ((normalizedLeRows base).getD p.2 default).rhs)).symm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  dsimp only [Function.comp_apply]
  let origin := certificateOrigin base cert p
  change (p.val.1 * origin.sign) *
      (spoolRow (sinitPool base) origin.source).rhs =
    p.val.1 * ((normalizedLeRows base).getD p.val.2 default).rhs
  rw [initial_spoolRow_eq_getD base origin.source_lt]
  rw [origin.rhs_eq]
  ring

theorem farkasCertificate_to_witness (base : List SLe)
    (cert : FarkasCertificate (normalizedLeRows base)) :
    Nonempty (RationalFarkasWitness base) := by
  refine ⟨
    { comb := mapFarkasComb base cert
      referencesPast := mapFarkasComb_referencesPast base cert
      suitable := mapFarkasComb_suitable base cert
      zero := ?_
      negative := ?_ }⟩
  · apply formZeroReal_of_ratEvalZero
    intro a
    rw [mapFarkasComb_eval, cert.zero]
  · rw [mapFarkasComb_rhs]
    exact cert.negative

def RationalFarkasWitness.conclusion {base : List SLe}
    (w : RationalFarkasWitness base) : SLe :=
  ⟨'L', (scomb (resolve (sinitPool base) w.comb)).form,
    (scomb (resolve (sinitPool base) w.comb)).rhs⟩

def RationalFarkasWitness.step {base : List SLe}
    (w : RationalFarkasWitness base) : SStep :=
  ⟨w.conclusion, .lin w.comb⟩

private theorem initial_spoolAsm_eq_empty (base : List SLe) (i : Nat) :
    spoolAsm (sinitPool base) i = ∅ := by
  by_cases hi : i < (sinitPool base).length
  · rw [show spoolAsm (sinitPool base) i =
        ((sinitPool base).getD i sdflt).2 by rfl]
    rw [List.getD_eq_getElem _ _ hi]
    simp [sinitPool]
  · rw [show spoolAsm (sinitPool base) i =
        ((sinitPool base).getD i sdflt).2 by rfl]
    rw [List.getD_eq_default _ _ (by omega)]
    rfl

private theorem witness_assumptions_empty {base : List SLe}
    (w : RationalFarkasWitness base) :
    (sentryOf (sinitPool base) w.step).2 = ∅ := by
  simp only [RationalFarkasWitness.step, sentryOf]
  induction w.comb with
  | nil => rfl
  | cons p ps ih =>
      simp [collectAsms, initial_spoolAsm_eq_empty, ih]

/-- Every exact rational Farkas witness is expressible as a one-step closed VIPR
refutation.  This is the proof-format completeness theorem for LP leaves. -/
theorem farkasWitness_to_vipr {base : List SLe}
    (w : RationalFarkasWitness base) :
    ProofValid [] base [w.step] := by
  let pool := sinitPool base
  let step := w.step
  refine ⟨?_, ?_⟩
  · refine ⟨?_, trivial⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simpa [sinitPool] using w.referencesPast p hp
    · exact Or.inl (Or.inl ⟨w.suitable, w.zero, w.negative⟩)
  · refine ⟨sentryOf pool step, ?_, ?_, ?_⟩
    · simp [sfreplay, pool, step]
    · simpa [pool, step] using witness_assumptions_empty w
    · refine ⟨?_, Or.inl ⟨rfl, w.negative⟩⟩
      change FormZeroReal w.conclusion.form
      simpa [RationalFarkasWitness.conclusion] using w.zero

/-- Exact rational Farkas completeness, isolated as the mathematical existence
theorem needed by the LP fragment. -/
def RationalFarkasComplete : Prop :=
  ∀ base : List SLe,
    RowsWellFormed base →
    SemanticallyInfeasible base [] →
    Nonempty (RationalFarkasWitness base)

def LPFragmentComplete : Prop :=
  ∀ base : List SLe,
    RowsWellFormed base →
    SemanticallyInfeasible base [] →
    HasViprRefutation base []

/-- Rational Farkas completeness, constructed by certificate-carrying
Fourier--Motzkin elimination and mapped back through VIPR row senses. -/
theorem rationalFarkas_complete : RationalFarkasComplete := by
  intro base hrows hinfeasible
  obtain ⟨cert⟩ :=
    rationalFarkas_complete_le (ratInfeasible_normalizedLeRows hrows hinfeasible)
  exact farkasCertificate_to_witness base cert

/-- If exact rational Farkas multipliers exist for every infeasible rational LP,
then the VIPR proof system is complete for its LP fragment. -/
theorem lpFragment_complete_of_farkas
    (hfarkas : RationalFarkasComplete) : LPFragmentComplete := by
  intro base hrows hinfeas
  obtain ⟨w⟩ := hfarkas base hrows hinfeas
  exact ⟨[w.step], farkasWitness_to_vipr w⟩

/-- Unconditional completeness of VIPR's rational LP fragment. -/
theorem lpFragment_complete : LPFragmentComplete :=
  lpFragment_complete_of_farkas rationalFarkas_complete

/-- Conditional soundness-and-completeness characterization for the rational LP
fragment.  The reverse implication is the already verified VIPR soundness
theorem; the forward implication isolates rational Farkas existence as the only
additional mathematical ingredient. -/
theorem lpFragment_sound_iff_hasProof
    (hfarkas : RationalFarkasComplete) (base : List SLe) (hrows : RowsWellFormed base) :
    SemanticallyInfeasible base [] ↔ HasViprRefutation base [] := by
  constructor
  · exact lpFragment_complete_of_farkas hfarkas base hrows
  · rintro ⟨steps, hcert⟩
    exact proofSystem_sound base [] steps hcert

/-- The remaining theorem needed for full MILP completeness: every semantically
infeasible well-formed rational MILP has a finite VIPR derivation.  Keeping this
proposition explicit prevents the external finite-rank result from being mistaken
for something already proved in this development. -/
def FiniteBranchAndCutComplete : Prop := ProofSystemComplete

end LeanVIPR.Completeness.ViprCompleteness
