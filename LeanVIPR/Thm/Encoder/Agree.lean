module

public import LeanVIPR.Impl.Encoder.Agree
public import LeanVIPR.Thm.System.RuleSound
public import LeanVIPR.Thm.System.Sound

@[expose] public section

/-!
# The agreement check is sound

Three layers. `relaxesRowsB_sound` refines the `Bool` decision into the declarative
`RelaxesRows`, as elsewhere in this development. `RelaxesRows.transfer` is the content: it
carries a point satisfying one problem into a point satisfying the other, across a
renaming. And because `Mip.Feasible` and `Vipr.Feasible` unfold to the *same* conjunction,
that one lemma serves both directions — `Relaxes.feasible` forwards, which is what makes
an infeasibility claim transport, and `Relaxed.feasible` backwards, which is what makes a
`SOL` point usable. `SameProblem.feasible_iff` states the pair as the equivalence it is.

The whole thing turns on one observation, `evalReal_renameForm`: evaluating a renamed form
in `a` is the same as evaluating the original in `a ∘ σ`. Both sides are the same sum with
the same summands, so it is a `map`-composition identity and nothing more. Everything else
is unfolding.

Note what is *not* assumed anywhere below: `σ` is an arbitrary function, `rows` and `ints`
are arbitrary lists, and `m` need not be `WellFormed`. The strength of the agreement check
comes entirely from the two membership tests, not from any property of the renaming.
-/

namespace LeanVIPR.Mip

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Semantics.System LeanVIPR.Semantics.Rule
open LeanVIPR.Parser LeanVIPR.Impl.Encoder

/-! ## Renaming commutes with evaluation -/

/-- The one computation everything here rests on: evaluating a renamed form is evaluating
the original in the composed valuation. Both sides are the same sum with the same
summands, so it is a `map`-composition identity and nothing more.

Stated on `renameForm`, which is the layer `simp` reaches after unfolding the structure
update in `renameSLe`; a `renameSLe`-phrased version would never fire. -/
@[simp] theorem evalReal_renameForm (σ : Nat → Nat) (f : LinForm) (a : RealValuation) :
    evalReal (renameForm σ f) a = evalReal f (a ∘ σ) := by
  simp [evalReal, renameForm, List.map_map, Function.comp_def]

theorem satReal_renameSLe (σ : Nat → Nat) (c : SLe) (a : RealValuation) :
    satReal (renameSLe σ c) a ↔ satReal c (a ∘ σ) := by
  simp only [satReal, renameSLe, evalReal_renameForm]

/-! ## Transfer -/

/-- **The transfer, stated once.** If `σ` exhibits `(rows₂, ints₂)` as a relaxation of
`(rows₁, ints₁)`, then a point satisfying the first, composed with `σ`, satisfies the
second.

Both pipeline directions are this lemma. Since `Mip.Feasible` and `Vipr.Feasible` unfold
to exactly this conjunction, instantiating with `m` first gives
`m`-feasible ⇒ certificate-feasible, and instantiating with the certificate first gives
the converse. -/
theorem RelaxesRows.transfer {rows₁ rows₂ : List SLe} {ints₁ ints₂ : List Nat}
    {σ : Nat → Nat} (hrel : RelaxesRows rows₁ ints₁ σ rows₂ ints₂)
    {a : RealValuation}
    (haint : ∀ j ∈ ints₁, IsIntReal (a j)) (harow : ∀ c ∈ rows₁, satReal c a) :
    (∀ i ∈ ints₂, IsIntReal ((a ∘ σ) i)) ∧ (∀ c ∈ rows₂, satReal c (a ∘ σ)) := by
  obtain ⟨hints, hrows⟩ := hrel
  refine ⟨fun i hi => haint _ (hints i hi), fun c hc => ?_⟩
  obtain ⟨d, hd, hdom⟩ := hrows c hc
  exact (satReal_renameSLe σ c a).mp (dominates_sound hdom (harow d hd))

/-- A feasible point of `m` is feasible for any problem `m` relaxes to, read through the
renaming. This is the whole content of the agreement check for `RTP infeas`. -/
theorem Relaxes.feasible {m : Mip} {σ : Nat → Nat} {rows : List SLe} {ints : List Nat}
    (hrel : m.Relaxes σ rows ints) {a : RealValuation} (ha : m.Feasible a) :
    (∀ i ∈ ints, IsIntReal ((a ∘ σ) i)) ∧ (∀ c ∈ rows, satReal c (a ∘ σ)) :=
  hrel.transfer ha.1 ha.2

/-- The converse: a point feasible for the certificate's problem, read back through `τ`,
is feasible for `m`. This is what lets a `SOL` entry become a solution of `m`. -/
theorem Relaxed.feasible {m : Mip} {τ : Nat → Nat} {rows : List SLe} {ints : List Nat}
    (hrel : m.Relaxed τ rows ints) {b : RealValuation}
    (hbint : ∀ i ∈ ints, IsIntReal (b i)) (hbrow : ∀ c ∈ rows, satReal c b) :
    m.Feasible (b ∘ τ) :=
  hrel.transfer hbint hbrow

/-! ## Transfer of the objective

The bound a `RTP range` certificate establishes is a bound on *its* objective at *its*
feasible points. Carrying it to `m` needs the two objectives to be the same linear
function once the renaming is undone, which is `ObjAgrees`. -/

/-- The certificate's objective at `a ∘ σ` is our objective at `a`. -/
theorem objectiveReal_comp {m : Mip} {σ : Nat → Nat} {objForm : LinForm}
    (hobj : m.ObjAgrees σ objForm) (a : RealValuation) :
    evalReal objForm (a ∘ σ) = m.objectiveReal a := by
  rw [← evalReal_renameForm σ objForm a]
  exact hobj a

/-! ## The decision procedure refines the predicate -/

theorem objAgreesWith_sound {m : Mip} {v : Vipr} (h : objAgreesWith m v = true) :
    m.ObjAgrees (sigmaFn (recoverSigma m v.varNames)) (Vipr.objectiveForm v) :=
  formEq_sound_real h

theorem objAgreesNegWith_sound {m : Mip} {v : Vipr} (h : objAgreesNegWith m v = true) :
    m.ObjAgreesNeg (sigmaFn (recoverSigma m v.varNames)) (Vipr.objectiveForm v) :=
  formEq_sound_real h

/-- The certificate's objective at `a ∘ σ` is *minus* ours at `a`. -/
theorem objectiveReal_comp_neg {m : Mip} {σ : Nat → Nat} {objForm : LinForm}
    (hobj : m.ObjAgreesNeg σ objForm) (a : RealValuation) :
    evalReal objForm (a ∘ σ) = -m.objectiveReal a := by
  rw [← evalReal_renameForm σ objForm a]
  simpa [Mip.objectiveReal] using hobj a

/-- Stated generically, so the two directions are one proof. -/
theorem relaxesRowsB_sound {rows₁ rows₂ : List SLe} {ints₁ ints₂ : List Nat}
    {σ : Array Nat} (h : relaxesRowsB rows₁ ints₁ σ rows₂ ints₂ = true) :
    RelaxesRows rows₁ ints₁ (sigmaFn σ) rows₂ ints₂ := by
  simp only [relaxesRowsB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  refine ⟨fun i hi => h.1 i (by simpa using hi), fun c hc => ?_⟩
  obtain ⟨d, hd, hdom⟩ := h.2 c (by simpa using hc)
  exact ⟨d, by simpa using hd, domSLe_valid_real hdom⟩

theorem relaxesB_sound {m : Mip} {σ : Array Nat} {rows : List SLe} {ints : List Nat}
    (h : relaxesB m σ rows ints = true) :
    m.Relaxes (sigmaFn σ) rows ints :=
  relaxesRowsB_sound h

theorem relaxedB_sound {m : Mip} {τ : Array Nat} {rows : List SLe} {ints : List Nat}
    (h : relaxedB m τ rows ints = true) :
    m.Relaxed (sigmaFn τ) rows ints :=
  relaxesRowsB_sound h

/-- **The Trestle-style guarantee.** A passing `sameProblemAs` means the certificate's
problem and ours have the same feasible points, each read through its own renaming. -/
theorem sameProblemAs_sound {m : Mip} {v : Vipr} (h : sameProblemAs m v = true) :
    m.SameProblem (sigmaFn (recoverSigma m v.varNames))
      (sigmaFn (recoverTau m v.varNames)) (Lower.conSLes v) v.intVars := by
  simp only [sameProblemAs, Bool.and_eq_true] at h
  exact ⟨relaxesB_sound h.1, relaxedB_sound h.2⟩

/-- The equivalence of feasible sets that `SameProblem` buys, in the shape a reader
expects: `m`-feasible and certificate-feasible correspond in both directions. -/
theorem SameProblem.feasible_iff {m : Mip} {σ τ : Nat → Nat} {rows : List SLe}
    {ints : List Nat} (h : m.SameProblem σ τ rows ints) :
    (∀ a, m.Feasible a →
        (∀ i ∈ ints, IsIntReal ((a ∘ σ) i)) ∧ (∀ c ∈ rows, satReal c (a ∘ σ))) ∧
    (∀ b, (∀ i ∈ ints, IsIntReal (b i)) → (∀ c ∈ rows, satReal c b) →
        m.Feasible (b ∘ τ)) :=
  ⟨fun _ ha => h.1.feasible ha, fun _ hi hr => h.2.feasible hi hr⟩

end LeanVIPR.Mip
