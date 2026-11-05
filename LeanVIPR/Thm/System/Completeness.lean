module

public import LeanVIPR.Spec.Semantics.Completeness
public import LeanVIPR.Thm.System

@[expose] public section

/-!
# What is proved towards completeness

The statements are in `LeanVIPR.Spec.Semantics.Completeness`; this file proves the one ingredient
that is provable here. Every exact rational Farkas witness compiles to a one-step closed
VIPR refutation, so any rational Farkas completeness theorem immediately yields
completeness of the VIPR LP fragment. The finite mixed-integer branch-and-cut existence
theorem remains open and is named, not assumed.
-/

namespace LeanVIPR.Semantics.Completeness

open LeanVIPR.Semantics LeanVIPR.Semantics.System

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

/-- If exact rational Farkas multipliers exist for every infeasible rational LP,
then the VIPR proof system is complete for its LP fragment. -/
theorem lpFragment_complete_of_farkas
    (hfarkas : RationalFarkasComplete) : LPFragmentComplete := by
  intro base hinfeas
  obtain ⟨w⟩ := hfarkas base hinfeas
  exact ⟨[w.step], farkasWitness_to_vipr w⟩

/-- Conditional soundness-and-completeness characterization for the rational LP
fragment.  The reverse implication is the already verified VIPR soundness
theorem; the forward implication isolates rational Farkas existence as the only
additional mathematical ingredient. -/
theorem lpFragment_sound_iff_hasProof
    (hfarkas : RationalFarkasComplete) (base : List SLe) :
    SemanticallyInfeasible base [] ↔ HasViprRefutation base [] := by
  constructor
  · exact lpFragment_complete_of_farkas hfarkas base
  · rintro ⟨steps, hcert⟩
    exact proofSystem_sound base [] steps hcert

end LeanVIPR.Semantics.Completeness
