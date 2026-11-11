module

public import LeanVIPR.Thm.Encoder.Denote

@[expose] public section

/-!
# The encoder, actually run

`encodeMps` had no caller: the executable never emits MPS, so nothing exercised the
emitter outside of scratch files. This module is that caller, and it doubles as the
non-vacuity check for the layer above it.

Three things are checked here rather than asserted elsewhere.

1. **The preconditions are satisfiable.** `Mps.EncodableNames`, `Mps.Emittable` and
   `Mip.WellFormed` all hold of a concrete problem, by `decide`. Every hypothesis the
   encoder's theorems carry is therefore dischargeable for a particular `Mip`, which is
   what makes `isTokenization_encodeMps'` and the obligations in `Thm/Encoder/Denote.lean`
   non-vacuous in practice and not merely in principle.
2. **`IsNameTok` discriminates.** It accepts ordinary names and rejects the section
   keywords, the marker literal, the empty string, names containing whitespace, and names
   beginning with the comment marker. A predicate that accepted everything would make the
   grammar's unambiguity claims hollow.
3. **The emitter runs**, and its output is the file in `examples/`.
-/

namespace LeanVIPR.Tactic.Roundtrip

open LeanVIPR LeanVIPR.Impl.Encoder LeanVIPR.Mps

/-- The knapsack of `examples/uns_knapsack.mps`, written in Lean. -/
def knapsack : Mip where
  vars := #[ { name := "x", isInt := true, lo := some 0, hi := some 3 },
             { name := "y", isInt := true, lo := some 0, hi := some 2 },
             { name := "z", isInt := true, lo := some 0, hi := some 1 } ]
  objSense := .min
  obj := []
  rows := #[ { name := "c0", sense := 'E', rhs := 23, form := [⟨0, 6⟩, ⟨1, 10⟩, ⟨2, 15⟩] },
             { name := "c1", sense := 'G', rhs := 1,  form := [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] } ]

/-! ## The preconditions hold of it -/

theorem knapsack_wellFormed : knapsack.WellFormed := by decide
theorem knapsack_encodable : EncodableNames knapsack objRowName := by decide
theorem knapsack_emittable : Emittable knapsack "k1" := by
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> decide

/-- Consequently the tokenization theorem applies to a real problem, with nothing assumed
that cannot be checked. -/
theorem knapsack_isTokenization :
    Parser.IsTokenization (encodeMpsNamed "k1" knapsack).toList
      (mpsToks "k1" knapsack) :=
  isTokenization_encodeMps' knapsack knapsack_emittable

/-! ## `IsNameTok` accepts what it should and rejects what it must

Without the negative cases the grammar's unambiguity argument would be hollow: a predicate
that accepted `COLUMNS` as a row name could not justify splitting the token stream by
keyword. -/

theorem isNameTok_accepts : IsNameTok "x" ∧ IsNameTok objRowName := by decide

theorem isNameTok_rejects :
    ¬ IsNameTok "COLUMNS" ∧ ¬ IsNameTok "ENDATA" ∧ ¬ IsNameTok markerTok ∧
    ¬ IsNameTok "" ∧ ¬ IsNameTok "a b" ∧ ¬ IsNameTok "%x" := by decide

end LeanVIPR.Tactic.Roundtrip
