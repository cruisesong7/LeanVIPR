module

public import LeanVIPR.Thm.Checker.Sound
public import LeanVIPR.Thm.Checker.Complete
public import LeanVIPR.Thm.Checker.Parallel

@[expose] public section

/-!
# What is proved about the checker

**This file is the result.** Every theorem a reader of the development should need is
here or named here; the files in `LeanVIPR.Thm.Checker.*` are how they are proved.

```lean
checkVipr v = true ↔ Vipr.ProofValid v        -- the checker decides the proof system
checkVipr v = true → Vipr.ClaimValid v        -- and the system means what it claims
```

The two are different claims and both are needed. `checkVipr_iff_proofValid` is about
the *checker*: the array-backed implementation accepts exactly the certificates the
declarative proof system of `LeanVIPR.Semantics.Claim` admits, so no acceptance is an
artefact of the implementation and no rejection is either. `checkVipr_sound` is about
the *system*: what it admits is mathematically true of the problem, by way of
`proofSystem_sound` in `LeanVIPR.Thm.System.Sound`.

| result | statement | where it is proved |
|---|---|---|
| `checkVipr_iff_proofValid` | the checker decides `ProofValid` exactly | below |
| `checkViprSlice_sound` | a verified slice refutes the original | below |
| `checkVipr_sound` | acceptance implies `ClaimValid` | `Thm.Checker.Sound` |
| `checkVipr_complete` | `ProofValid` implies acceptance | `Thm.Checker.Complete` |
| `checkViprInfeasibleSubset_sound` | infeasibility transports along a row subset | `Thm.Checker.Sound` |

The three proved elsewhere stay there because other theorems in those files consume
them; declaring them here would close an import cycle. The same constraint applies to
`validateVipr_eq_ok_iff` on the reader side — see `LeanVIPR.Thm.Parser`.

What is *not* proved here is that the proof system is complete for mixed-integer
infeasibility — that every infeasible problem has some VIPR certificate. That is a
statement about the format rather than about this checker, it is open, and
`LeanVIPR.Thm.System.Completeness` records what it would take.
-/

namespace LeanVIPR.Checker

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.Lower
open LeanVIPR.Parser.Vipr LeanVIPR.Semantics.System

/-- **The checker decides the declarative VIPR proof system exactly.** -/
theorem checkVipr_iff_proofValid (v : Vipr) : checkVipr v = true ↔ Vipr.ProofValid v :=
  ⟨checkVipr_refines, checkVipr_complete⟩

theorem checkViprSlice_sound (original sliced : Vipr)
    (h : checkViprSlice original sliced = true) :
    ∀ a, Feasible original a → False := by
  simp only [checkViprSlice, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hinfeas, hint⟩, hsub⟩, hcheck⟩ := h
  exact checkViprInfeasibleSubset_sound original sliced hinfeas hint
    (fun c hc => (List.isSublist_iff_sublist.mp hsub).subset hc) hcheck

end LeanVIPR.Checker
