module

public import LeanVIPR.Thm.System.Sound
public import LeanVIPR.Thm.System.RuleSound
public import LeanVIPR.Thm.System.RuleComplete
public import LeanVIPR.Thm.System.LinForm
public import LeanVIPR.Thm.System.Row

@[expose] public section

/-!
# What is proved about the proof system

**This file is the result for the middle layer**, between `LeanVIPR.Thm.Parser` (the
reader) and `LeanVIPR.Thm.Checker` (the checker). It names what is proved and where;
the files in `LeanVIPR.Thm.System.*` are how.

The layer answers two questions that are easy to conflate. *Is the rulebook valid?* —
a derivation admitted by the declarative VIPR rules really does refute the problem.
*Do the executable rule checks implement the rulebook?* — the Boolean side-condition
checks the checker runs accept exactly the rule applications the rulebook permits.
Checker correctness needs both: without the first, the checker decides a rulebook that
proves nothing; without the second, it decides a different rulebook than the one proved
sound.

| result | statement | where it is proved |
|---|---|---|
| `proofSystem_sound` | a valid derivation refutes the problem over ℝ, with the integer variables integral | below |
| `replay_sound` | every row a replay puts in the pool holds at any such valuation | `Thm.System.Sound` |
| `linCheck_valid_real`, `rndCheck_valid_real`, `absurdB_sound_real`, `domSLe_valid_real`, `unsBoundsB_valid_real` | each executable rule check implies its declarative rule | `Thm.System.RuleSound` |
| `linCheck_complete`, `rndCheck_complete`, `absurdB_complete`, `domSLe_complete`, `unsBoundsB_complete` | and is implied by it, so the checks lose no derivations | `Thm.System.RuleComplete` |
| `farkasWitness_to_vipr`, `lpFragment_complete_of_farkas`, `lpFragment_sound_iff_hasProof` | the LP fragment is complete given rational Farkas | `Thm.System.Completeness` |

Only the headline is here; the rest stays where it is proved because a later layer
consumes it — the claim semantics rests on `replay_sound`, and the rule lemmas on each
other — so declaring those here would close an import cycle. The same constraint shapes
`LeanVIPR.Thm.Parser` and `LeanVIPR.Thm.Checker`; it is a consequence of the layering,
not an accident of where things were written. For the same reason
`Thm.System.Completeness` imports *this* file rather than the other way round: LP-fragment
completeness is stated against the soundness result below.

Open, and deliberately not assumed: that the proof system is *complete* for
mixed-integer infeasibility — that every infeasible problem admits some finite VIPR
certificate. `Thm.System.Completeness` reduces this to two separate mathematical
ingredients, proves the compilation step for the LP fragment, and names the
branch-and-cut existence theorem rather than quietly taking it for granted.
-/

namespace LeanVIPR.Semantics.System

/-- **VIPR proof-system soundness over real continuous valuations.**

This theorem is independent of the executable checker.  It formalizes:

`declaratively valid closed VIPR refutation → real/integer MILP infeasible`.
-/
theorem proofSystem_sound (base : List SLe) (intVars : List Nat) (steps : List SStep)
    (hvalid : ProofValid intVars base steps) :
    ∀ a : RealValuation,
      (∀ j ∈ intVars, IsIntReal (a j)) →
      (∀ c ∈ base, satReal c a) →
      False := by
  intro a hint hbase
  obtain ⟨hder, e, hlast, hclosed, habs⟩ := hvalid
  have hall := replay_sound base intVars a hint (sinitPool base) steps hder
    (initialPool_holds base a)
  have he : EntryHolds base a e := hall e (List.mem_of_getLast? hlast)
  have hsat : satReal e.1 a := he hbase (by simp [hclosed])
  exact absurd_unsat habs a hsat

end LeanVIPR.Semantics.System
