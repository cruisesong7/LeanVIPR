module

public import LeanVIPR.Ast.Types

@[expose] public section

/-!
# When a parsed certificate describes a usable problem

**This file is the review surface for validation.** It says which certificates are
well formed beyond their syntax, and nothing else: no proofs, and no reference to how
the checks are implemented. `LeanVIPR.Thm.Valid` proves `validateVipr` decides exactly
this, so a reader who accepts these definitions need not read the validator.

This is deliberately separate from the grammar. `LeanVIPR.Thm.Vipr.Grammar` says what a
certificate *is*; these conditions say whether what it denotes is a problem the checker
can replay — every index names a declared variable, no sparse vector mentions a variable
twice, and no derivation uses a constraint the format already allowed a verifier to
discard. Nothing here is required for soundness; the first two keep the denotation
single-valued, and the last is conformance with the specification's `DER` rule.

`reasonRefs`, `reasonMultipliers`, `finalUseHint` and `usedAfterFinal` live in
`LeanVIPR.Ast.Types` because they state what the AST's index fields *mean* — which
constraints a reason cites, and what a `DER` row's trailing field declares. They are
part of the format, used by this specification and by the validator alike, in the same
way `digitsValue` is shared by the number grammar and the number reader.
-/

namespace LeanVIPR.Ast

open LeanVIPR.Cert

/-- A sparse vector's indices name declared variables, and none is repeated.

Duplicates are rejected rather than resolved: they have no agreed meaning, since the
reference checker keeps the last value while summing them is equally natural. -/
def IndicesOk (nvar : Nat) (idxs : List Nat) : Prop :=
  (∀ i ∈ idxs, i < nvar) ∧ idxs.Nodup

/-- A solution vector names declared variables and assigns each at most one value. A
repeated index is allowed when the values agree, since then the vector still denotes
one point. -/
def SolutionOk (nvar : Nat) (vals : List (Nat × ℚ)) : Prop :=
  (∀ p ∈ vals, p.1 < nvar) ∧ ∀ p ∈ vals, ∀ q ∈ vals, p.1 = q.1 → p.2 = q.2

/-- No derivation cites a constraint past that constraint's declared final use. The
position of a derivation in the `DER` list is its constraint index, offset by the number
of `CON` rows, which is why the rule is stated over a split of the list. -/
def FinalUseOk (v : Vipr) : Prop :=
  ∀ before d after, v.ders.toList = before ++ d :: after →
    ∀ k ∈ reasonRefs d.reason, ¬ usedAfterFinal v (v.cons.size + before.length) k

/-- `IsValid v`: every sparse vector that contributes to the claimed problem or to a
stated derived row is well formed, and the final-use rule holds. -/
def IsValid (v : Vipr) : Prop :=
  (∀ i ∈ v.intVars, i < v.varNames.size) ∧
  IndicesOk v.varNames.size (v.objTerms.map Prod.fst) ∧
  (∀ c ∈ v.cons.toList, IndicesOk v.varNames.size (c.form.map (·.idx))) ∧
  (∀ s ∈ v.sols.toList, SolutionOk v.varNames.size s.2) ∧
  (∀ d ∈ v.ders.toList,
    IndicesOk v.varNames.size (d.form.map (·.idx)) ∧
      (reasonMultipliers d.reason).Nodup) ∧
  FinalUseOk v

end LeanVIPR.Ast
