module

-- Syntax: the AST, the numeric readers, and the reader itself.
public import LeanVIPR.Parser.Ast
public import LeanVIPR.Parser.Number
public import LeanVIPR.Parser

-- Semantics: rows, claims, the declarative proof system, and lowering to it.
public import LeanVIPR.Semantics.LinCon
public import LeanVIPR.Semantics.LinForm
public import LeanVIPR.Semantics.Rows
public import LeanVIPR.Semantics.Claim
public import LeanVIPR.Semantics.Lower

-- The executable checker.
public import LeanVIPR.Checker

-- Theorems: the reader implements its grammar.
public import LeanVIPR.Thm.Parser

-- Theorems: the declarative proof system is sound, and its rule checks refine it.
public import LeanVIPR.Thm.System
public import LeanVIPR.Thm.System.Completeness

-- Theorems: the executable checker implements the proof system.
public import LeanVIPR.Thm.Checker

@[expose] public section

/-!
# LeanVIPR

A verified checker for VIPR mixed-integer result certificates, in four layers.

| layer | where | what it holds |
|---|---|---|
| syntax | `Parser.lean`, `Parser/` | how a `.vipr` file is read into the AST |
| semantics | `Semantics/` | what a certificate means, and the declarative proof system |
| checker | `Checker.lean` | the array-backed executable checker |
| theorems | `Thm/` | every proof, and the specification they are stated against |

`Parser.lean` and `Checker.lean` are the two ends of the pipeline and sit side by side;
`Parser/` holds the AST the reader produces and the numeric readers it uses.

`Thm/` has one directory per layer:

* `Thm/Parser.lean` — **the reader's results**: soundness, completeness, and the `iff`.
  Read this one. `Thm/Parser/Grammar.lean` is the specification they are stated against,
  the one other file worth reading; the rest of `Thm/Parser/` is how they are proved.
* `Thm/System.lean` — **the proof system's results**: the declarative rules are valid,
  and the executable rule checks implement them exactly. `Thm/System/` is the proofs.
* `Thm/Checker.lean` — **the checker's results**: it decides the proof system exactly,
  and what the system admits is true. `Thm/Checker/` is how that is proved.
-/
