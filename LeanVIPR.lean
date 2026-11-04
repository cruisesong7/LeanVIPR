module

-- Syntax: the AST and the reader.
public import LeanVIPR.Parser.Ast
public import LeanVIPR.Parser.Number
public import LeanVIPR.Parser.Read

-- Semantics: rows, claims, the declarative proof system, and lowering to it.
public import LeanVIPR.Semantics.LinCon
public import LeanVIPR.Semantics.LinForm
public import LeanVIPR.Semantics.Rows
public import LeanVIPR.Semantics.Claim
public import LeanVIPR.Semantics.Lower

-- The executable checker.
public import LeanVIPR.Checker

-- Theorems: the reader implements its grammars.
public import LeanVIPR.Thm.Tokens
public import LeanVIPR.Thm.Number
public import LeanVIPR.Thm.Parser
public import LeanVIPR.Thm.Valid

-- Theorems: the checker implements the proof system.
public import LeanVIPR.Thm.System
public import LeanVIPR.Thm.Rule.Sound
public import LeanVIPR.Thm.Rule.Complete
public import LeanVIPR.Thm.Checker.Sound
public import LeanVIPR.Thm.Checker.Complete
public import LeanVIPR.Thm.Completeness

@[expose] public section

/-!
# LeanVIPR

A verified checker for VIPR mixed-integer result certificates, in four layers.

| layer | where | what it holds |
|---|---|---|
| syntax | `Parser/` | the AST, and how a `.vipr` file is read into it |
| semantics | `Semantics/` | what a certificate means, and the declarative proof system |
| checker | `Checker.lean` | the array-backed executable checker |
| theorems | `Thm/` | every proof, and the specifications they are stated against |

`Thm/` mirrors the code it is about. Each of its subdirectories holds a `Grammar.lean`
— a specification written without reference to any executable function, which is the
file to read to know what LeanVIPR accepts — alongside the proofs that the code agrees
with it.
-/
