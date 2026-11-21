module

public import LeanVIPR.Spec.Syntax
public import LeanVIPR.Spec.Semantics
public import LeanVIPR.Spec.Mip

@[expose] public section

/-!
# The specification

**This is what to read.** Everything LeanVIPR claims is stated here, and nothing here
refers to an executable function: no reader, no checker, no `Bool`, no `Except`. Accept
these definitions and you know what `viprcheck` means when it prints `ACCEPT`, without
reading a line of `LeanVIPR.Impl`.

| file | says |
|---|---|
| `Spec.Syntax` | which files are certificates, and which certificate each one denotes |
| `Spec.Semantics` | what a certificate means, which derivations are admitted, and what a valid one claims |
| `Spec.Mip` | what a mixed-integer program is, written in Lean rather than in a file |

Three of these are worth dwelling on.

`Spec.Syntax.Grammar` is why the reader is not trusted. A correctness statement phrased in
terms of the tokenizer's own output would take that output as the definition of
tokenization and could not detect a tokenizer that dropped or merged tokens; stated
against this file, it can. `LeanVIPR.Thm.Parser` closes that loop in both directions.

`Spec.Semantics.Lower` contains a search, which may look out of place in a specification. It is
not: VIPR v1.1's `lin weak` rows omit their variable-bound multipliers, so the meaning
of such a row is only defined up to completing it. The search is part of what the
format says a certificate denotes. Its untrustedness is handled by rechecking the
completed combination with the verified `lin` rule, not by hiding it here.

`Spec.Mip` is about a program, not about a certificate, and it is what lets a result
be stated about the problem we asked rather than about the problem the solver wrote down
for itself. `LeanVIPR.Thm.Encoder` connects the two.
-/
