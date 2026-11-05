module

public import LeanVIPR.Thm.Parser
public import LeanVIPR.Thm.System
public import LeanVIPR.Thm.System.Claim
public import LeanVIPR.Thm.System.Completeness
public import LeanVIPR.Thm.Checker

@[expose] public section

/-!
# The proofs

That `LeanVIPR.Impl` meets `LeanVIPR.Spec`. Three files are the results, one per layer,
and each sits beside the directory that proves it:

| file | result |
|---|---|
| `Thm.Parser` | the reader accepts exactly the files the grammar derives, and returns the certificate it assigns |
| `Thm.System` | a derivation the rulebook admits really does refute the problem |
| `Thm.Checker` | the checker accepts exactly the derivations the rulebook admits |

`Thm.System.Claim`, `Thm.System.LinForm` and `Thm.System.Row` are infrastructure those
rest on; they are grouped with `System` because they are about the semantics layer.

Each result comes in both directions, and the two do different jobs. Soundness is what
makes an `ACCEPT` mean something about the problem. Completeness is what makes a
rejection mean something about the file, rather than possibly being an artefact of a
narrow reader or a conservative check.

An index cannot generally restate its own layer's headline: almost every top-level
result is consumed by the layer above, so declaring it in the index would close an
import cycle. Each index therefore holds what it can and names where the rest is proved.
-/
