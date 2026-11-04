module

public import LeanVIPR.Spec
public import LeanVIPR.Impl
public import LeanVIPR.Thm

@[expose] public section

/-!
# LeanVIPR

A verified checker for VIPR mixed-integer result certificates, in three parts.

| | |
|---|---|
| `Spec/` | what a certificate is and what it claims — **the part to read** |
| `Impl/` | the reader and the checker: the executable artifacts |
| `Thm/` | the proofs that `Impl` meets `Spec` |

Nothing in `Spec/` mentions an executable function, and nothing in `Impl/` is trusted.
That division is the point of the development: `LeanVIPR.Thm.Parser` and
`LeanVIPR.Thm.Checker` state their results with `Spec` on one side and `Impl` on the
other, so neither can be satisfied by an implementation that merely agrees with itself.

Each directory has a header file — `LeanVIPR.Spec`, `LeanVIPR.Impl`, `LeanVIPR.Thm` —
which says what is in it and what to read first.
-/
