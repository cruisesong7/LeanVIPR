module

public import LeanVIPR.Thm.Encoder.Agree
public import LeanVIPR.Thm.Encoder.Emit
public import LeanVIPR.Thm.Encoder.Pipeline

@[expose] public section

/-!
# The encoder's theorems

`Thm.Encoder.Agree` proves the agreement check sound: a passing check transports an
`m`-feasible point into a point feasible for the problem the certificate carries.
`Thm.Encoder.Pipeline` composes that with checker soundness to reach `Mip.Infeasible` —
a statement about the problem written in Lean rather than about the certificate's own.
-/
