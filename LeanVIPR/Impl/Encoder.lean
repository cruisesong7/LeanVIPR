module

public import LeanVIPR.Impl.Encoder.Mps
public import LeanVIPR.Impl.Encoder.Agree

@[expose] public section

/-!
# The encoder

The direction that poses the question. `Impl.Encoder.Mps` turns a `Mip` into the MPS file
exact SCIP reads; `Impl.Encoder.Agree` decides whether a returned certificate is about
that same problem, in either or both directions.

Neither is trusted. The agreement check is what makes the pipeline sound and is proved in
`LeanVIPR.Thm.Encoder.Agree`; the emitter is what makes it useful, and is proved against
the MPS grammar in `LeanVIPR.Thm.Encoder.Emit`.
-/
