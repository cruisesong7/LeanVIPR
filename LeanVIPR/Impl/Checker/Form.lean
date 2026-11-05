module

public import LeanVIPR.Spec.Semantics.LinForm

@[expose] public section

/-!
# Executable tests on linear forms

The `Bool`-valued decisions behind the declarative notions of
`LeanVIPR.Spec.Semantics.LinForm`. Each is proved to agree with the notion it decides in
`LeanVIPR.Thm.System.LinForm`.
-/

namespace LeanVIPR.Semantics

open Classical


/-- Decidable "is an integer" for `ℚ`. -/
def isIntValB (q : ℚ) : Bool := q.den == 1

/-- A linear form is identically zero if all its normalized coefficients vanish. -/
def formIsZero (f : LinForm) : Bool := (normForm f).all (fun p => p.2 == 0)

end LeanVIPR.Semantics
