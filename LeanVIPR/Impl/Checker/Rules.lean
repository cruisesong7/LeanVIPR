module

public import LeanVIPR.Spec.Semantics.Row
public import LeanVIPR.Impl.Checker.Form

@[expose] public section

/-!
# Executable rule checks

The `Bool`-valued side-condition checks the checker runs for each VIPR rule: suitability
of a combination, integrality for `rnd`, absurdity, domination, and the complementary
bounds of `uns`. Each is proved to imply the corresponding declarative rule of
`LeanVIPR.Spec.Semantics.System` in `LeanVIPR.Thm.System.RuleSound`, and to be implied by it in
`LeanVIPR.Thm.System.RuleComplete` — so the checker neither admits a derivation the
rulebook forbids nor loses one it permits.
-/

namespace LeanVIPR.Semantics


/-- Decidable "the two forms are equal as functions" (their difference is identically 0). -/
def formEq (f g : LinForm) : Bool := formIsZero (f ++ sNegForm g)

/-! ## Per-reason checks and soundness -/

/-- Decidable suitability for a `≤`-deriving combination. -/
def suitLe (cs : List (ℚ × SLe)) : Bool := cs.all (fun p => decide (p.1 * senseSign p.2.sense ≤ 0))

/-- Decidable suitability for a `≥`-deriving combination. -/
def suitGe (cs : List (ℚ × SLe)) : Bool := cs.all (fun p => decide (0 ≤ p.1 * senseSign p.2.sense))

/-- One normalized coefficient is integral on an integer variable, or vanishes. -/
def intEntry (intVars : List Nat) (p : Nat × ℚ) : Bool :=
  p.2 == 0 || (isIntVal p.2 && decide (p.1 ∈ intVars))

/-- The form is integer-valued: after summing duplicate indices, every nonzero
coefficient is an integer on an integer variable. Normalizing first accepts
combinations whose fractional or continuous-variable terms cancel. -/
def formInt (intVars : List Nat) (f : LinForm) : Bool :=
  (normForm f).all (intEntry intVars)

def alIsZero (al : List (Nat × ℚ)) : Bool := al.all (fun p => p.2 == 0)

def alInt (intVars : List Nat) (al : List (Nat × ℚ)) : Bool := al.all (intEntry intVars)

/-- The combination is itself an absurdity (identically-zero form, rhs contradicting a
valid sense) — which, per the VIPR spec, dominates *any* stated constraint. -/
def linAbsurd (cs : List (ℚ × SLe)) (combined : Le) (normalized : List (Nat × ℚ)) : Bool :=
  (suitLe cs && alIsZero normalized && decide (combined.rhs < 0)) ||
  (suitGe cs && alIsZero normalized && decide (0 < combined.rhs))

/-- **`lin` step check.** Accepts either normal rhs-domination or an absurd combination.

Domination is tested first, and the absurdity test second, because `||` short-circuits
and each test needs a *different* form normalized: domination needs the combination minus
the stated row, absurdity needs the combination alone. Testing absurdity first would
normalize both on every step; this way a step that dominates normally — all but a
handful in any real certificate — normalizes once. The order does not change the result,
only which normalizations are forced. -/
def linCheck (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  let combined := scomb cs
  (formEq combined.form stated.form &&
    (if stated.sense = 'L' then suitLe cs && decide (combined.rhs ≤ stated.rhs)
     else if stated.sense = 'G' then suitGe cs && decide (stated.rhs ≤ combined.rhs)
     else if stated.sense = 'E' then
       suitLe cs && suitGe cs && decide (combined.rhs = stated.rhs)
     else false)) ||
  linAbsurd cs combined (normForm combined.form)

/-- **`rnd` step check.** -/
def rndCheck (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  let combined := scomb cs
  let normalized := normForm combined.form
  formEq combined.form stated.form && alInt intVars normalized &&
  (if stated.sense = 'L' then
      suitLe cs && decide (((⌊combined.rhs⌋ : ℤ) : ℚ) ≤ stated.rhs)
   else if stated.sense = 'G' then
      suitGe cs && decide (stated.rhs ≤ ((⌈combined.rhs⌉ : ℤ) : ℚ))
   else false)

/-! ## Domination and complementary integer bounds (for `uns` case-splits) -/

/-- An absurdity (identically-zero form, rhs contradicting the sense). -/
def isAbsurd (c : SLe) : Bool :=
  formIsZero c.form &&
  (if c.sense = 'L' then decide (c.rhs < 0)
   else if c.sense = 'G' then decide (0 < c.rhs)
   else if c.sense = 'E' then decide (c.rhs ≠ 0)
   else false)

/-- `c` dominates `d`: either `c` is an absurdity (which, per the VIPR spec, dominates
any constraint), or the forms are equal as functions and the right-hand side is at least
as strong for `d`'s sense (an `=`-row dominates either inequality direction). -/
def domSLe (c d : SLe) : Bool :=
  isAbsurd c ||
  (formEq c.form d.form &&
   (if d.sense = 'L' then ((c.sense == 'L') || (c.sense == 'E')) && decide (c.rhs ≤ d.rhs)
    else if d.sense = 'G' then ((c.sense == 'G') || (c.sense == 'E')) && decide (d.rhs ≤ c.rhs)
    else if d.sense = 'E' then (c.sense == 'E') && decide (c.rhs = d.rhs)
    else false))

/-- `b1`,`b2` are complementary integer bounds `f ≤ β` / `f ≥ β+1` (in either order):
same form as functions, integer-valued form over `intVars`, integer `β`. -/
def unsBounds (intVars : List Nat) (b1 b2 : SLe) : Bool :=
  ((b1.sense == 'L') && (b2.sense == 'G') && formEq b1.form b2.form
    && formInt intVars b1.form && isIntVal b1.rhs && decide (b2.rhs = b1.rhs + 1))
  ||
  ((b1.sense == 'G') && (b2.sense == 'L') && formEq b1.form b2.form
    && formInt intVars b2.form && isIntVal b2.rhs && decide (b1.rhs = b2.rhs + 1))

end LeanVIPR.Semantics
