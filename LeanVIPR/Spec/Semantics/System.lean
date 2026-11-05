module

public import LeanVIPR.Spec.Semantics.Row
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# The declarative VIPR proof system

**This is the rulebook.** It says which derivations the VIPR proof system admits, over
real-valued valuations with the stated variables integral, and nothing else: no
executable check, no array, no `Bool`. `LeanVIPR.Thm.System` proves that a derivation it
admits really does refute the problem, and `LeanVIPR.Thm.Checker` proves the executable
checker accepts exactly these derivations.

Everything is stated over `RealValuation = Nat -> R` rather than over the rationals the
certificate is written in. That is deliberate: a certificate with rational coefficients
must refute the problem over the reals, since that is the problem a solver claims to
have solved. The rational arithmetic is an implementation detail of the checker, not of
the claim.
-/

namespace LeanVIPR.Semantics.System

open LeanVIPR.Semantics


/-! ## Real semantics for rational VIPR rows -/

/-- A valuation of the MILP variables over the reals. -/
abbrev RealValuation := Nat → ℝ

/-- Evaluate a rational sparse linear form in a real valuation. -/
def evalReal (f : LinForm) (a : RealValuation) : ℝ :=
  (f.map (fun t => (t.coeff : ℝ) * a t.idx)).sum

/-- Satisfaction of a rational sensed row by a real valuation. -/
def satReal (c : SLe) (a : RealValuation) : Prop :=
  if c.sense = 'L' then evalReal c.form a ≤ (c.rhs : ℝ)
  else if c.sense = 'G' then (c.rhs : ℝ) ≤ evalReal c.form a
  else if c.sense = 'E' then evalReal c.form a = (c.rhs : ℝ)
  else False

/-- A real value is integral when it is the cast of an integer. -/
def IsIntReal (x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ)

/-- Two rational forms denote the same real linear function. -/
def FormEqReal (f g : LinForm) : Prop := ∀ a, evalReal f a = evalReal g a

/-- A rational form denotes the zero real linear function. -/
def FormZeroReal (f : LinForm) : Prop := ∀ a, evalReal f a = 0

/-- A form is integer-valued whenever all declared integer variables are integral. -/
def FormIntegralReal (intVars : List Nat) (f : LinForm) : Prop :=
  ∀ a, (∀ j ∈ intVars, IsIntReal (a j)) → IsIntReal (evalReal f a)

/-! ## Suitable combinations and the `lin` rule -/

def senseSignReal (s : Char) : ℝ :=
  if s = 'L' then -1 else if s = 'G' then 1 else 0

def SuitableLe (cs : List (ℚ × SLe)) : Prop :=
  ∀ p ∈ cs, (p.1 : ℝ) * senseSignReal p.2.sense ≤ 0

def SuitableGe (cs : List (ℚ × SLe)) : Prop :=
  ∀ p ∈ cs, 0 ≤ (p.1 : ℝ) * senseSignReal p.2.sense

/-- A suitable combination that is already contradictory. -/
def LinAbsurd (cs : List (ℚ × SLe)) : Prop :=
  (SuitableLe cs ∧ FormZeroReal (scomb cs).form ∧ (scomb cs).rhs < 0) ∨
  (SuitableGe cs ∧ FormZeroReal (scomb cs).form ∧ 0 < (scomb cs).rhs)

/-- Declarative validity of a VIPR `lin` step. A combination whose multipliers all
lie on equality rows (`λⱼ·s(Cⱼ) = 0`, i.e. suitable in both directions) derives an
equality, which dominates an equality with the same right-hand side. -/
def LinValid (stated : SLe) (cs : List (ℚ × SLe)) : Prop :=
  LinAbsurd cs ∨
  (FormEqReal (scomb cs).form stated.form ∧
    ((stated.sense = 'L' ∧ SuitableLe cs ∧ (scomb cs).rhs ≤ stated.rhs) ∨
     (stated.sense = 'G' ∧ SuitableGe cs ∧ stated.rhs ≤ (scomb cs).rhs) ∨
     (stated.sense = 'E' ∧ SuitableLe cs ∧ SuitableGe cs ∧
       (scomb cs).rhs = stated.rhs)))

/-- Declarative validity of a VIPR `rnd` step. -/
def RndValid (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) : Prop :=
  FormEqReal (scomb cs).form stated.form ∧
  FormIntegralReal intVars (scomb cs).form ∧
  ((stated.sense = 'L' ∧ SuitableLe cs ∧
      ((⌊(scomb cs).rhs⌋ : ℤ) : ℚ) ≤ stated.rhs) ∨
   (stated.sense = 'G' ∧ SuitableGe cs ∧
      stated.rhs ≤ ((⌈(scomb cs).rhs⌉ : ℤ) : ℚ)))

/-! ## Domination, absurdities, and `uns` -/

/-- A sensed row is an absurdity over the reals. -/
def Absurd (c : SLe) : Prop :=
  FormZeroReal c.form ∧
  ((c.sense = 'L' ∧ c.rhs < 0) ∨
   (c.sense = 'G' ∧ 0 < c.rhs) ∨
   (c.sense = 'E' ∧ c.rhs ≠ 0))

/-- Declarative VIPR domination. -/
def Dominates (c d : SLe) : Prop :=
  Absurd c ∨
  (FormEqReal c.form d.form ∧
    ((d.sense = 'L' ∧ (c.sense = 'L' ∨ c.sense = 'E') ∧ c.rhs ≤ d.rhs) ∨
     (d.sense = 'G' ∧ (c.sense = 'G' ∨ c.sense = 'E') ∧ d.rhs ≤ c.rhs) ∨
     (d.sense = 'E' ∧ c.sense = 'E' ∧ c.rhs = d.rhs)))

/-- Complementary integer bounds `f ≤ β` and `f ≥ β+1`, in either order. -/
def ComplementaryBounds (intVars : List Nat) (b1 b2 : SLe) : Prop :=
  (b1.sense = 'L' ∧ b2.sense = 'G' ∧ FormEqReal b1.form b2.form ∧
    FormIntegralReal intVars b1.form ∧ IsIntVal b1.rhs ∧ b2.rhs = b1.rhs + 1) ∨
  (b1.sense = 'G' ∧ b2.sense = 'L' ∧ FormEqReal b1.form b2.form ∧
    FormIntegralReal intVars b2.form ∧ IsIntVal b2.rhs ∧ b1.rhs = b2.rhs + 1)

/-! ## Declarative derivations -/

/-- All references of a reason point to the current pool. -/
def ReferencesPast (pool : SPool) : SReason → Prop
  | .asm => True
  | .lin comb => ∀ p ∈ comb, p.2 < pool.length
  | .rnd comb => ∀ p ∈ comb, p.2 < pool.length
  | .uns i1 l1 i2 l2 =>
      i1 < pool.length ∧ l1 < pool.length ∧ i2 < pool.length ∧ l2 < pool.length
  | .sol => True

/-- Declarative validity of one VIPR derivation step. -/
def StepValid (intVars : List Nat) (pool : SPool) (s : SStep) : Prop :=
  ReferencesPast pool s.reason ∧
  match s.reason with
  | .asm => True
  | .lin comb => LinValid s.stated (resolve pool comb)
  | .rnd comb => RndValid intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      Dominates (spoolRow pool i1) s.stated ∧
      Dominates (spoolRow pool i2) s.stated ∧
      ComplementaryBounds intVars (spoolRow pool l1) (spoolRow pool l2) ∧
      spoolRow pool l1 ∈ spoolAsm pool i1 ∧
      spoolRow pool l2 ∈ spoolAsm pool i2
  | .sol => False

/-- Declarative validity of a threaded derivation list. -/
def DerivationValid (intVars : List Nat) (pool : SPool) : List SStep → Prop
  | [] => True
  | s :: ss =>
      StepValid intVars pool s ∧
      DerivationValid intVars (pool ++ [sentryOf pool s]) ss

/-- A declaratively valid infeasibility certificate ends in a closed absurdity. -/
def ProofValid (intVars : List Nat) (base : List SLe) (steps : List SStep) : Prop :=
  DerivationValid intVars (sinitPool base) steps ∧
  ∃ e, (sfreplay (sinitPool base) steps).getLast? = some e ∧ e.2 = ∅ ∧ Absurd e.1

/-- Semantic invariant for one replay-pool entry. -/
def EntryHolds (base : List SLe) (a : RealValuation) (e : SLe × SAsm) : Prop :=
  (∀ c ∈ base, satReal c a) → (∀ s ∈ e.2, satReal s a) → satReal e.1 a

end LeanVIPR.Semantics.System
