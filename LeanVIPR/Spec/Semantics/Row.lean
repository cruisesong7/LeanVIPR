module

public import LeanVIPR.Spec.Semantics.LinForm
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Sensed rows, pools, and derivation steps

**The vocabulary the proof system is written in.** A real solver certificate uses VIPR's
*suitable linear combination*: signed multipliers over rows that each carry a sense
(`E`, `L`, `G`), rather than a fixed inequality direction. A sensed row `SLe` keeps that
sense, so an equality row stays one row instead of two, and pool indices then match the
certificate's own indices.

Definitions only. The executable checks that decide these notions are in
`LeanVIPR.Impl.Checker.Rules`; what the rules *mean* is `LeanVIPR.Spec.Semantics.System`.
-/

namespace LeanVIPR.Semantics


/-- A sensed linear constraint `form  sense  rhs`, sense ∈ {`'L'` (≤), `'G'` (≥),
`'E'` (=)}. -/
structure SLe where
  sense : Char
  form : LinForm
  rhs : ℚ
deriving Inhabited, DecidableEq

/-- VIPR sign `s(C)`: `-1` for `≤`, `+1` for `≥`, `0` for `=`. -/
def senseSign (s : Char) : ℚ :=
  if s = 'L' then -1 else if s = 'G' then 1 else 0

/-- Forget the sense (to reuse `combineForm`/`combine`). -/
def SLe.toLe (c : SLe) : Le := ⟨c.form, c.rhs⟩

/-- The combined form/rhs, reusing `combineForm`/`combine` on sense-forgotten rows. -/
def scomb (comb : List (ℚ × SLe)) : Le := combine (comb.map (fun p => (p.1, p.2.toLe)))

/-! ## Form equality (for constraint domination) -/

/-- Negate a form (as `-1 · f`). -/
def sNegForm (f : LinForm) : LinForm := LinForm.scale (-1) f

/-! ### Tests on an already normalized form

`linCheck` and `rndCheck` normalize the (typically long) combined form once and reuse
it: `normForm (f ++ g)` extends `normForm f` term by term with the short stated row `g`.
The `@[simp]` lemmas fold these tests back into `formIsZero`, `formEq`, and `formIntB`. -/

/-- Extend a normalized form with further terms. -/
def alExtend (al : List (Nat × ℚ)) (g : LinForm) : List (Nat × ℚ) :=
  g.foldl (fun acc t => addTerm acc t.idx t.coeff) al

/-! ## Derivation replay over sensed constraints -/

/-- A derivation step: the stated (sensed) row, and its reason (indices reference the
running pool: base constraints `0..m-1`, then derivations). -/
inductive SReason where
  | asm
  | lin (comb : List (ℚ × Nat))
  | rnd (comb : List (ℚ × Nat))
  | uns (i1 l1 i2 l2 : Nat)
  | sol

structure SStep where
  stated : SLe
  reason : SReason

abbrev SAsm := Finset SLe

abbrev SPool := List (SLe × SAsm)

def sdflt : SLe × SAsm := (⟨'L', [], 0⟩, ∅)

def spoolRow (pool : SPool) (i : Nat) : SLe := (pool.getD i sdflt).1

def spoolAsm (pool : SPool) (i : Nat) : SAsm := (pool.getD i sdflt).2

def resolve (pool : SPool) (comb : List (ℚ × Nat)) : List (ℚ × SLe) :=
  comb.map (fun p => (p.1, spoolRow pool p.2))

/-- Union of the open-assumption sets of all rows referenced by a combination. -/
def collectAsms (pool : SPool) : List (ℚ × Nat) → SAsm
  | [] => ∅
  | p :: ps => spoolAsm pool p.2 ∪ collectAsms pool ps

/-- The pool entry a step produces. An `uns` (case-split) entry keeps the stated row and
discharges the two branch bounds: its open assumptions are branch `i1`'s minus bound
`l1`, plus branch `i2`'s minus bound `l2`. -/
def sentryOf (pool : SPool) (s : SStep) : SLe × SAsm :=
  match s.reason with
  | .asm => (s.stated, {s.stated})
  | .lin comb => (s.stated, collectAsms pool comb)
  | .rnd comb => (s.stated, collectAsms pool comb)
  | .uns i1 l1 i2 l2 =>
      (s.stated, (spoolAsm pool i1).erase (spoolRow pool l1) ∪
        (spoolAsm pool i2).erase (spoolRow pool l2))
  | .sol => (s.stated, ∅)

/-- Declarative list replay used by the proof-system semantics. -/
def sfreplay (pool : SPool) : List SStep → SPool
  | [] => pool
  | s :: ss => sfreplay (pool ++ [sentryOf pool s]) ss

/-- Initial pool from the base (CON) rows, each with no assumptions. -/
def sinitPool (base : List SLe) : SPool := base.map (fun c => (c, (∅ : SAsm)))

end LeanVIPR.Semantics
