module

public import LeanVIPR.Cert.Vipr
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Sensed VIPR rows and the executable rule checks

Real solver certificates use VIPR's *suitable linear combination*: **signed**
multipliers over constraints of mixed senses (`≤`, `≥`, `=`), deriving a row of a
computed sense that must **dominate** the stated one. This module defines sensed rows
`SLe`, the Boolean rule checks (`linCheck`, `rndCheck`, `domSLe`, `unsBoundsB`), and the
replay pool. Their real-valued soundness is proved in `ViprRuleSound`.

Sign convention (VIPR spec): `s(C) = -1` for `≤`, `+1` for `≥`, `0` for `=`. A
combination with multipliers `λⱼ` derives a `≤` row when every `λⱼ·s(Cⱼ) ≤ 0`, and a
`≥` row when every `λⱼ·s(Cⱼ) ≥ 0`.
-/

namespace LeanVIPR.Cert

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

theorem scomb_eval (comb : List (ℚ × SLe)) (a : Valuation) :
    (scomb comb).form.eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  simp only [scomb, combine, eval_combineForm, List.map_map]
  rfl

theorem scomb_rhs (comb : List (ℚ × SLe)) :
    (scomb comb).rhs = (comb.map (fun p => p.1 * p.2.rhs)).sum := by
  simp only [scomb, combine, List.map_map]
  rfl

/-! ## Form equality (for constraint domination) -/

/-- Negate a form (as `-1 · f`). -/
def sNegForm (f : LinForm) : LinForm := LinForm.scale (-1) f

/-- Decidable "the two forms are equal as functions" (their difference is identically 0). -/
def formEq (f g : LinForm) : Bool := formIsZero (f ++ sNegForm g)

/-! ## Per-reason checks and soundness -/

/-- Decidable suitability for a `≤`-deriving combination. -/
def suitLeB (cs : List (ℚ × SLe)) : Bool := cs.all (fun p => decide (p.1 * senseSign p.2.sense ≤ 0))
/-- Decidable suitability for a `≥`-deriving combination. -/
def suitGeB (cs : List (ℚ × SLe)) : Bool := cs.all (fun p => decide (0 ≤ p.1 * senseSign p.2.sense))

theorem suitLeB_sound {cs} (h : suitLeB cs = true) : ∀ p ∈ cs, p.1 * senseSign p.2.sense ≤ 0 :=
  fun p hp => of_decide_eq_true ((List.all_eq_true.mp h) p hp)
theorem suitGeB_sound {cs} (h : suitGeB cs = true) : ∀ p ∈ cs, 0 ≤ p.1 * senseSign p.2.sense :=
  fun p hp => of_decide_eq_true ((List.all_eq_true.mp h) p hp)

/-- One normalized coefficient is integral on an integer variable, or vanishes. -/
def intEntryB (intVars : List Nat) (p : Nat × ℚ) : Bool :=
  p.2 == 0 || (isIntValB p.2 && decide (p.1 ∈ intVars))

/-- The form is integer-valued: after summing duplicate indices, every nonzero
coefficient is an integer on an integer variable. Normalizing first accepts
combinations whose fractional or continuous-variable terms cancel. -/
def formIntB (intVars : List Nat) (f : LinForm) : Bool :=
  (normForm f).all (intEntryB intVars)

/-! ### Tests on an already normalized form

`linCheck` and `rndCheck` normalize the (typically long) combined form once and reuse
it: `normForm (f ++ g)` extends `normForm f` term by term with the short stated row `g`.
The `@[simp]` lemmas fold these tests back into `formIsZero`, `formEq`, and `formIntB`. -/

/-- Extend a normalized form with further terms. -/
def alExtend (al : List (Nat × ℚ)) (g : LinForm) : List (Nat × ℚ) :=
  g.foldl (fun acc t => addTerm acc t.idx t.coeff) al

def alIsZero (al : List (Nat × ℚ)) : Bool := al.all (fun p => p.2 == 0)

def alIntB (intVars : List Nat) (al : List (Nat × ℚ)) : Bool := al.all (intEntryB intVars)

@[simp] theorem alIsZero_normForm (f : LinForm) : alIsZero (normForm f) = formIsZero f := rfl

@[simp] theorem alIntB_normForm (intVars : List Nat) (f : LinForm) :
    alIntB intVars (normForm f) = formIntB intVars f := rfl

@[simp] theorem alIsZero_alExtend_normForm (f g : LinForm) :
    alIsZero (alExtend (normForm f) (sNegForm g)) = formEq f g := by
  simp only [alExtend, normForm, formEq, formIsZero, alIsZero, List.foldl_append]

theorem intEntryB_sound {intVars : List Nat} {p : Nat × ℚ}
    (h : intEntryB intVars p = true) :
    p.2 = 0 ∨ (IsIntVal p.2 ∧ p.1 ∈ intVars) := by
  simp only [intEntryB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with h | ⟨hq, hidx⟩
  · exact Or.inl h
  · exact Or.inr ⟨isIntValB_sound hq, hidx⟩

/-- The combination is itself an absurdity (identically-zero form, rhs contradicting a
valid sense) — which, per the VIPR spec, dominates *any* stated constraint. -/
def linAbsurd (cs : List (ℚ × SLe)) (combined : Le) (normalized : List (Nat × ℚ)) : Bool :=
  (suitLeB cs && alIsZero normalized && decide (combined.rhs < 0)) ||
  (suitGeB cs && alIsZero normalized && decide (0 < combined.rhs))

/-- **`lin` step check.** Accepts either normal rhs-domination or an absurd combination.
The combination is computed once and shared by every test. -/
def linCheck (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  let combined := scomb cs
  let normalized := normForm combined.form
  linAbsurd cs combined normalized ||
  (alIsZero (alExtend normalized (sNegForm stated.form)) &&
    (if stated.sense = 'L' then suitLeB cs && decide (combined.rhs ≤ stated.rhs)
     else if stated.sense = 'G' then suitGeB cs && decide (stated.rhs ≤ combined.rhs)
     else if stated.sense = 'E' then
       suitLeB cs && suitGeB cs && decide (combined.rhs = stated.rhs)
     else false))

/-- **`rnd` step check.** -/
def rndCheck (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  let combined := scomb cs
  let normalized := normForm combined.form
  alIsZero (alExtend normalized (sNegForm stated.form)) && alIntB intVars normalized &&
  (if stated.sense = 'L' then
      suitLeB cs && decide (((⌊combined.rhs⌋ : ℤ) : ℚ) ≤ stated.rhs)
   else if stated.sense = 'G' then
      suitGeB cs && decide (stated.rhs ≤ ((⌈combined.rhs⌉ : ℤ) : ℚ))
   else false)

/-! ## Domination and complementary integer bounds (for `uns` case-splits) -/

/-- An absurdity (identically-zero form, rhs contradicting the sense). -/
def absurdB (c : SLe) : Bool :=
  formIsZero c.form &&
  (if c.sense = 'L' then decide (c.rhs < 0)
   else if c.sense = 'G' then decide (0 < c.rhs)
   else if c.sense = 'E' then decide (c.rhs ≠ 0)
   else false)

/-- `c` dominates `d`: either `c` is an absurdity (which, per the VIPR spec, dominates
any constraint), or the forms are equal as functions and the right-hand side is at least
as strong for `d`'s sense (an `=`-row dominates either inequality direction). -/
def domSLe (c d : SLe) : Bool :=
  absurdB c ||
  (formEq c.form d.form &&
   (if d.sense = 'L' then ((c.sense == 'L') || (c.sense == 'E')) && decide (c.rhs ≤ d.rhs)
    else if d.sense = 'G' then ((c.sense == 'G') || (c.sense == 'E')) && decide (d.rhs ≤ c.rhs)
    else if d.sense = 'E' then (c.sense == 'E') && decide (c.rhs = d.rhs)
    else false))

/-- `b1`,`b2` are complementary integer bounds `f ≤ β` / `f ≥ β+1` (in either order):
same form as functions, integer-valued form over `intVars`, integer `β`. -/
def unsBoundsB (intVars : List Nat) (b1 b2 : SLe) : Bool :=
  ((b1.sense == 'L') && (b2.sense == 'G') && formEq b1.form b2.form
    && formIntB intVars b1.form && isIntValB b1.rhs && decide (b2.rhs = b1.rhs + 1))
  ||
  ((b1.sense == 'G') && (b2.sense == 'L') && formEq b1.form b2.form
    && formIntB intVars b2.form && isIntValB b2.rhs && decide (b1.rhs = b2.rhs + 1))

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

theorem mem_collectAsms {pool : SPool} {comb : List (ℚ × Nat)}
    {p : ℚ × Nat} (hp : p ∈ comb) {t : SLe} (ht : t ∈ spoolAsm pool p.2) :
    t ∈ collectAsms pool comb := by
  induction comb with
  | nil => simp at hp
  | cons q qs ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Finset.mem_union_left _ ht
      · exact Finset.mem_union_right _ (ih hp)

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

end LeanVIPR.Cert
