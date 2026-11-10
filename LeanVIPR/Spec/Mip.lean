module

public import LeanVIPR.Spec.Semantics.System

@[expose] public section

/-!
# The mixed-integer program, as stated in Lean

**This is the question.** A VIPR certificate answers a question about a mixed-integer
program, but the certificate carries its own copy of that program in its `CON` section,
so `LeanVIPR.Spec.Semantics.Claim` can only ever say *the problem this file is about* is
infeasible. Nothing so far says which problem that is, or that it is the one we meant to
ask about.

This file supplies the missing end: a mixed-integer program written directly in Lean, and
what it means for a real valuation to be feasible for it. It is the source of truth for
the SCIP pipeline — the thing we encode into MPS and hand to the solver, and the thing
the returned certificate is checked against.

Definitions only, and deliberately shaped to line up with `Vipr.Feasible`: `Mip.conSLes`
produces the same `List SLe` vocabulary as `LeanVIPR.Semantics.Lower.conSLes`, so the
agreement between a problem and a certificate is a statement about two lists of rows
rather than about two unrelated semantics.

Mathlib has no linear- or mixed-integer-program type, so this is it.
-/

namespace LeanVIPR

open LeanVIPR.Semantics LeanVIPR.Semantics.System

namespace Mip

/-- Which way the objective is optimized. -/
inductive ObjSense where
  | min
  | max
  deriving Repr, DecidableEq, Inhabited

/-- A declared variable: the name it is given in the emitted problem file, whether it is
integral, and its bounds. `none` is an infinite bound.

The defaults are MPS's own: a variable is continuous, bounded below by zero and
unbounded above. Stating them here rather than relying on the reader's defaults keeps
the meaning of a `Mip` independent of the file format. -/
structure Var where
  name : String
  isInt : Bool := false
  lo : Option ℚ := some 0
  hi : Option ℚ := none
  deriving Repr, DecidableEq, Inhabited

/-- A named constraint row `form sense rhs`, with `sense ∈ {'L', 'G', 'E'}` as in
`SLe`. The name is carried because the emitted file needs one and because the agreement
check reports against it; it has no bearing on the meaning of the row. -/
structure Row where
  name : String
  sense : Char
  rhs : ℚ
  form : LinForm
  deriving Repr, DecidableEq, Inhabited

end Mip

/-- A mixed-integer program. Variables are referred to by their index in `vars`, which
is the same indexing `LinForm` uses, so `obj` and every `Row.form` are forms over
`Fin vars.size` spelled as `Nat`. An index past `vars.size` is not ruled out by the type;
`WellFormed` rules it out. -/
structure Mip where
  vars : Array Mip.Var
  objSense : Mip.ObjSense
  obj : LinForm
  rows : Array Mip.Row
  deriving Repr, Inhabited

namespace Mip

/-! ## The rows a problem stands for -/

/-- The declared integer variables, by index. -/
def intVars (m : Mip) : List Nat :=
  (m.vars.toList.mapIdx (fun j v => if v.isInt then [j] else [])).flatten

/-- The sensed rows a single variable declaration stands for. -/
def Var.boundSLes (j : Nat) (v : Var) : List SLe :=
  (match v.lo with
   | none => []
   | some l => [⟨'G', [⟨j, 1⟩], l⟩]) ++
  (match v.hi with
   | none => []
   | some u => [⟨'L', [⟨j, 1⟩], u⟩])

/-- The sensed rows the variable bounds stand for, in index order, lower bound first.
This is the order exact SCIP emits them in, which is why the agreement check can compare
row lists without sorting. -/
def boundSLes (m : Mip) : List SLe :=
  (m.vars.toList.mapIdx Var.boundSLes).flatten

/-- The sensed rows the explicit constraints stand for. -/
def rowSLes (m : Mip) : List SLe :=
  m.rows.toList.map (fun r => ⟨r.sense, r.form, r.rhs⟩)

/-- Every row of the problem: the explicit constraints, then the variable bounds. -/
def conSLes (m : Mip) : List SLe :=
  m.rowSLes ++ m.boundSLes

/-! ## What the problem means

Over `RealValuation`, for the same reason `LeanVIPR.Spec.Semantics.System` is: the
problem a solver claims to have solved is the real one, and the rational coefficients
are how it is written down, not what it is about. -/

/-- A real valuation is feasible when the declared integer variables take integer values
and every row holds. -/
def Feasible (m : Mip) (a : RealValuation) : Prop :=
  (∀ j ∈ m.intVars, IsIntReal (a j)) ∧
  (∀ c ∈ m.conSLes, satReal c a)

/-- The objective value at a valuation. -/
def objectiveReal (m : Mip) (a : RealValuation) : ℝ :=
  evalReal m.obj a

/-- A feasible valuation at which the objective is optimal. -/
def IsOptimal (m : Mip) (a : RealValuation) : Prop :=
  m.Feasible a ∧
  match m.objSense with
  | .min => ∀ b, m.Feasible b → m.objectiveReal a ≤ m.objectiveReal b
  | .max => ∀ b, m.Feasible b → m.objectiveReal b ≤ m.objectiveReal a

/-! ## The two results a certificate can establish -/

/-- No feasible mixed-integer valuation exists. This is what `RTP infeas` claims. -/
def Infeasible (m : Mip) : Prop :=
  ∀ a, m.Feasible a → False

/-- The objective lies in `[lb, ub]` at every optimum, with `none` an infinite end.
This is what `RTP range` claims, in the form it is usually quoted. The stronger
statement a valid certificate actually gives — the derived bound holds at *every*
feasible valuation, so it bounds the infimum even when no optimum is attained — is
`RangeBoundValid` in `LeanVIPR.Spec.Semantics.Claim`, and the transfer theorem is
stated against that. -/
def OptimumWithin (m : Mip) (lb ub : Option ℚ) : Prop :=
  ∀ a, m.IsOptimal a →
    (match lb with
     | none => True
     | some lower => (lower : ℝ) ≤ m.objectiveReal a) ∧
    (match ub with
     | none => True
     | some upper => m.objectiveReal a ≤ (upper : ℝ))

/-! ## Relating a problem to someone else's variable numbering

A certificate restates its problem in its own variable numbering, so comparing it to a
`Mip` means comparing rows across a renaming. `RelaxesRows` is that comparison, stated
once and instantiated in both directions: `Relaxes` forwards and `Relaxed` backwards, with
`SameProblem` their conjunction.

Each direction is undemanding about its renaming — see `Relaxes` for why nothing at all is
required of `σ` — and the two directions license different conclusions, so which one a
theorem needs is worth reading off its statement rather than assuming.

**Why a subset and not an equality.** To conclude `m.Infeasible` from a certificate's
infeasibility, all that is needed is that every `m`-feasible point gives rise to a
certificate-feasible point. That holds as soon as every row the *certificate* constrains
is a row of `m` — the certificate's problem may constrain less, in which case its feasible
set is larger, and emptiness still transports down. Equality of the two problems is a
stronger statement that nothing here needs.

**Why nothing is required of `σ`.** `σ` maps the certificate's indices to ours, so
`a ∘ σ` is a well-defined valuation for *any* `σ` whatsoever — no injectivity, no
surjectivity, no agreement of sizes. A wrong `σ` cannot produce an unsound conclusion; it
can only fail the membership tests below. That is what lets the search for `σ` be an
untrusted heuristic. -/

/-- Rename the variables of a linear form, sending each term's index through `σ`. -/
def renameForm (σ : Nat → Nat) (f : LinForm) : LinForm :=
  f.map (fun t => ⟨σ t.idx, t.coeff⟩)

/-- Rename the variables of a row, sending each term's index through `σ`. -/
def renameSLe (σ : Nat → Nat) (c : SLe) : SLe :=
  { c with form := renameForm σ c.form }

/-- The foreign objective, read in our numbering, is our objective — as a linear
function, not as a list, since the certificate orders its terms its own way.

Separate from `Relaxes` because the two carry different weight. `Relaxes` is what makes
the infeasibility conclusion sound; this is additionally needed to carry an objective
*bound* across, and it is irrelevant to `RTP infeas`. -/
def ObjAgrees (m : Mip) (σ : Nat → Nat) (objForm : LinForm) : Prop :=
  FormEqReal (renameForm σ objForm) m.obj

/-- The foreign objective is the *negation* of ours.

This is not an exotic case, it is the normal one for maximization. Exact SCIP converts a
maximization to a minimization by negating the objective, so a `Mip` with
`objSense := .max` comes back as a certificate saying `OBJ min` over `-obj`, with its
bounds negated to match. Measured: every certificate real exact SCIP has produced here
says `OBJ min`, whatever the problem said.

A minimizing certificate's *lower* bound `l` on `-obj` is therefore an *upper* bound `-l`
on our objective, which is what `pipeline_upper_bound_of_min` concludes. -/
def ObjAgreesNeg (m : Mip) (σ : Nat → Nat) (objForm : LinForm) : Prop :=
  FormEqReal (renameForm σ objForm) (LinForm.scale (-1) m.obj)

/-- `σ` exhibits the problem `(rows₂, ints₂)` as a relaxation of `(rows₁, ints₁)`: every
variable the second declares integral renames to one the first does, and every row of the
second, once renamed, is implied by a row of the first.

Stated on bare row/integer lists rather than on a `Mip` because `Mip.Feasible` and
`Vipr.Feasible` are literally the same shape — `(∀ j ∈ ints, IsIntReal (a j)) ∧
(∀ c ∈ rows, satReal c a)`. One relation and one transfer lemma therefore serve both
directions: `Relaxes` instantiates it with `m` first, and `Relaxed` with the certificate
first. That symmetry is why the second direction costs almost nothing. -/
def RelaxesRows (rows₁ : List SLe) (ints₁ : List Nat) (σ : Nat → Nat)
    (rows₂ : List SLe) (ints₂ : List Nat) : Prop :=
  (∀ i ∈ ints₂, σ i ∈ ints₁) ∧
  (∀ c ∈ rows₂, ∃ d ∈ rows₁, Dominates d (renameSLe σ c))

/-- `σ` exhibits a foreign problem — given as its rows and its integer variables, in its
own numbering — as a relaxation of `m`: every variable it declares integral renames to one
`m` declares integral, and every foreign row, once renamed, is *implied by* some row of
`m`.

Implication rather than equality, via the existing `Dominates`, because mere list equality
on `SLe` is too brittle to be usable. Exact SCIP emits a renamed row's terms in its own
index order, so the knapsack's `C0` renames to a form listing `(1,10)` before `(0,6)`
where ours lists `(0,6)` first — the same linear function, a different list. `Dominates`
compares forms through `formEq`, which is insensitive to term order and to repeated
indices, and additionally accepts a tighter `m` bound implying a looser foreign one. -/
def Relaxes (m : Mip) (σ : Nat → Nat) (rows : List SLe) (ints : List Nat) : Prop :=
  RelaxesRows m.conSLes m.intVars σ rows ints

/-- The converse direction: `τ` exhibits `m` as a relaxation of the foreign problem, so a
foreign-feasible point gives rise to an `m`-feasible one.

This is the half a *positive* answer needs. `Relaxes` alone makes an infeasibility claim
transfer down; to use a certificate's `SOL` entry as an actual solution of `m`, or to say
the two are *the same problem* rather than one bounding the other, feasibility has to
travel the other way too.

Unlike `Relaxes`, this direction genuinely needs a second map. `σ` sends the
certificate's indices to ours, which is what makes `a ∘ σ` meaningful for an arbitrary
`σ`; going back needs `τ` in the opposite direction. The two are not required to be
mutually inverse — nothing below assumes it — they are simply two independently checked
renamings. -/
def Relaxed (m : Mip) (τ : Nat → Nat) (rows : List SLe) (ints : List Nat) : Prop :=
  RelaxesRows rows ints τ m.conSLes m.intVars

/-- Both directions at once: the certificate's problem and ours are the same problem, each
read through its own renaming. This is the LeanVIPR analogue of the index Trestle's
`VEncCNF` carries — an equivalence of feasible sets modulo renaming, rather than a
one-sided bound. -/
def SameProblem (m : Mip) (σ τ : Nat → Nat) (rows : List SLe) (ints : List Nat) : Prop :=
  m.Relaxes σ rows ints ∧ m.Relaxed τ rows ints

/-! ## Integer witnesses

A `Mip` means something about `RealValuation`, because that is the setting a solver's
claim lives in. A user's `Prop`, though, quantifies over `ℤ`: the thing they want to know
is that no *integer* tuple satisfies their constraints. `valuationOfInts` is the bridge
between the two, and it is what a `Prop`-level front end reflects a goal through. -/

/-- The real valuation sending variable `j` to the `j`-th entry of `xs`, and to zero past
the end of the list. Every value is the cast of an integer, so `IsIntReal` holds at every
index — which is why a goal about integer tuples needs no integrality side conditions. -/
def valuationOfInts (xs : List ℤ) : RealValuation := fun j => ((xs.getD j 0 : ℤ) : ℝ)

/-! ## Well-formedness

A `Mip` with a form mentioning a variable it never declared still has a meaning — the
valuation assigns that index a value like any other — but it cannot be written to a
problem file, since there is no name to write. The encoder requires this; the semantics
above do not. The *further* conditions the encoder needs — that names be tokens a reader
will give back — are `LeanVIPR.Mps.EncodableNames`, stated where the grammar is. -/

/-- Every index a form mentions is a declared variable. -/
def FormDeclared (m : Mip) (f : LinForm) : Prop :=
  ∀ t ∈ f, t.idx < m.vars.size

/-- Names are what a problem file refers to, so distinct variables need distinct names,
and so do distinct rows. -/
def WellFormed (m : Mip) : Prop :=
  m.FormDeclared m.obj ∧
  (∀ r ∈ m.rows, m.FormDeclared r.form ∧ (r.sense = 'L' ∨ r.sense = 'G' ∨ r.sense = 'E')) ∧
  (m.vars.toList.map Var.name).Nodup ∧
  (m.rows.toList.map Row.name).Nodup

end Mip

end LeanVIPR
