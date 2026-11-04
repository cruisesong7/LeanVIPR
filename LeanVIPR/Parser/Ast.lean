module

public import LeanVIPR.Semantics.LinCon

@[expose] public section

/-!
# The parsed certificate

The shape a VIPR certificate is read into. Kept separate from the reader
(`LeanVIPR.Parser.Read`) so that the grammars in `LeanVIPR.Thm.Parser.Grammar` and
`LeanVIPR.Thm.Valid.Grammar` can be stated without reference to any parser function.

It also holds the few functions that say what the AST's index fields *mean* — which
constraints a reason cites, and what a `DER` row's trailing field declares. Those are
part of the format rather than of the reader, and are shared by the validator and by
its specification.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Semantics

/-- A `CON` constraint: `name sense rhs (form | OBJ)`. -/
structure ViprCon where
  name : String
  sense : Char        -- 'E' (=), 'L' (≤), 'G' (≥)
  rhs : ℚ
  form : LinForm      -- explicit sparse form; empty when `usesObj`
  usesObj : Bool      -- form is the objective row
  deriving Repr, Inhabited

/-- One local variable bound offered for completing a VIPR v1.1 `lin weak` reason. -/
structure ViprWeakBound where
  kind : Char
  varIdx : Nat
  rowIdx : Nat
  value : ℚ
  deriving Repr, Inhabited

/-- Bounds available while completing a VIPR v1.1 `lin weak` reason.

`global` is the `{ 0 }` spelling; `local` records the explicitly listed local bounds
and permits fallback to the global bounds, as in the reference completer. -/
inductive ViprWeakBounds where
  | global
  | local (bounds : List ViprWeakBound)
  deriving Repr, Inhabited

/-- The justification of a derived constraint. `lin`/`linWeak`/`rnd` carry
`(index, multiplier)` pairs referencing earlier constraints; `uns` carries four earlier
indices. -/
inductive ViprReason where
  | asm
  | lin (terms : List (Nat × ℚ))
  | linWeak (bounds : ViprWeakBounds) (terms : List (Nat × ℚ))
  | rnd (terms : List (Nat × ℚ))
  | uns (i1 l1 i2 l2 : Nat)
  | sol
  deriving Repr, Inhabited

/-- A `DER` derived constraint: `name sense rhs (form | OBJ) { reason } finalUseIdx`. -/
structure ViprDer where
  name : String
  sense : Char
  rhs : ℚ
  form : LinForm
  usesObj : Bool
  reason : ViprReason
  idx : Int            -- trailing final-use index (`-1` = unused)
  isGlobal : Bool := false
  deriving Repr, Inhabited

/-- The `RTP` (relation-to-prove) target. -/
inductive ViprRtp where
  | infeas
  | range (lb ub : Option ℚ)   -- `none` = unbounded (`-inf` / `inf`)
  deriving Inhabited, DecidableEq

/-- Render an optional bound with explicit parentheses. The derived instance prints
`some -7`, which Lean reparses as a subtraction when emitting kernel-mode data. -/
def reprOptionRat : Option ℚ → Std.Format
  | none => "none"
  | some q => "(some (" ++ repr q ++ "))"

instance : Repr ViprRtp where
  reprPrec
    | .infeas, _ => "LeanVIPR.Parser.ViprRtp.infeas"
    | .range lb ub, prec =>
        Repr.addAppParen
          ("LeanVIPR.Parser.ViprRtp.range " ++ reprOptionRat lb ++ " " ++ reprOptionRat ub)
          prec

/-- A parsed VIPR certificate. -/
structure Vipr where
  version : String
  varNames : Array String
  intVars : List Nat
  objSense : String              -- "min" / "max"
  objTerms : List (Nat × ℚ)
  numCon : Nat
  numBounds : Nat
  cons : Array ViprCon
  rtp : ViprRtp
  numSol : Nat
  sols : Array (String × List (Nat × ℚ))
  ders : Array ViprDer
  deriving Repr, Inhabited

/-! ## What the AST's index fields mean

These are not parser functions: they say what a reason refers to and what a `DER` row's
trailing field declares, which is part of the format and is used both by the validator
and by its specification in `LeanVIPR.Thm.Valid.Grammar`. -/

/-- The constraint indices a reason refers to. A `lin weak` reason also refers to the
rows naming its local variable bounds, since completion may use them. -/
def reasonRefs : ViprReason → List Nat
  | .asm | .sol => []
  | .lin terms | .rnd terms => terms.map Prod.fst
  | .linWeak bounds terms =>
      terms.map Prod.fst ++
        (match bounds with
         | .global => []
         | .local bs => bs.map (·.rowIdx))
  | .uns i1 l1 i2 l2 => [i1, l1, i2, l2]

/-- The multipliers a reason must not repeat. The specification requires the constraint
indices of `lin` and `rnd` reasons to be distinct; the reference checker silently keeps
the last multiplier. -/
def reasonMultipliers : ViprReason → List Nat
  | .lin terms | .linWeak _ terms | .rnd terms => terms.map Prod.fst
  | .asm | .sol | .uns _ _ _ _ => []

/-- The final-use index declared for constraint `k`: `-1` for an original `CON` row,
which is never discarded, and otherwise the trailing field of derivation `k`. -/
def finalUseHint (v : Vipr) (k : Nat) : Int :=
  if k < v.cons.size then -1 else (v.ders.getD (k - v.cons.size) default).idx

/-- Constraint `k` is used by the derivation with index `user`, but `k` declared a
final-use index before `user` — so a verifier was entitled to have discarded it. A
hint of `-1` means "never discarded" and so is never a violation. -/
def usedAfterFinal (v : Vipr) (user : Nat) (k : Nat) : Prop :=
  0 ≤ finalUseHint v k ∧ finalUseHint v k < (user : Int)

instance (v : Vipr) (user k : Nat) : Decidable (usedAfterFinal v user k) := by
  unfold usedAfterFinal; infer_instance

/-- A certificate as a list of whitespace-separated tokens. -/
abbrev Toks := List String

end LeanVIPR.Parser
