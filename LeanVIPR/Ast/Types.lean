module

public import LeanVIPR.Cert.LinCon

@[expose] public section

/-!
# The parsed certificate

The shape a VIPR certificate is read into. Separated from the reader so that the
grammar denotation in `LeanVIPR.Ast.ViprDenote` can be stated without reference to
any parser function.
-/

namespace LeanVIPR.Ast

open LeanVIPR.Cert

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
    | .infeas, _ => "LeanVIPR.Ast.ViprRtp.infeas"
    | .range lb ub, prec =>
        Repr.addAppParen
          ("LeanVIPR.Ast.ViprRtp.range " ++ reprOptionRat lb ++ " " ++ reprOptionRat ub)
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

/-- A certificate as a list of whitespace-separated tokens. -/
abbrev Toks := List String

end LeanVIPR.Ast
