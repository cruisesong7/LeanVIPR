module

public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Tactic.Basic
public meta import LeanVIPRTactic.Scip

/-!
# Options for `mip`, `mip_maximize`, `mip_minimize` and `#mip_scip`

Written in Lean's standard configuration syntax, as for `omega` and `decide`:

```lean
mip (timeout := 60) (dir := "/tmp/run")
mip (cert := "Foo-bar-12-2.vipr")   -- no solver: the certificates `mip?` saved
```

Where a term follows the options — the objective of `mip_maximize`, the problem of
`#mip_scip` — the `-opt` form is not accepted: `-x` would otherwise be read as the option
`x := false`, and the objective taken from whatever comes next. Write `(opt := false)`.
`+opt` is safe there, since Lean has no unary `+`.

Not `@[expose]`, unlike the other files here: `declare_config_elab` defines a private
helper, which an exposed body could not refer to.
-/

public section

namespace LeanVIPR.Tactic

/-- Options before a term: `+opt` and `(opt := v)`, not `-opt`. See the module docstring. -/
syntax mipTermConfig :=
  (colGt (Lean.Parser.Tactic.posConfigItem <|> Lean.Parser.Tactic.valConfigItem))*

end LeanVIPR.Tactic

end

public meta section

namespace LeanVIPR.Tactic

/-- Options for the `mip` tactics and `#mip_scip`. -/
structure MipConfig where
  /-- Keep the `.mps` and `.vipr` in this directory. `""`, the default, uses a temporary
  one. -/
  dir : String := ""
  /-- Stop the solver after this many seconds. `0`, the default, means no limit. -/
  timeout : Nat := 0
  /-- Take the certificates from this file instead of running the solver. Relative to the
  Lean file's directory, as for `bv_check`; `mip?` writes the file and suggests the call. -/
  cert : String := ""
  /-- Encode a disjunction of two comparisons with a fresh binary, where both sides have a
  finite big-M, rather than splitting it into cases: one solver call instead of two.
  `mip -encodeDisjunctions` splits every one. -/
  encodeDisjunctions : Bool := true
  /-- Decide the certificate's checks by compiled code (`decide +native`) rather than by the
  kernel: much faster on a large certificate, at the cost of trusting the compiler. Each
  check adds an axiom of its own to the proof, as `native_decide` does. -/
  native : Bool := false

/-- Elaborate the options of a `mip` tactic. -/
declare_config_elab elabMipConfig MipConfig

/-- Elaborate the options of `#mip_scip`. -/
declare_command_config_elab elabMipCommandConfig MipConfig

/-- The solver settings the options ask for, leaving `cert` aside. -/
def MipConfig.toScipConfig (c : MipConfig) : ScipConfig :=
  { workDir := if c.dir.isEmpty then none else some ⟨c.dir⟩
    timeLimit := if c.timeout == 0 then none else some c.timeout
    encodeDisjunctions := c.encodeDisjunctions
    native := c.native }

/-- The directory of the Lean file being elaborated. -/
def srcDirOf (fileName : String) : System.FilePath :=
  (System.FilePath.mk fileName).parent.getD "."

open Lean in
/-- The solver settings the options ask for, with the saved certificates read in if `cert`
names a file. -/
def MipConfig.resolve {m : Type → Type} [Monad m] [MonadLog m] [MonadError m]
    [MonadLiftT IO m] (c : MipConfig) : m ScipConfig := do
  if c.cert.isEmpty then return c.toScipConfig
  match ← (loadSaved (srcDirOf (← getFileName) / c.cert) : IO _) with
  | .error e => throwError e.message
  | .ok s => return { c.toScipConfig with saved? := some s }

open Lean Elab Tactic in
/-- Where `mip?` saves a call's certificates: `File-decl-line-col.vipr` next to the Lean
file, as `bv_decide?` names its LRAT proofs. -/
def savedFileName : TacticM String := do
  let stem := (System.FilePath.mk (← getFileName)).fileStem.getD "lean"
  let decl := (← Term.getDeclName?).map toString |>.getD "anonymous"
  let pos := (← getFileMap).toPosition (← getRefPos)
  let safe (c : Char) := c.isAlphanum || c == '_' || c == '-' || c == '.'
  return s!"{stem}-{decl}-{pos.line}-{pos.column}".map (fun c => if safe c then c else '_')
    ++ ".vipr"

open Lean Elab Tactic in
/-- Start recording for `mip?`: the options, and where the certificates go. -/
def MipConfig.recording (c : MipConfig) : TacticM (ScipConfig × IO.Ref (Array String)) := do
  unless c.cert.isEmpty do
    throwError "`mip?` writes the certificate file, so it takes no `(cert := …)`"
  let r ← IO.mkRef #[]
  return ({ c.toScipConfig with record? := some r }, r)

open Lean Elab Tactic in
/-- Write what `mip?` recorded to `name`, next to the Lean file. -/
def saveRecorded (r : IO.Ref (Array String)) (name : String) : TacticM Unit := do
  let texts ← r.get
  if texts.isEmpty then throwError "internal: `mip?` recorded no certificate"
  IO.FS.writeFile (srcDirOf (← getFileName) / name) (joinCertificates texts)

end LeanVIPR.Tactic

end
