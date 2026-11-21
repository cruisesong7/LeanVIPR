module

public meta import Lean.Elab.ConfigEval
public meta import LeanVIPRTactic.Scip

/-!
# Options for `mip`, `mip_maximize`, `mip_minimize` and `#mip_scip`

Written in Lean's standard configuration syntax, as for `omega` and `decide`:

```lean
mip (timeout := 60) (dir := "/tmp/run")
```

Where a term follows the options — the objective of `mip_maximize`, the problem of
`#mip_scip` — only the `(opt := v)` form is accepted: `-x` would otherwise be read as the
option `x := false`, and the objective taken from whatever comes next.

Not `@[expose]`, unlike the other files here: `declare_config_elab` defines a private
helper, which an exposed body could not refer to.
-/

public section

namespace LeanVIPR.Tactic

/-- Options before a term: `(opt := v)` items only. See the module docstring. -/
syntax mipTermConfig := (colGt Lean.Parser.Tactic.valConfigItem)*

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

/-- Elaborate the options of a `mip` tactic. -/
declare_config_elab elabMipConfig MipConfig

/-- Elaborate the options of `#mip_scip`. -/
declare_command_config_elab elabMipCommandConfig MipConfig

/-- The solver settings the options ask for. -/
def MipConfig.toScipConfig (c : MipConfig) : ScipConfig :=
  { workDir := if c.dir.isEmpty then none else some ⟨c.dir⟩
    timeLimit := if c.timeout == 0 then none else some c.timeout }

end LeanVIPR.Tactic

end
