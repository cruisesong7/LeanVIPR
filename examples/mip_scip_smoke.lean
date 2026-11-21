import LeanVIPRTactic

/-!
Smoke tests for stages 1 and 2 of the `mip` tactic: driving exact SCIP from `IO`, and
reporting the result from a command.

These **require a certifying SCIP build** and so are not part of `lake build`. Run them
with the binary from `docs/SCIP-SETUP.md`:

```
LEANVIPR_SCIP=~/scip-exact/scipoptsuite-10.0.1/build/bin/scip \
  lake env lean examples/mip_scip_smoke.lean
```

Nothing here proves anything — `#mip_scip` only logs. Stage 3 is what turns a reported
`agreesWith`/`checkVipr` pair into a proof term; `examples/mip_prop_demo.lean` does that
step by hand, and needs no solver. Usage is written up in `docs/TACTIC.md`.
-/

open LeanVIPR LeanVIPR.Tactic

/-- The knapsack of `examples/uns_knapsack.mps`: `6x + 10y + 15z = 23`, `x + y + z ≥ 1`,
integer `x ∈ [0,3]`, `y ∈ [0,2]`, `z ∈ [0,1]`. Infeasible, and the problem the
checked-in certificate is about. -/
def knapsack : Mip where
  vars := #[{ name := "x", isInt := true, lo := some 0, hi := some 3 },
            { name := "y", isInt := true, lo := some 0, hi := some 2 },
            { name := "z", isInt := true, lo := some 0, hi := some 1 }]
  objSense := .min
  obj := []
  rows := #[{ name := "c0", sense := 'E', rhs := 23,
              form := [⟨0, 6⟩, ⟨1, 10⟩, ⟨2, 15⟩] },
            { name := "c1", sense := 'G', rhs := 1,
              form := [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] }]

/-- The same knapsack with the right-hand side moved to 25, which `10 + 15` attains. The
certificate comes back `RTP range`, so no infeasibility conclusion is available — the
report must say so rather than the tactic later discovering it. -/
def knapsackFeasible : Mip :=
  { knapsack with rows := knapsack.rows.set! 0 { knapsack.rows[0]! with rhs := 25 } }

/-- Infeasible only if `1/2` survives the round trip to the solver and back; this is the
problem `probeBinary` uses. -/
def half : Mip := probeMip

/-! ## Stage 1: the driver, in plain `IO` -/

#eval show IO Unit from do
  match ← findScip {} with
  | .error e => IO.println e.message
  | .ok binary => IO.println s!"probe passed: {binary}"

#eval show IO Unit from do
  match ← runScip knapsack with
  | .error e => IO.println e.message
  | .ok r =>
    IO.println r.summary
    if !r.provesInfeasible then throw (IO.userError "expected an infeasibility result")

#eval show IO Unit from do
  match ← runScip knapsackFeasible with
  | .error e => IO.println e.message
  | .ok r =>
    IO.println r.summary
    if r.provesInfeasible then throw (IO.userError "expected no infeasibility result")

/-! ## Stage 2: the same thing from a command -/

#mip_scip knapsack

#mip_scip half

#mip_scip knapsackFeasible

-- options, in Lean's configuration syntax: the `.mps` and `.vipr` are kept in `dir`
#mip_scip (dir := "/tmp/leanvipr-mip-smoke") (timeout := 60) knapsack
