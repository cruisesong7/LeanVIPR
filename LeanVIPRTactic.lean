module

public import LeanVIPR

@[expose] public section

/-!
# `mip`: discharge a mixed-integer goal with exact SCIP

A separate library target from `LeanVIPR`, not a separate repository — see `lakefile.toml`
for why. Nothing in the checker imports this, so the trusted artifact stays free of
metaprogramming, `IO` and any dependency on a solver being installed.

Scaffold; the plan is `docs/TACTIC-TODO.md`. The intended shape:

```
goal : Prop
  │  reflect                     (metacode, untrusted — may fail, cannot lie)
  ▼
m : Mip  ──encodeMps──▶  .mps  ──exact SCIP──▶  .vipr  ──parse──▶  v : Vipr
  │                                                                  │
  └───────────── agreesWith m v  (verified) ─────────────────────────┘
                              │  checkVipr v  (verified)
                              ▼
                      Mip.Infeasible m  ⟹  the original goal
```

Only the two `Bool`s matter: `pipeline_infeasible` depends on `agreesWith m v` and
`checkVipr v`, both decided against the reified `Mip` rather than against any text. So the
reflection, the emitter, the file, the solver and the parser are all untrusted — each can
make the tactic *fail*, none can make it prove something false. This is the same division
`Trestle` and `bv_decide` use when they ship a formula to an external solver: the returned
proof is checked against the reified formula, so the transport needs no verifying.

The declarations below name the dependency surface the tactic will stand on, so a break
upstream shows up here rather than three steps into the tactic.
-/

namespace LeanVIPR.Tactic

open LeanVIPR LeanVIPR.Impl.Encoder

example : Mip → String := encodeMps
example : Mip → Parser.Vipr → Bool := agreesWith
example : Mip → Parser.Vipr → Bool := sameProblemAs

end LeanVIPR.Tactic
