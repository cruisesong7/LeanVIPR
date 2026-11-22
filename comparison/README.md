# Comparison harness

Competing Lean tactics, each in its own Lake project so it can pin its own toolchain.
LeanVIPR is on `v4.35.0`; `leanprover/lp` is on `v4.33.1`, and Lean minor versions are not
interchangeable, so a single workspace cannot hold both. Each subdirectory is therefore a
standalone project, invisible to the root `lake build`.

| directory | tool | toolchain | oracle |
|---|---|---|---|
| `lp/` | `leanprover/lp` — `lp` / `maximize` tactics | `v4.33.1` | SoPlex, out-of-process via the JSON backend |

`omega` and `linarith` need no project of their own: they ship with Lean and mathlib, which
LeanVIPR already depends on, so those comparisons run against the root workspace.

## What `lp/` checks

`cd comparison/lp && lake build`, with a `soplex` binary on `PATH`. A green build means
every assertion held; the failures are pinned with `#guard_msgs`, so a future `lp` that
closes one of them breaks the build rather than going unnoticed.

| file | shows |
|---|---|
| `LpCompare.lean` | `lp` closes what a Farkas argument reaches, over `Rat` and `Int`, and not the knapsack or `2x = 1` over `Int`, whose LP relaxations are feasible |
| `LpIndicator.lean` | on the indicator example of `docs/TACTIC.md`, `maximize` certifies 30, or 150/7 with big-M written by hand, where the optimum is 19; over `Int`, `lp` still misses 19 by 17/7 |

## Why the JSON backend and not the FFI one

`lp`'s default backend links a vendored SoPlex through C++ FFI. With Lean `v4.33.1` on macOS
that link can fail: the bundled `ld64.lld` cannot parse the SDK's `.tbd` files (`unknown
architecture`). The failure is environmental rather than a bug in `lp`: its pure-Lean side
compiles, and LeanVIPR's `v4.35.0` links against the same SDK.

`lp-backend-soplex-json` avoids the problem by design — "no GMP, no Boost, no SoPlex
headers" in the build graph. It spawns a stock `soplex` binary and speaks JSON over stdio,
so `brew install soplex` is the only prerequisite.
