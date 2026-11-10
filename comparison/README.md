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

## Why the JSON backend and not the FFI one

`lp`'s default backend links a vendored SoPlex through C++ FFI. On this machine that build
fails at link time — Lean `v4.33.1`'s bundled `ld64.lld` cannot parse the installed macOS
SDK's `.tbd` files (`unknown architecture`). The failure is environmental rather than a bug
in `lp`: its entire pure-Lean side compiles, and our own `v4.35.0` links fine against the
same SDK.

`lp-backend-soplex-json` avoids the problem by design — "no GMP, no Boost, no SoPlex
headers" in the build graph. It spawns a stock `soplex` binary and speaks JSON over stdio,
so `brew install soplex` is the only prerequisite.
