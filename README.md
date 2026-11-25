# LeanVIPR

LeanVIPR checks the certificates that exact mixed-integer solvers write, with a checker
proved correct in Lean 4. A VIPR certificate claims that a problem is infeasible, or that
its optimum lies in a range, and gives the derivation. `viprcheck` re-derives the claim
in exact rational arithmetic and accepts only if it holds, so the solver that wrote the
certificate is not trusted.

LeanVIPR is:

- **Verified.** The checker is proved sound and complete against a specification of the
  VIPR proof system, which is written separately from the code.
- **Exact.** Every number is a rational; nothing is rounded.
- **Practical.** A compiled, parallel checker by default, and a theorem checked by
  Lean's kernel on request.

It also works the other way round: the `mip` tactic states a mixed-integer problem in
Lean, asks exact SCIP about it, and turns the certificate into a theorem.

## Build

```sh
lake exe cache get
lake build
```

[`elan`](https://github.com/leanprover/elan) installs the pinned toolchain. SCIP is not
needed to check a certificate.

## Check a certificate

```sh
lake exe viprcheck examples/uns_knapsack.vipr
```

This prints `NATIVE ACCEPT`. Exit codes: `0` accept, `1` usage or parse error, `2`
reject. For a theorem checked by Lean's kernel instead:

```sh
lake exe viprcheck --kernel-mode reconstruct examples/uns_knapsack.vipr
```

Every mode and option is in [`docs/CLI.md`](docs/CLI.md).

## Prove a mixed-integer fact in Lean

```lean
import LeanVIPRTactic

example (x y : ℤ) (h1 : 27 ≤ 11*x + 13*y) (h2 : 11*x + 13*y ≤ 45)
    (h3 : -10 ≤ 7*x - 9*y) (h4 : 7*x - 9*y ≤ 4) : False := by
  mip
```

`omega` cannot prove this one. `mip` needs a certifying exact SCIP;
[`docs/TACTIC.md`](docs/TACTIC.md) covers the setup, `mip_maximize`, and building from
saved certificates without a solver.

## Documentation

| Document | Contents |
|---|---|
| [`docs/CLI.md`](docs/CLI.md) | `viprcheck`'s modes, options and format coverage |
| [`docs/TACTIC.md`](docs/TACTIC.md) | the `mip` tactics |
| [`docs/VERIFICATION.md`](docs/VERIFICATION.md) | what is proved, and what is trusted |
| [`docs/LAYOUT.md`](docs/LAYOUT.md) | how the development is organized |
| [`benchmarks/README.md`](benchmarks/README.md) | the certificate corpus and measured results |
| [`docs/SCIP-SETUP.md`](docs/SCIP-SETUP.md) | building exact SCIP and writing certificates |
| [`examples/audit/`](examples/audit/README.md) | adversarial and edge-case certificates, including ones other checkers mishandle, and the [upstream reports](docs/disclosure/README.md) |

## License

Copyright 2026 the LeanVIPR contributors. Licensed under the Apache License, Version 2.0;
see [`LICENSE`](LICENSE).
