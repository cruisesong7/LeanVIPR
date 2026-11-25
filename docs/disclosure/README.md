# Upstream reports

Drafts of the bug reports and patches written for the VIPR checkers and exact SCIP,
from findings made while developing LeanVIPR. The reproducing certificates are in
[`examples/audit/`](../../examples/audit/README.md).

| File | About | Status |
|---|---|---|
| `issue-scip-certificates.md` | certificates from exact SCIP that `viprchk` cannot verify | filed, [scipopt/scip#305](https://github.com/scipopt/scip/issues/305) |
| `issue-sol-cutoff.md` | `viprchk`'s `{ sol }` cutoff is wrong for maximization | filed, [scipopt/vipr#26](https://github.com/scipopt/vipr/issues/26) |
| `issue-viprchk-parallel.md` | `viprchk_parallel` accepts false claims that `viprchk` rejects | filed, [scipopt/vipr#27](https://github.com/scipopt/vipr/issues/27) |
| `viprchk-parallel-fixes.patch` | fixes for the `viprchk_parallel` bugs | draft |
| `viprchk-round-issue.md`, `round-continuous.patch` | `viprchk` accepts `rnd` steps that round continuous variables, and a fix | draft; open upstream PRs #24 and #25 address the same bug |
| `pr24-comment.md` | an extra regression test for scipopt/vipr PR #24 | draft, not posted |
