# Exact SCIP emits a range certificate whose last row does not prove its claim

Found 2026-11-19 while testing linearized indicator models. Reported upstream as
[scipopt/scip#305](https://github.com/scipopt/scip/issues/305), with the measurements in
[`freq/`](#how-often-freq).

- Solver: exact SCIP 10.0.1 (`~/scip-exact/scipoptsuite-10.0.1/build/bin/scip`),
  `set exact enable TRUE`, input `ind_bigM.lp` (min -x, x in [0,5], z binary,
  z >= 1, x + 4z <= 5). SCIP reports the optimum -1 correctly.
- Certificate `ind_bigM.vipr`: row 9 derives the objective bound `-x >= -1`;
  SCIP then appends two global-bound rows, ending with `x <= 1`.
- VIPR spec (v1.0 lines 234-235, v1.1 lines 242-243): the last constraint must
  dominate `OBJ >= lb`. Domination requires identical coefficients, so `x <= 1`
  does not dominate `-x >= -1`.
- viprchk (scipopt/vipr 99eec19): rejects, "Failed to derive lower bound.
  Proved: t_x <= 1 Instead of: -t_x >= -1". Its early exit (viprchk.cpp:1129)
  fires only for rows written with the literal `OBJ` keyword; row 9 is written
  as explicit coefficients.
- LeanVIPR: rejected it at first (`FinalValid` -> `Dominates`). Since #9 it accepts any
  closed row that proves the claim, and warns that the proving row is not the last.

Every derivation step is arithmetically valid; the claim is true. The fault is
in SCIP's certificate output, not in the checkers.

## Versions (tested 2026-11-19)

| SCIP | default settings | `set presolving maxrounds 0` |
|---|---|---|
| 10.0.1 (exact build, `~/scip-exact`) | buggy certificate | buggy certificate |
| 10.0.3 (Homebrew) | presolve solves it; no `.vipr` written | buggy certificate, DER identical to 10.0.1 |
| 10.1.0 (official macOS arm64 release, commit c8e5737a84, run from a scratch dir) | presolve solves it; no `.vipr` written | buggy certificate, DER identical to 10.0.1 |

Diagnosis: a normal range certificate ends with a `DualBound_k ... OBJ` row (the
McCormick control does, and both checkers accept it). This one has no `DualBound`
row at all: the bound comes from an activity-propagation row (`ACT_L9`) written
with explicit coefficients, followed by `GlobalBound` rows.

Side observation, raised in #305 as a question about default presolving: in the
default 10.0.3/10.1.0 runs the log says it stored and closed the certificate, but
only `<name>_ori` exists. Its bounds are presolve's (`x` in [1,1]; the input has
[0,5]), it has `DER 0`, and it claims only `RTP range -inf -1`. So the reported
optimum carries no dual-bound certificate. Files: `scip-10.1.0/`.

## How often (`freq/`)

`freq/freq.py` solves 847 models (SCIP's own exact-mode test instances, the 26
problems behind `benchmarks/{infeas,range}`, and seeded random families) with exact
SCIP, under default settings and with presolving off, and checks every certificate
with LeanVIPR and with upstream `viprchk`. The results are the `results-*.csv` files,
one per SCIP version and LeanVIPR revision; #305 summarizes them.

To regenerate them you need an exact SCIP build (`docs/SCIP-SETUP.md`) and
`viprchk`/`viprcomp` built from [scipopt/vipr](https://github.com/scipopt/vipr) in
`freq/bin/`. The models (`freq/models/`), the certificates (`freq/work-*/`) and the
run logs are written by the script and not committed:

```bash
python3 examples/audit/scip-final-row/freq/freq.py --scip /path/to/exact/scip --label 10.1.0
```
