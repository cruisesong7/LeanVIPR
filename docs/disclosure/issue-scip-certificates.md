# Exact mode: VIPR certificates that `viprchk` can't verify, on small models SCIP solves correctly

Hi all,

We've been checking exact SCIP's VIPR certificates with `viprchk` and with [LeanVIPR](https://github.com/cruisesong7/LeanVIPR), a VIPR checker we verified in Lean. SCIP's answers were correct every time, but a fair number of certificates don't actually prove them. Details and small reproducers are below.

**Versions:** SCIP 10.1.0 (official macOS arm64 release, `c8e5737a84`), also reproduced on 10.0.1 and 10.0.3. VIPR `99eec19`, using `viprcomp --soplex=on` first for certificates with `lin weak`.

**What we ran:** 847 models in exact mode, once with default settings and once with `set presolving maxrounds 0`. The models were 800 small random MILPs (general, big-M and knapsack), 26 ALU and MIPLIB 3.0 problems, and SCIP's own `check/instances/MIPEX` under its three `exact-*` settings files. Results on 10.1.0:

| # | What goes wrong | presolving off | default |
|---|---|---|---|
| 1 | No row proves the objective bound | 125 | 0 |
| 2 | The `SOL` solution misses the claimed optimum, or breaks the certificate's own bounds | 9 | 4 |
| 3 | A `lin weak` row that `viprcomp` can't complete | 4 | 1 |
| 4 | An `RTP infeas` certificate that never derives an absurdity | 1 | 0 |
| 5 | A `DualBound` row with `+infinity` multipliers | 0 | 1 |
| 6 | No `.vipr` file at all (see the questions below) | 0 | 472 |

Every run used `scip -c "set exact enable TRUE" [-c "set presolving maxrounds 0"] -c "set certificate filename <abs path>" -c "read <model>" -c "optimize" -c "quit"`.

## 1. No objective bound when propagation alone closes the gap

```
Maximize
 obj: x1 + 4 x2 + x3
Subject To
 c0: 4 x1 - x3 <= 5
Bounds
 0 <= x1 <= 3
 0 <= x2 <= 3
 0 <= x3 <= 5
General
 x2 x3
End
```

With presolving off, SCIP reports the optimum 39/2 correctly. The certificate has only propagation rows bounding `x1`, and nothing that bounds the objective:

```
ACT_L7 G -10 1 2 -4 { lin 2 0 -1 4 -1 } -1
ACT_L8 L 5/2 1 2 1 { lin 1 7 -1/4 } -1
GlobalBound_9 L 5/2 1 2 1 { lin 1 8 1 } -1 global
```

`viprchk` reports `Failed to derive lower bound`. A normal range certificate ends with a `DualBound_k ... OBJ` row; all 125 of these have none, and end in a `GlobalBound` row instead. With a one-variable objective, a propagation row can happen to equal the bound, but it's written with explicit coefficients rather than `OBJ`, so `viprchk` still rejects it. One such certificate (`min -x` s.t. `z >= 1`, `x + 4z <= 5`, `0 <= x <= 5`, `z` binary) has a DER section that is byte-identical across 10.0.1, 10.0.3 and 10.1.0.

## 2. A `SOL` solution that doesn't support the claim

- **Presolving off (model 1 below):** the exact optimum is −76/3, and `DualBound_19 G -76/3` proves it exactly. But `SOL` writes `x5 = 6004799503160661/18014398509481984`, a floating-point approximation of 1/3. `viprchk`: `Best objective values (-114091190560052565/4503599627370496) exceeds upper bound (-76/3)`.
- **Default settings (model 2 below):** presolve tightens `x0 ≤ 2`, which it can because `x0` has objective coefficient 0, but `SOL` still writes `x0 = 5/2`. `viprchk`: `Constraint 7 not satisfied`.

<details><summary>Models 1 and 2 (MPS)</summary>

```
NAME model
OBJSENSE
    MAX
ROWS
 N obj
 G c0
 L c1
 G c2
 L c3
COLUMNS
    x0 obj -3
    x0 c1 2
    x0 c2 -3
    x0 c3 2
    MARKER 'MARKER' 'INTORG'
    x1 obj -1
    x1 c1 -2
    x1 c2 1
    x2 obj -1
    x2 c1 5
    x3 obj 0
    x3 c0 1
    x3 c1 1
    x3 c2 5
    x3 c3 1
    x4 obj 4
    x4 c0 -2
    x4 c1 -1
    x4 c3 -2
    MARKER 'MARKER' 'INTEND'
    x5 obj 4
    x5 c0 -3
    x5 c1 2
    x5 c3 -3
    MARKER 'MARKER' 'INTORG'
    x6 obj 1
    x6 c1 2
    x6 c3 -2
    MARKER 'MARKER' 'INTEND'
RHS
    RHS c0 -10
    RHS c1 28
    RHS c3 -9
BOUNDS
 LO BND x0 0
 UP BND x0 2
 LO BND x1 0
 UP BND x1 1
 LO BND x2 0
 UP BND x2 6
 LO BND x3 0
 UP BND x3 1
 LO BND x4 0
 UP BND x4 5
 LO BND x5 0
 UP BND x5 1
 LO BND x6 0
 UP BND x6 4
ENDATA
```

```
NAME model
OBJSENSE
    MAX
ROWS
 N obj
 G c0
 G c1
 L c2
 L c3
 L c4
COLUMNS
    x0 obj 0
    x0 c2 4
    x0 c3 -5
    x1 obj -1
    x1 c0 -3
    x1 c1 -2
    x1 c2 -5
    x1 c3 5
    x1 c4 1
    MARKER 'MARKER' 'INTORG'
    x2 obj 5
    x2 c1 5
    x2 c2 -5
    x2 c3 2
    x2 c4 -1
    MARKER 'MARKER' 'INTEND'
RHS
    RHS c0 -3
    RHS c1 8
    RHS c2 -11
    RHS c3 5
BOUNDS
 LO BND x0 0
 UP BND x0 5
 LO BND x1 0
 UP BND x1 3
 LO BND x2 0
 UP BND x2 5
ENDATA
```
</details>

## 3. `lin weak` rows that can't be completed

This happens on your own `check/instances/MIPEX/egout.cip` with presolving off, under all three `exact-*` settings, and on the ALU instance `alu4_9` under both settings. `viprcomp --soplex=on` reports `Failed to complete derivation AggrRow_1398` for egout and `L29307_gom192_s55` for alu4_9. In `AggrRow_1398`, the stated right-hand side is tighter than its combination supports, by 169/(54975581388800 · 131072). It looks like #248, but it's still there with VIPR `99eec19`.

## 4. An infeasibility certificate without an absurdity

On `alu6_2` (infeasible) with presolving off, SCIP reports `problem is solved [infeasible]` and writes `RTP infeas`. But the last row is `UnsplitNode1_10712 G 223 OBJ { uns ... }`, and the `0 >= 1` rows appear only under assumptions. After `viprcomp`, `viprchk` prints `Proved: ... >= 223 Instead of:` and then segfaults (exit 139).

## 5. Infinite multipliers

On `check/instances/MIPEX/misc03p1.zpl` with `exact-exactlp`, default presolving and a 60 s time limit, the certificate has `DualBound_65126 G 0 OBJ { lin 256 96 +infinity 98 +infinity ... }`: all 256 multipliers are `+infinity`. This one depends on the time limit.

## Questions about default presolving

1. **No certificate when presolving solves the problem.** The log says `storing certificate information in file <x.vipr>` and later `closing certificate file`, but `x.vipr` is never created. Only `x.vipr_ori` exists, with `DER 0` and `RTP range -inf <primal>`. For the six infeasible ALU instances among our 26 (`alu4_3`, `alu4_5`, `alu5_3`, `alu5_5`, `alu6_3`, `alu7_5`), it says `RTP range -inf inf`, so the reported infeasibility has no certificate. Is this intended?
2. **The original problem's bound isn't certified.** When presolving doesn't solve the problem, the main certificate describes the presolved problem. For `alu4_9` that's 172 variables instead of 291, and `RTP range 1192 1192` against the reported optimum 1224, so the objective offset is dropped. Meanwhile `.vipr_ori` only claims `-inf 1224`. Neither file certifies the original problem's dual bound. Is the link between the two meant to be covered somewhere else?

## One more: rows after the final bound

The spec says the last DER row must dominate `OBJ >= lb`. In 12 runs with presolving off (3 with default settings), SCIP writes the exact bound and then a weaker one after it, for example on this two-variable LP:

```
DualBound_10 G -89/5 OBJ { lin 2 4 -3 0 -1/5 } -1
DualBound_11 G -5010254585449677/281474976710656 OBJ { lin 2 4 -3 8 -1 } -1
```

`viprchk` accepts these through its `OBJ` early exit (`viprchk.cpp:1129`), but a checker that follows the spec rejects them. Time-limited runs do the same thing with Gomory cuts written after the last `DualBound`. Which behavior is intended, the spec's last-row rule or `viprchk`'s? If it's the spec's, one easy fix would be for SCIP to end every range certificate with a final `DualBound ... OBJ` row restating the proven bound.

We're happy to share all the models, certificates and scripts. 
