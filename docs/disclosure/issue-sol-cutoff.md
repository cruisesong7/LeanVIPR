**Title:** `{ sol }` cutoff is wrong for maximization, and the claimed dual bound is not checked against the incumbent

### Summary

Two problems in the handling of `{ sol }` derivations let `viprchk` and `viprchk_parallel` verify wrong optimal-value ranges:

1. For a **maximization** problem the cutoff row is still `OBJ ≤ best` (the code requires sense `L`). Any feasible solution can then be "proved" optimal. Conversely, the correct row `OBJ ≥ best` is rejected.
2. With an **integral objective** the cutoff is `OBJ ≤ best − 1`, but the claimed lower bound (for `min`) is never compared with `best`. A certificate can therefore prove a lower bound above the value of a known solution.

Both are in `case SOL` of the derivation loop: `code/viprchk.cpp:1078` and `code/viprchk_parallel.cpp:1099` on `master` (`99eec19`), and both are still present in #25 (`b0e56a5`). We found them by differential testing against LeanVIPR, a VIPR checker whose soundness is proved in Lean 4.

### Reproducer 1: maximization

`max x` subject to `0 ≤ x ≤ 2`, with `x` continuous. The optimum is 2.

```
VER 1.0
VAR 1 x
INT 0
OBJ max 1 0 1
CON 2 0
c1 G 0 1 0 1
c2 L 2 1 0 1
RTP range 0 0
SOL 1
s1 0
DER 1
d1 L 0 OBJ { sol } -1
```

```
$ ./viprchk max_sol_direction.vipr
...
Successfully verified optimal value range [0, 0].
```

The solution `x = 0` supports the lower bound 0, and `d1` supplies the upper bound `OBJ ≤ 0` from that same solution. For maximization a known solution only shows `OBJ ≥ 0`.

The correct certificate for this kind of problem is rejected. For `max x` subject to `0 ≤ x ≤ 1`:

```
VER 1.0
VAR 1
x
INT 0
OBJ max
1 0 1
CON 2 0
C0 L 1 1 0 1
C1 G 0 1 0 1
RTP range 1 1
SOL 1
opt 1 0 1
DER 2
D0 G 1 OBJ { sol } -1
D1 L 1 OBJ { lin 1 0 1 } -1
```

```
$ ./viprchk max_range.vipr
...
Cutoff bound should have sense 'L'
Verification failed.
```

### Reproducer 2: integral cutoff

`min x` subject to `x ≥ 5`, with `x` integer. The optimum is 5.

```
VER 1.0
VAR 1 x
INT 1 0
OBJ min 1 0 1
CON 1 0
c1 G 5 1 0 1
RTP range 100 100
SOL 1
s1 1 0 5
DER 2
d1 L 4 OBJ { sol } -1
d2 G 100 OBJ { lin 2 0 96 1 -95 } -1
```

```
$ ./viprchk cutoff_false_lb.vipr
...
Successfully verified optimal value range [100, 100].
```

`d1` is the cutoff `x ≤ 4` (best − 1). `d2` is a valid combination `96·(x ≥ 5) − 95·(x ≤ 4)`, giving `x ≥ 100`. The cutoff only describes solutions strictly better than the incumbent, so a bound derived from it is valid for the problem only if it does not exceed the incumbent's value 5; that is not checked. (`viprchk_parallel` additionally accepts an absurd final row in this situation, for example `0 ≥ 1` derived from `x ≤ 4` and `x ≥ 5`.)

### Possible fix

The spec lists `{ sol }` without defining it, so the intended semantics is your call. One option:

- for maximization, require sense `G` and use the cutoff `OBJ ≥ best` (or `best + 1` for an integral objective);
- when solutions are present, reject a claimed lower bound above `best` (minimization) or a claimed upper bound below `best` (maximization). Such a claim contradicts the listed solution, so this check is valid with or without cutoff rows.

It may also help to document `{ sol }` in the specification.
