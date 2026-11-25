**Title:** `viprchk_parallel` accepts false claims that `viprchk` rejects

### Summary

`viprchk_parallel` differs from `viprchk` in four places that let it accept false claims. All four are on `master` (`99eec19`) and still present in #25 (`b0e56a5`). We found them by differential testing against LeanVIPR, a VIPR checker whose soundness is proved in Lean 4; `viprchk` rejects every example below.

### 1. A solution is checked against only one constraint

`processSOL`, `code/viprchk_parallel.cpp:870`:

```cpp
for( int j = 0; j < numberOfConstraints; ++j )
{
   if( !satisfies(constraint[i], solutionSpecified) )   // i is the solution index
```

Solution `i` is only checked against constraint `i`, so an infeasible solution is accepted as the primal witness. (`viprchk.cpp` has `constraint[j]`.) Example: `min x` subject to `x ≥ 0`, `x ≥ 2`; the optimum is 2, and the infeasible solution `x = 0` "proves" the range `[0, 0]`:

```
VER 1.0
VAR 1 x
INT 0
OBJ min 1 0 1
CON 2 0
C0 G 0 1 0 1
C1 G 2 1 0 1
RTP range 0 0
SOL 1
opt 1 0 0
DER 1
D1 G 0 OBJ { lin 1 0 1 } -1
```

### 2. A failed final check still exits with 0

In the final check of `parCheck_Der` (`code/viprchk_parallel.cpp:1205` and `:1217`), the failure branches print a message but leave `returnStatement` true. Example: the feasible problem `x ≥ 0` claimed infeasible, with no contradiction:

```
VER 1.0
VAR 1 x
INT 0
OBJ min 0
CON 1 0
c1 G 0 1 0 1
RTP infeas
SOL 0
DER 1
d1 G 0 1 0 1 { lin 1 0 1 } -1
```

```
$ ./viprchk_parallel trivial_infeas.vipr; echo $?
...
Failed to verify infeasibility.
...
0
```

The same happens after `Failed to derive lower bound.`. (For this file, sequential `viprchk` exits with a segmentation fault after printing the failure message, apparently while printing `relationToProve`, which is not set for `RTP infeas`.)

### 3. A primal bound without a solution is accepted

`processSOL` in `viprchk_parallel.cpp` lacks the branch of `viprchk.cpp:843` that reports `No solutions to prove primal bound.` Example: `min x` subject to `x ≥ 2`, claimed range `[0, 0]`, with no solution:

```
VER 1.0
VAR 1 x
INT 0
OBJ min 1 0 1
CON 1 0
C0 G 2 1 0 1
RTP range 0 0
SOL 0
DER 1
D1 G 0 OBJ { lin 1 0 1 } -1
```

### 4. `uns` drops assumptions of the second branch

In `canUnsplit` (`code/viprchk_parallel.cpp:1554–1558`), the assumptions of the second branch are added to the result only if they are already in it:

```cpp
for( auto it = asm2.begin(); it != asm2.end(); ++it ) {
   if( assumptionList.find(it->first) != assumptionList.end() ) {
      assumptionList[it->first] = true;
   }
}
```

`viprchk.cpp` takes the union. With the intersection, an assumption used only in the second branch disappears. Example: `0 ≤ x ≤ 5`, `x` integer (feasible). The first branch `x ≤ -1` is refuted honestly; the second branch `x ≥ 0` is "refuted" with the unjustified assumption `a3: x ≥ 10`, which the `uns` step then drops:

```
VER 1.0
VAR 1 x
INT 1 0
OBJ min 0
CON 2 0
c1 G 0 1 0 1
c2 L 5 1 0 1
RTP infeas
SOL 0
DER 6
a1 L -1 1 0 1 { asm } -1
d1 G 1 0 { lin 2 0 1 2 -1 } -1
a2 G 0 1 0 1 { asm } -1
a3 G 10 1 0 1 { asm } -1
d2 G 5 0 { lin 3 1 -3 4 1 5 2 } -1
u G 1 0 { uns 3 2 6 4 } -1
```

```
$ ./viprchk_parallel uns_drops_assumption.vipr
...
Successfully verified infeasibility.
```

`viprchk` reports `Final derived constraint contains undischarged assumptions` (`a3`).

### Possible fix

The attached patch (against `master`) changes `constraint[i]` to `constraint[j]`, adds the missing primal-bound check, sets `returnStatement = false` in both failure branches, and takes the union of the assumptions in `canUnsplit`. With it, the four examples are rejected, the files in `examples/` get the same verdicts as with `viprchk`, and all 26 certificates from our benchmark set (exact SCIP output for ALU and MIPLIB 3.0 instances, completed with `viprcomp`) are still accepted.

### Further differences

The patch does not make the two checkers agree. On 8,849 mutated certificates (derived from `examples/` and two ALU certificates), the patched `viprchk_parallel` and `viprchk` still give different verdicts on 581. The larger groups:

- about 250 range certificates that `viprchk` rejects with `Failed to derive lower bound.` (for example, ones whose final row is an absurdity, or with `DER 0`) and `viprchk_parallel` accepts;
- about 120 certificates that `viprchk` rejects with `Accessing trashed constraint` (a row used after its final-use index) and `viprchk_parallel` accepts;
- about 45 `uns` steps that `viprchk` rejects (`unsplit failed`) and `viprchk_parallel` accepts;
- about 140 certificates that `viprchk` accepts and `viprchk_parallel` rejects.

Apart from the `rnd` issue fixed in #24 (the patch is based on `master`), we have not found a further false claim among these, but we have not checked all of them. We can share the certificates if that helps.
