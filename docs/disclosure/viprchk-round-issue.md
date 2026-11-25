**Title:** `viprchk` accepts `rnd` steps that round continuous variables (false acceptance)

### Summary

`Constraint::round()` checks that coefficients of *integer* variables are integral, but never checks that coefficients of *continuous* variables are zero. The specification requires both ("[…] is such that for j = 1, …, p, a_{i_j} is an integer and is nonzero only if i_j is an integer variable index", `cert_spec_v1_1.md`, *Rounding*). As a result, `viprchk` and `viprchk_parallel` accept certificates that "prove" false infeasibility and false optimal-value claims.

Affected: `code/viprchk.cpp` and `code/viprchk_parallel.cpp`, at least from `30f2951` through current `master` (`99eec19`).

### Reproducer 1: wrong optimal value

`min x` subject to `x ≥ 1/2`, with `x` continuous. The optimum is `1/2`, but `viprchk` verifies the range `[1, 1]`.

```
VER 1.0
VAR 1 x
INT 0
OBJ min 1 0 1
CON 1 0
c1 G 1/2 1 0 1
RTP range 1 1
SOL 1
s1 1 0 1
DER 1
d1 G 1 OBJ { rnd 1 0 1 } -1
```

```
$ ./viprchk false_optimum.vipr
...
Successfully verified optimal value range [1, 1].
$ echo $?
0
```

Step `d1` rounds `x ≥ 1/2` up to `x ≥ 1`, which is only valid if `x` is integer.

### Reproducer 2: false infeasibility

`x ≥ 1/2` and `x ≤ 1/2`, with `x` continuous; `x = 1/2` is feasible.

```
VER 1.0
VAR 1 x
INT 0
OBJ min 0
CON 2 0
c1 G 1/2 1 0 1
c2 L 1/2 1 0 1
RTP infeas
SOL 0
DER 2
d1 L 0 1 0 1 { rnd 1 1 1 } -1
d2 G 1/2 0 { lin 2 0 1 2 -1 } -1
```

```
$ ./viprchk false_infeas.vipr
...
Successfully verified infeasibility.
```

`d1` rounds `x ≤ 1/2` down to `x ≤ 0`; `d2` is then a valid combination giving `0 ≥ 1/2`. Fractional coefficients on continuous variables are accepted too (for example, rounding `x/2 ≤ 1/4` to `x/2 ≤ 0`). `viprchk_parallel` behaves identically.

### Cause

`code/viprchk.cpp:1634` (and `code/viprchk_parallel.cpp:1682`):

```cpp
for(auto & it : *_coefficients)
{
   auto j = it.first;
   auto a = it.second;

   if( isInt[j] )
   {   // needs to be an integer variable
      if( !isInteger(a) ) { ... return false; }
   }
   // no check for continuous variables: a != 0 is accepted
}
```

### Proposed fix

Reject a nonzero coefficient on a continuous variable (same change in both files; the patch is attached):

```diff
       }
+      else if( a != 0 )
+      {   // a continuous variable must not appear in a rounded constraint
+         cerr << "Coefficient of continuous variable with index "
+              << j << " is nonzero" << endl;
+         returnStatement = false;
+         goto TERMINATE;
+      }
    }
```

Testing the patch on `master` (`99eec19`):

- all three counterexamples are rejected by both `viprchk` and `viprchk_parallel`;
- `examples/paper_eg3.vipr` is still accepted;
- 26 certificates produced by exact SCIP (20 infeasibility instances from the ALU suite, 6 objective-range instances from ALU/MIPLIB 3.0), completed with `viprcomp --soplex=off`, get the same verdict as before (all accepted).

So certificates produced by SCIP should be unaffected. The risk is a faulty certificate producer (for example, a cut derivation that leaves a continuous term after aggregation), which `viprchk` would then confirm.

### How we found it

We found it while developing an independent VIPR checker whose soundness is proved in Lean 4; that checker rejects all three certificates. We are happy to share it or submit the fix as a pull request.
