Thanks for this PR. We independently ran into the `rnd` issue while developing LeanVIPR, a VIPR checker whose soundness is proved in Lean 4, and can confirm the fix.

One extra regression test you may want to add: the same bug also lets `viprchk` verify a wrong optimal value, not just a false infeasibility claim.

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

The optimum is `1/2`, but `master` prints `Successfully verified optimal value range [1, 1].` Step `d1` rounds `x ≥ 1/2` up to `x ≥ 1`, which is only valid for integer `x`. With this PR the certificate is rejected.
