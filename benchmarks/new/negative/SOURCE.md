# Forged and manipulated certificates

Hand-written VIPR v1.0 certificates from

> Kenan Wood, Runtian Zhou, Haoze Wu, Hammurabi Mendes, Jonad Pulaj.
> *Satisfiability Modulo Theories for Verifying MILP Certificates.*
> arXiv:2312.10420 (Examples 4 and 5, Appendix C).

Downloaded from the root of <https://github.com/hammurabi-mendes/vipr_checker> at
commit `b13c92d06ecdccffe1dd63442dcfe82ea7bee2dd`, then gzipped (`gzip -n`) so the
runner picks them up. The contents are unchanged.

| File | What it is | Paper's classification |
|---|---|---|
| `forged1.vipr.gz` | Claims optimum 1 for a MILP whose optimum is 2, via a derived row `x + y <= 1` justified by `{ sol }`. | invalid |
| `forged2.vipr.gz` | Claims range `[-inf, 0]` for an infeasible MILP with no solutions and no derivations. | invalid |
| `manipulated1.vipr.gz` | `paper_eg3.vipr` with one index of derivation `C8` changed. The paper reports that `viprchk` rejects it even though every derivation is sound, and that the SMT checker accepts it. | sound, but violates an index rule |

These files test checker soundness and spec conformance. They are not performance
benchmarks.

SHA-256 of the gzipped files:

```
fd23aa5dc1521366498a3775a5784b8eec916f52609f50b80515f96ec8296d55  forged1.vipr.gz
62934ad878174430080cd2bf1ea3d4f49bd2daf349a2a2c8a77234ffe89ed688  forged2.vipr.gz
69533f7de215db756f2cb3e38456a21d2785d7cc8e9f071252589163ca13bc68  manipulated1.vipr.gz
```
