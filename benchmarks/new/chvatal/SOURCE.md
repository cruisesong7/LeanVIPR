# Chvátal's conjecture certificates (n = 5, 6, 7)

Exact-SCIP VIPR v1.0 certificates from

> Leon Eifler, Ambros Gleixner, Jonad Pulaj. *A Safe Computational Framework for
> Integer Programming applied to Chvátal's Conjecture.* arXiv:1809.01572
> (ZIB-Report 18-49).

Downloaded unchanged from `certificates/` of
<https://github.com/leoneifler/ChvatalIP> at commit
`49d73526e413148811a3e6e1a594f0cc9ff89a1e`.

| File | VAR | CON | DER | RTP |
|---|---:|---:|---:|---|
| `redprob_5.vipr.gz` | 63 | 919 | 4 | range 0 0 |
| `redprob_6.vipr.gz` | 127 | 2801 | 17 | range 0 0 |
| `redprob_7.vipr.gz` | 255 | 8507 | 18153 | range 0 0 |

All three are complete (no `lin weak`).

SHA-256:

```
154c93d1b662cbc44fa73fcbfb2f63394354af40cf3a3e8a015f734ad0415085  redprob_5.vipr.gz
64f25cb66e28d6d48444f638ca54af8ced9b07eb842128bc444221821423d2f0  redprob_6.vipr.gz
fb459c1ef6326bd09c179de75c0154fd2526de029aca73c1d6e6836c1e8c41c1  redprob_7.vipr.gz
```
