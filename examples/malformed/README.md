# Well-formedness fixtures

Minimal certificates that are syntactically readable but violate a condition of
`LeanVIPR.Parser.IsValid`, so `viprcheck` reports a parse error rather than a
verdict. One file per condition, each as small as the condition allows, and each
containing nothing but the structure under test.

These are the reproducible evidence for the conditions `IsValid` states.
`validateVipr_eq_ok_iff` proves the validator decides exactly `IsValid`, so a
condition without a fixture is a claim with nothing to run.

| File | Condition violated | Expected |
|---|---|---|
| `forward_reason_ref.vipr` | `ReasonRefsOk` — `d1` cites constraint 2, but only `CON` row 0 exists where it is cited | parse error, exit `1` |

Run one:

```bash
lake exe viprcheck examples/malformed/forward_reason_ref.vipr   # exit 1
```

An out-of-range reference has no denotation: `finalUseHint` would resolve it with
`(v.ders.getD (k - v.cons.size) default).idx`, so the certificate would denote a
problem containing a row that was never written. The checker separately refuses to
replay such a reference, so soundness never rested on this — what rests on it is
that an accepted certificate denotes one problem.
