# How the development is organized

```
LeanVIPR/
  Spec.lean       Spec/Syntax.lean      Syntax/     Ast  Grammar
                  Spec/Semantics.lean   Semantics/  LinCon  LinForm  Row  Lower
                                                    System  Claim  Completeness
  Impl.lean       Impl/Parser.lean      Parser/     Utils  Printer
                  Impl/Checker.lean     Checker/    Form  Rules  Solution
  Thm.lean        Thm/Parser.lean       Parser/     Tokens  Number  NumberLemmas
                                                    Certificate  CertificateLemmas
                                                    Valid  Printer
                  Thm/System.lean       System/     Sound  RuleSound  RuleComplete
                                                    LinForm  Row  Claim  Completeness
                  Thm/Checker.lean      Checker/    Sound  Complete  Parallel
LeanVIPRMain.lean    -- the `viprcheck` command line
LeanVIPRTactic.lean  LeanVIPRTactic/  Scip  Eval  Config  Command  Certify
                                      Reflect  Optimize  Roundtrip   -- the `mip` tactics
```

Three parts, and the division is the point of the development:

* **`Spec/`** — what a certificate is (`Syntax/`) and what it means (`Semantics/`).
  Nothing here refers to an executable function: no reader, no checker, no `Bool`, no
  `Except`. Accept these definitions and you know what `ACCEPT` means without reading
  the implementation.
* **`Impl/`** — the reader (`Parser/`) and the checker (`Checker/`). The only artifacts
  whose correctness is in question, and nothing here is trusted.
* **`Thm/`** — the proofs that `Impl` meets `Spec`, with one results file per layer
  (`Thm/Parser.lean`, `Thm/System.lean`, `Thm/Checker.lean`) beside the directory that
  proves it.

The dependency order is enforced, not just intended: `Spec/` imports nothing from
`Impl/` or `Thm/`, and `Impl/` imports only `Spec/`. So no correctness statement can be
satisfied by an implementation that merely agrees with itself.

Every directory has a header file beside it saying what is in it and what to read first,
so `Spec.lean`, `Spec/Syntax.lean` and `Spec/Semantics.lean` are each an index to the
directory of the same name.

`LeanVIPRTactic/` is a separate library target for the other direction: stating a
mixed-integer program *in Lean*, asking exact SCIP about it, and getting a theorem about
the problem you wrote. Nothing in `LeanVIPR` imports it, so the checker stays free of
metaprogramming, `IO` and any dependency on a solver being installed. Usage is
[`TACTIC.md`](TACTIC.md); the roadmap is [`TACTIC-TODO.md`](TACTIC-TODO.md).

Outside the Lean sources: `benchmarks/` holds the certificate corpus and its runners,
`comparison/` the harness that checks other Lean tactics' results, and `examples/audit/`
adversarial and edge-case certificates, including ones other checkers mishandle.
