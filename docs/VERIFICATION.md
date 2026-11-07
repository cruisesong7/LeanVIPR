# What is proved, and what is trusted

This is the verification story: the boundary of the formal result, and what the
parser's correctness theorems say. For how to run the checker see the
[README](../README.md); for timings see
[`benchmarks/README.md`](../benchmarks/README.md).

## What is trusted

Relative to the emitted certificate AST, trusted: the Lean kernel and the small
definitions of “satisfies” and “infeasible”. Not trusted: SCIP, certificate replay
in the compiled CLI, and proof generation. The generated theorem is checked with
`decide +kernel`, not `native_decide`, and `ACCEPT` additionally requires its
reported axioms to be among `propext`, `Classical.choice`, and `Quot.sound`.

Two pieces of machinery in the default path are deliberately outside the trusted
set, because a theorem covers each of them:

- **The slicer.** `sliceVipr` is an untrusted heuristic. Nothing is taken on its
  word: `checkViprSlice_sound` requires the slice to carry the same `RTP` and the
  same integer variables and to have rows that are a sublist of the original's,
  and all three are re-tested at run time. A slice the checker rejects falls back
  to complete replay rather than becoming a rejection.
- **The task count.** `checkViprPar_eq` proves the parallel replay returns what
  the sequential one returns for every value of `VIPRCHECK_TASKS`, so the split
  cannot change a verdict. The proof needs no reasoning about concurrency:
  `Task.spawn fn` is `{ get := fn () }` in Lean's logic, so the parallelism is an
  evaluation strategy the logic cannot observe.

Neither is a soundness boundary and neither adds an axiom. Parallelism does,
however, widen the *runtime* trusted base, and that deserves saying plainly.

Native mode already trusts the Lean compiler and runtime to execute a pure
function faithfully. Running the replay across tasks adds Lean's task scheduler,
its multi-threaded reference counting, and the memory model under which worker
threads observe the shared pool. Those are not covered by any theorem here;
`checkViprPar_eq` is a statement about pure functions, and it would still hold if
the scheduler were wrong. Concurrency bugs in a language runtime are a real class
of bug, and this takes a dependency on that code not having any.

Two things bound it. Kernel mode is untouched: the kernel unfolds `Task.spawn fn`
to `{ get := fn () }` and reduces sequentially, so no thread is involved in
producing a machine-checked theorem. And `VIPRCHECK_TASKS=1` yields a single chunk,
which `parAll` evaluates directly instead of spawning — so the scheduler, the
atomic reference counting and the memory model are left out of the run entirely,
not merely reduced to one thread. If you want the narrowest runtime base from the
compiled checker, that is the setting.

For `RTP range`, `Vipr.ClaimValid` states that every listed solution is feasible,
the primal witness bound holds, and the derived objective bound holds at every
feasible point (minimization: `lb ≤ obj(x)` for all feasible `x`). The classical
statement that every optimal value lies in `[lb, ub]` is the corollary
`Vipr.ClaimValid.optimal_within`.

## Parser verification

The reader is verified against an independent specification rather than trusted. That
specification is one file — [`Spec/Grammar.lean`](../LeanVIPR/Spec/Syntax/Grammar.lean),
about 450 lines — stated without reference to any parser function:

| section of `Spec/Grammar.lean` | covers |
|---|---|
| `IsNumValue` | a numeric token to an exact rational |
| `IsTokenization` | characters to tokens |
| `IsVipr`, `IsViprText` | tokens to a certificate |
| `IsValid` | when a certificate denotes a usable problem |

and the reader is proved to agree with it in both directions:

```lean
theorem parseVipr_eq_ok_iff : parseVipr content = .ok v ↔
                                (IsViprText content.toList v ∧ IsValid v)
```

Both sides of that `↔` matter. **Soundness** closes a gap replay cannot:
`checkVipr_sound` proves a claim about the AST it is handed, so a token read as the
wrong rational would let it establish a true claim about a *different* mixed-integer
problem. **Completeness** is what makes a rejection a statement about the file rather
than possibly an artefact of a narrow reader. `isVipr_unique`, `isTokenization_unique`
and `isNumValue_unique` record that no part of the grammar is ambiguous.

The specification contains no implementation function. Nothing on the right-hand side
of that `↔` reduces to `wsTokens`, `parseViprToks` or `validateVipr`; it mentions only
that one grammar file and the AST type definitions, which is checked mechanically. That is the property that makes
the theorem worth proving — a correctness statement phrased in terms of `wsTokens`
would take the tokenizer's own output as the definition of tokenization and so could
not detect a tokenizer that dropped, merged or truncated tokens.

One limit is worth naming because the grammar states it rather than hiding it. VIPR
v1.1 leaves the `DER` scope keyword `global`/`local` optional *and* unbracketed, so the
format is only unambiguous under maximal munch: a derivation *named* `global` or
`local` directly after a flagless row would have its name read as that row's flag.
`IsDers` carries that side condition. Such a file is rejected rather than misread, so
this limits completeness only, and it is a property of the format — `viprchk` has the
same exposure.

What remains trusted is the per-run binding, not the reader. The theorems are about the
Lean functions; the artifact does not *kernel-check*, on each run, that the AST emitted
into the generated proof is the parse of the exact source bytes. The compiled CLI, the
AST printer, and the OS/file plumbing sit outside this result and are not included in
the benchmark below.

