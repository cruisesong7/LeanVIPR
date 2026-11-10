# A Lean problem in, a Lean theorem out

Branch `scip-encoder`. Goal: turn LeanVIPR from "this certificate is valid" into "this
mixed-integer program, as written in Lean, is infeasible / has its optimum in `[lb, ub]`",
with exact SCIP as a fully untrusted oracle.

**What is and is not proved.** The soundness-critical half is complete: `pipeline_infeasible`,
the objective-bound results and `pipeline_optimal_*` are proved, with no `sorry`, no added
axiom and no `native_decide`. The *emitter* is not yet proved correct — `Thm/Encoder/Emit.lean`
proves the tokenization half of its round trip and the denotation half is open, so
`mpsRoundTrip` is a statement in this document rather than a theorem in Lean. That gap is
deliberate and bounded: no pipeline theorem mentions `encodeMps`, so a faulty emitter makes
the agreement check *reject* rather than produce a wrong theorem. Calling this a "verified
encoder" would overstate it; the verified thing is the agreement between a certificate and
the problem we posed.

## The gap this closes

Today the pipeline is

```
hand-written .mps  →  exact SCIP 10  →  .vipr  →  viprcheck (verified)  →  ACCEPT
```

and `ACCEPT` gives `Vipr.ClaimValid v` — a statement about the problem written in the
**certificate's own** `CON`/`OBJ`/`INT` sections. Two links are unverified, and they are
different kinds of unverified:

1. **The `.mps` is hand-written.** Nothing says the file says what we meant.
2. **Nothing ties the returned certificate to the problem we posed.** SCIP could return
   a perfectly valid certificate for a *different* problem and `viprcheck` would accept
   it, correctly.

Link 2 is the soundness-critical one, and it is not hypothetical: on
`examples/uns_knapsack.mps` SCIP declares variables `x y z` and emits a certificate over
`t_y t_x t_z` — renamed *and* permuted. Any argument that goes "we encoded `m`, so the
certificate is about `m`" has to pass through SCIP's own bookkeeping, which is exactly
what we are refusing to trust.

So the design does not try to trust the solver's faithfulness. It **re-derives** the
connection from the certificate text:

```
Lean Mip  ──encode──▶  .mps  ──SCIP (untrusted)──▶  .vipr  ──parse──▶  Vipr
   │                                                                     │
   └──────────────────── agreement check (verified) ─────────────────────┘
                                      │
                          viprcheck ACCEPT + agreement
                                      ▼
                        Mip.Infeasible m  /  Mip.OptimumWithin m lb ub
```

The agreement check reads the certificate's variable names, integrality marks and rows,
recovers the renaming `π` against the `Mip`'s own names, and decides whether the
certificate's problem *is* `m` up to `π`. The encoder's correctness is then not
soundness-critical — it is what stops the pipeline from failing spuriously, and what
makes the claim honest (the file we hand SCIP is the problem we state the theorem about).
Both are worth having; they buy different things, and the plan below keeps them separate
so that is visible.

## Why MPS and not CPLEX LP

There is no single standard format. `display readers` on the exact build lists about
twenty-five; the ones that can carry a MIP are `mps` (IBM's), `lp` (IBM CPLEX's), `cip`
(SCIP's own), and a tail of niche ones — `osil`, `pip`, `opb`, `fzn`, `cnf`, `gms`, `rlp`,
the `smps` family. MPS is the closest thing to a lingua franca, being what MIPLIB
distributes, but it is a de facto convention rather than a specification.

**Correction to an earlier version of this document.** It claimed the exact LP path "has
no such guarantee" of lossless rational parsing, and that this was the reason to choose
MPS. That is false, and measured so. On `max (1/3)x + y` subject to
`(2/5)x + y ≤ 7/4`, `y ≤ 1/6` — fractions in the objective, in a constraint coefficient,
in a right-hand side and in a bound — the exact build reports
`Exact Primal Bound : 107/72` from the **LP** file and the identical `107/72` from the
equivalent MPS file. Both are the hand-computed answer. SCIP's own `cip` writer also
round-trips `<= 1/2` exactly, tagging the row `[exactlinear]`. So all three formats are
lossless under `-DEXACTSOLVE=ON`, and rational fidelity does not distinguish them.

**The real reason is that MPS is far cheaper to formalize.** `Spec/Syntax/Mps.lean` has to
be a grammar we can state `mpsRoundTrip` against, and MPS is a rigid line-and-section
format: fixed section keywords, a fixed field count per line, one datum per field. CPLEX
LP is an *expression language* — implicit coefficients, optional signs, free term
ordering, continuation lines, ranged constraints written `a <= expr <= b`, and relational
operators in either direction. Formalizing that grammar and proving a round trip against
it is a different order of work for no gain. Secondarily, `Mip` is already
sparse-column-oriented, which maps onto MPS's `COLUMNS` section directly, whereas an LP
emitter would have to transpose into row expressions.

What MPS costs us is ambiguity: readers disagree about several of its sections (see
"The MPS format is not DIMACS" below). That cost is real but it is absorbed by
`agreesWith` rather than trusted, and it is the lesser of the two prices.

Fixed-column MPS is not required — SCIP's reader is free-form.

## Why a `Mip` type at all?

Three answers, because the question gets asked three different ways.

**Is there one to reuse?** No. Mathlib at `v4.35.0` has no linear- or
mixed-integer-program type (no `LinearProgram`, no LP duality development).

**Why not state everything about a bare `Prop`?** Because `Prop` is not an inductive
type with constructors you can match on: `encodeMps : Prop → String` is not a function
that can be written, and `agreesWith : Prop → Vipr → Bool` is not one either. You *can*
write `Expr → String` in `MetaM`, but then the correctness theorem has nothing to be
stated about — `Expr` has no denotation into `Prop` that the object logic can see, so
there is nothing to put on the `Spec` side of `MpsDenotes`. The reified type is precisely
the thing that carries a denotation; here that is `Mip.Feasible`.

**Why not reuse the problem-bearing fields of `Vipr`?** This is the real alternative, and
it is not silly: `varNames`, `intVars`, `objSense`, `objTerms` and `cons` already *are* a
MIP, so one could take a `Vipr` as the input and skip `Mip` entirely. Against it: the user
would write their problem in certificate syntax; the type drags along `rtp`, `sols` and
`ders`, which are meaningless for an input; `objSense : String` is unvalidated; and
`cons` has already flattened variable bounds into rows, so there is nothing left to emit
an MPS `BOUNDS` section from. All of these are design-quality objections rather than
soundness ones — but they are the reason for a separate type, and they are what to say
when asked.

### The closest prior work: `leanprover/lp`

[`leanprover/lp`](https://github.com/leanprover/lp) — "Linear programming in Lean 4: `lp`
and `maximize` tactics, plus a verified SoPlex-backed solver" — is the nearest thing to
this branch, and much nearer than the SAT work below. Its architecture is ours: SoPlex is
an untrusted oracle, every certificate is validated by a pure-Lean checker, and the result
carries a Lean proof. It should be cited as the primary comparison.

**It independently confirms two decisions made here.**

* It has a *reified* problem type — `Problem n m` with `c`, `a`, `rowBounds`, `colBounds`,
  sizes pinned in the type. So the argument above against taking a bare `Prop` as the
  source is not idiosyncratic; the same conclusion was reached separately.
* It chooses **reconstruction over reflection**: "build kernel proof terms — no
  `Problem`/`Certificate` data reaches the kernel, only a weighted-sum-of-hypotheses
  identity", and "the kernel proof is reconstructed from those multipliers and the original
  hypothesis terms." That is authoritative support for the reconstructor, and it explains
  why they never meet the kernel-reduction ceiling measured below.

**What separates the two is integrality, and the separation is clean.** `leanprover/lp` is
pure continuous rational LP: `isInt` has zero occurrences in the repository, nothing
mentions MIP, branch-and-bound, cuts or Gomory, and SoPlex is an LP solver. Its
certificates are Farkas / dual multipliers. VIPR exists precisely *because* Farkas duality
cannot express a mixed-integer refutation — a MIP certificate needs `rnd` (integer
rounding) and `uns` (branch discharge), which is what `Thm/System/RuleSound.lean` proves
sound. Neither the knapsack nor the market-split instance is expressible in their
`Problem` type at all.

So the honest positioning is **not** "LP in Lean", which is taken and done better. It is
*verified mixed-integer* programming: the integrality layer above what they cover, with
LP as the degenerate case.

**Complementary, and the layering is literal rather than diplomatic.** Exact SCIP's own
`--version` reports `[LP solver: SoPlex 8.0.1]`: SCIP *is* branch-and-bound with cuts
sitting on top of SoPlex, which solves its LP relaxations. `leanprover/lp` verifies
SoPlex. This branch verifies SCIP. The relationship between the two Lean developments is
exactly the relationship between the two solvers they check, one layer up.

That is also why "we express more problems" is the weaker form of the claim, and not the
one to lead with. Expressing more is nearly free — it is the `isInt` field on
`Mip.Var`. What is not free is that the extra expressiveness arrives with extra *proof
rules that have to be proved sound*:

| | certificate is | rules to verify |
|---|---|---|
| `leanprover/lp` | a dual multiplier vector | Farkas duality |
| this branch | a derivation DAG | `asm`, `lin`, `rnd`, `uns` — branch discharge and integer rounding |

A Farkas certificate is a *vector*; a VIPR certificate is a *proof tree*. Those are
different objects, which is why the two developments cannot simply be merged into one
checker, and why the contribution here is the rule layer rather than the problem class.

And the fragments nest exactly: VIPR's `lin` reason **is** a Farkas combination. So
`leanprover/lp` is, in effect, a very well-engineered checker for the `lin` fragment, and
this branch adds `rnd` and `uns` above it. That suggests a real integration rather than a
turf split — their tactic frontend for continuous goals, falling through to this pipeline
when integrality appears — which is the right "future work" sentence.

Framing the relationship as subsumption is therefore both inaccurate and unnecessary.

For completeness, since the question comes up: **in problem class this does contain LP, in
capability it does not.**
A pure LP is a `Mip` with every `isInt := false`, and the pipeline does close on one:
exact SCIP certifies `max (1/3)a + b` s.t. `(2/5)a + b ≤ 7/4`, `b ≤ 1/6` in a 276-byte
certificate with `int 0` and `lin×2` — no `rnd`, no `uns`, pure Farkas — and
`agreesWith`, `sameProblemAs`, `objAgreesNegWith` and `checkVipr` all accept it. So the
containment is real in the implementation, not only on paper. Three things still stop it
being subsumption:

* **Unboundedness cannot be expressed.** `leanprover/lp` proves `.unbounded`. VIPR v1.0's
  `RTP` is `infeas` or `range lb ub`, and `range -inf inf` claims *no bound*, not
  unboundedness. This is a limitation of the certificate format, not of our checker, so it
  cannot be closed without extending VIPR.
* **On LP we would be far slower and clumsier.** Their path is an in-process SoPlex FFI
  call plus proof-term reconstruction. Ours writes an MPS file, forks a SCIP binary, parses
  a certificate, checks it, and reduces in the kernel — plus they have tactics and we do
  not. For a small LP goal they win on every axis that a user notices.
* **It needed a bug fix to work at all**, which is the useful lesson. Exact SCIP negates
  the objective to turn maximization into minimization, so the `v.objSense = "max"`
  hypothesis on `pipeline_upper_bound` is never satisfied by real output — those theorems
  were unreachable. `pipeline_upper_bound_of_min` and `objAgreesNegWith` are the fix. See
  `docs/SCIP-SETUP.md`.

**Where `leanprover/lp` is ahead, and it is worth saying so.**

| | `leanprover/lp` | this branch |
|---|---|---|
| variables | continuous `Rat` only | integer **and** continuous |
| oracle | SoPlex, in-process via FFI | exact SCIP 10, via a file |
| certificate | Farkas / dual multipliers | VIPR v1.0 (`asm`, `lin`, `rnd`, `uns`) |
| proof route | reconstruction | reflection (`decide +kernel`) |
| outcomes | optimal, infeasible, **unbounded** | infeasible, range, optimal point |
| semantics | `Rat` | `ℝ` |
| frontend | `lp`, `maximize`; a Π₂ fragment with `∃`/`∀` | none yet |
| packaging | five packages, FFI backend, synced examples | a research branch |

Their frontend is well beyond the reflection tactic sketched above — it handles
`∃ x : Rat, ∀ y : Rat, …`, atomizes non-affine subterms, and tracks strictness through a
strict-aware Farkas certificate. They also prove unboundedness, which has no counterpart
here. And being over `Rat` rather than `ℝ` costs them nothing in solving power, since
feasibility of a rational linear system coincides over `ℚ` and `ℝ`; it only means a user
whose variables are real cannot apply their tactic directly.

**The risk to state plainly.** If `leanprover/lp` swaps SoPlex for a MIP backend, the
distinction narrows to the certificate layer. The defensible contribution is therefore the
VIPR layer itself — the `rnd` and `uns` soundness proofs and the agreement check — not "a
verified solver in Lean". That is an argument for stating the contribution precisely, not
for competing on breadth.

### How to argue this is a contribution, specifically against `leanprover/lp`

Three things, in descending order of strength. The first is the one to lead with.

**0. The strongest form of the argument is a theorem, not a benchmark.** `leanprover/lp`'s
tactic is carrier-parametrized — it has `Rat`, `Int`, `Nat`, `Dyadic` and field lanes — so
it is *not* `Rat`-only, and the obvious worry is that its `Int` lane already does integer
reasoning. Reading the source settles it: `LPTactic/LP/IntCertificate.lean` says the whole
assembly is "the shared **ordered-ring** one in `RingCertificate.lean`", and its context
takes "integer multipliers only (the residual must clear to an integer; a fractional one
means the certificate is not expressible over `Int`)". The integrality check is on the
*multipliers*, not on the variables. So every lane proves goals by a weighted sum of
hypotheses — a Farkas / positive-combination argument.

Farkas' lemma then does the rest of the work for us. A linear system is infeasible **iff**
such a combination exists. Our examples have *feasible* LP relaxations — the knapsack's
relaxation is optimal at `y = 4/5`, `z = 1` — so no such combination exists, and therefore
**no Farkas-based method can prove them, in any carrier.** That is a completeness
statement about the method, not a gap in their implementation, and it is the cleanest
possible framing: the problems this branch addresses are exactly the ones duality cannot
reach, which is why VIPR has `rnd` and `uns` at all.

**1. Concretely, on our examples the answers differ.** This is
stronger than any timing comparison, because `leanprover/lp` is not slower on an integer
problem — it cannot state one, and the relaxation it *can* state has a different answer.
Measured on the running example: strip the integrality markers from
`encodeMps knap` and exact SCIP reports `3 variables (0 bin, 0 int, 3 cont)`, **optimal —
feasible**, with witness `y = 4/5`, `z = 1` (indeed `10·(4/5) + 15·1 = 23`). The integer
problem is **infeasible**. An LP-only checker given this problem therefore returns a
verified answer to a question the user did not ask, and the fractional witness `y = 4/5`
is exactly what the `rnd` rule exists to eliminate.

(Note the trap here: doing this experiment on the *hand-written*
`examples/uns_knapsack.mps` appears to show the relaxation is infeasible too. That file
uses `LI`/`UI` bound types, which SCIP reads as declaring integrality, so stripping the
markers does not remove it. `encodeMps` emits `LO`/`UP` precisely to avoid that ambiguity,
which is why the experiment has to be run on our own output.)

**2. The rule layer is the contribution, and it is quantifiable.** Farkas duality has no
rounding rule and no branch rule. Across `benchmarks/`, every instance is entirely
integer, and the derivations are dominated by exactly the reasons a Farkas checker lacks:

| instance | lines | int vars | `asm` | `lin` | `rnd` | `uns` |
|---|---|---|---|---|---|---|
| `alu4_1` | 66433 | 283/283 | 854 | 55126 | **8276** | **427** |
| `alu6_1` | 34664 | 295/295 | 440 | 27995 | **4193** | **220** |
| `alu5_5` | 6405 | 302/302 | 26 | 3966 | **540** | **13** |

A Farkas-only checker verifies zero of those `rnd` and `uns` steps. "We verify 8,276
integer-rounding steps on `alu4_1`" is a concrete claim; "we express more problems" is not,
since expressing more is just the `isInt` field.

**3. Scale on real instances.** The `benchmarks/` set is MIPLIB-derived and no other Lean
development can state any of it.

### The benchmark table the paper needs

Capability first — this is the primary table, and it needs no timings:

| | integer vars | objective | infeasibility | optimum | unbounded | frontend |
|---|---|---|---|---|---|---|
| `omega` | yes | no | yes | no | no | tactic |
| `linarith` | no | no | rational only | no | no | tactic |
| `leanprover/lp` | **no** | yes | rational only | yes | **yes** | tactics, Π₂ |
| this branch | **yes** | yes | yes | yes | no | none yet |

Then timings only where capability actually overlaps:

* **vs `omega`, integer feasibility.** Have one point: an infeasible market-split instance
  (3 equalities, 12 binaries) where `omega` ran 600s without finishing and this pipeline
  took 0.12s to certify and 22s to kernel-check. Should be extended to a family to show a
  curve rather than a single point.
* **vs `linarith`, rational LP infeasibility.** Not yet measured.
* **vs `leanprover/lp`, pure LP.** Not yet measured — and note it is not trivial to set
  up here: `lp` pins Lean **v4.33.1** against our v4.35.0, and on this machine its SoPlex
  FFI fails to link because v4.33.1's bundled `ld64.lld` cannot parse the installed macOS
  SDK's `.tbd` files ("unknown architecture"). Its pure-Lean side builds fine, so the
  blocker is environmental, not theirs; the `lp-backend-soplex-json` backend would avoid
  the native link. When measured, **we will lose** — they call
  SoPlex in-process and reconstruct a proof term, we fork a solver and parse a file.
  Report it anyway; disclosing the case where the specialised tool wins is what makes the
  rest of the comparison credible.

Two things not to claim: that this is faster (on LP it is not), and that it replaces their
tactic frontend (there is no frontend here yet).

One caveat on examples. `omega` proves the knapsack running example in one line, so the
knapsack is a *pedagogical* example and must not be the headline evidence. Lead with an
instance no competing tactic can state or finish — market split, or any `alu`.

### Relation to SAT and SMT in Lean

The natural comparison is `bv_decide` and [Trestle], and it is worth getting right,
because the comparison is usually made in a way that argues against `Mip` when in fact it
argues for it.

Both of those have a reified layer; it is just not what the user sees.

- `bv_decide` takes a `Prop` goal only as a *tactic entry point*. The verified chain is
  `BVLogicalExpr → AIG → Std.Sat.CNF → LRAT → verified checker`, every step about reified
  inductives, and the `Expr → BVLogicalExpr` step is proof-producing metaprogramming: per
  goal it emits a term of type `goal ↔ expr.denote env`. No theorem is quantified over
  `Prop`.
- Trestle's `VEncCNF` is the more interesting design. It moves the *specification* side to
  a semantic predicate `PropAssignment ν → Prop` — a `Prop` parameterized by the
  assignment — and carries the correctness statement in the encoding monad's type. But the
  *output* side stays `ICnf`, a reified inductive, because that is what gets printed to
  DIMACS and what the LRAT indices refer to.

### Matching Trestle's guarantee, not just its shape

`VEncCNF`'s index is an **iff**: the CNF's models, restricted to the original variables,
are *exactly* the assignments satisfying `P`. Both directions are load-bearing there,
because a SAT answer is used in both — `UNSAT` of the CNF must mean `P` unsatisfiable,
and a model must yield a real solution to `P`.

LeanVIPR now carries the same pair:

| direction | licenses | relation |
|---|---|---|
| `m`-feasible ⇒ certificate-feasible | an **infeasible** answer transfers down | `Relaxes` |
| certificate-feasible ⇒ `m`-feasible | a **positive** answer — a `SOL` point — transfers back | `Relaxed` |

and `SameProblem` is their conjunction, decided by `sameProblemAs`. That is the
LeanVIPR analogue of what `VEncCNF` asserts in its type: an equivalence of feasible sets
modulo renaming, rather than one problem bounding the other.

Two things made the second direction nearly free. Both `Mip.Feasible` and `Vipr.Feasible`
unfold to the *same* conjunction, `(∀ j ∈ ints, IsIntReal (a j)) ∧ (∀ c ∈ rows, satReal c a)`,
so the relation and the transfer lemma are stated once on bare row/integer lists
(`RelaxesRows`, `RelaxesRows.transfer`) and instantiated twice with the arguments swapped.
The whole converse cost one definition, one `Bool`, and two one-line corollaries.

The one genuine asymmetry: the forward direction needs nothing at all of `σ`, because
`a ∘ σ` is meaningful for an arbitrary function. Going back needs a second map `τ` in the
opposite direction. The two are **not** required to be mutually inverse — nothing assumes
it, they are independently checked — which keeps both recoveries untrusted heuristics.
(On both real certificates they happened to come out equal, `#[1,0,2]` and `#[0,2,1,3]`,
because both permutations are involutions. That is a coincidence of the examples and is
not relied on anywhere.)

Measured on real SCIP output: `sameProblemAs` is `true` for the knapsack (`RTP infeas`)
and for the mixed problem (`RTP range`), and `false` for a negative control whose
right-hand side is changed by one.

So **`Mip` is the analogue of Trestle's `ICnf`, not of its `PropFun`.** Our
`Mip.Feasible : Mip → RealValuation → Prop` already has the same shape as Trestle's
predicate; what cannot be dropped is the reified side, for the same reason Trestle cannot
drop `ICnf`: the reified form is what the oracle interface is about.

**And our oracle interface is weaker than theirs, which is the whole point.** A SAT
handoff is *positional*: DIMACS variables are `1..n` and the LRAT proof refers to that
same file, so "the solver answered *my* question" needs no check — there is no second copy
of the formula that could disagree. VIPR hands back a certificate that **re-declares the
problem** in its own `VAR`/`CON` sections, with its own names and its own order. Closing
that needs a decidable comparison between two reified problems, and both sides of a
decidable comparison must be data. That is `agreesWith`, and it is the contribution
relative to the SAT work: same architecture, one extra verified link.

**Where we are easier than Trestle.** Most of `VEncCNF`'s complexity is auxiliary
variables — Tseitin and cardinality encodings introduce fresh ones, so correctness is
equisatisfiability *modulo* new variables, with all the attendant `agreesOn` / `semVars`
machinery. Our encoder introduces none; MPS is a direct transcription of a `Mip`. So
`mpsRoundTrip` is plain denotation equality: strictly stronger, and much less work. Worth
stating explicitly, since a reader who knows Trestle will expect the harder statement.

[Trestle]: https://github.com/JamesGallicchio/trestle

### The `Prop` front end, and which shape it should take

`Mip.Feasible` *is* a `Prop`, so a `Prop`-level front end is a separate and later layer.
There are two shapes for it and the choice is open (see Open questions):

1. **Reflection tactic.** Match a goal of the form
   `¬ ∃ x y z : ℤ, 0 ≤ x ∧ … ∧ 6*x + 10*y + 15*z = 23`, build a `Mip` and a proof that
   the two agree, discharge by the pipeline theorem. Natural to *state*, brittle to
   implement: it must cope with however the user arranged their `∃` and `∧`, and it fails
   opaquely when it cannot.
2. **Verified-encoding monad, Trestle-style.** A `VEncMip` whose type carries
   `∀ a, m.Feasible a ↔ P a`, so the user writes
   `do let x ← intVar (lo := 0); constrain (6*x + 10*y = 23)` and gets the `Mip` and the
   agreement proof together. No `Expr` matching, no metaprogramming, proofs compose. Price
   is that the user writes a monadic program instead of a mathematical statement — the
   trade Trestle deliberately makes, and the reason it scales to real encodings.

Either way the *tactic* is worth doing only once the `Mip` end-to-end theorem exists — but
its mathematical content does not have to wait, and no longer does.

### What is already proved: `Thm/Reflect.lean`

The whole mathematical content of a `Prop` front end is the step from `Mip.Infeasible`,
which is about *real* valuations with the declared variables integral, to the narrower
statement a user asks for, which is about tuples of integers. That is now proved, and it
is short, because **integrality comes for free**: a valuation built by casting integers
satisfies `IsIntReal` at every index, not merely at the declared ones, so the first
component of `Mip.Feasible` is discharged without reference to `intVars`.

```lean
def valuationOfInts (xs : List ℤ) : RealValuation := fun j => ((xs.getD j 0 : ℤ) : ℝ)

theorem absurd_of_infeasible {m : Mip} (h : m.Infeasible) (xs : List ℤ)
    (hrows : ∀ c ∈ m.conSLes, satReal c (valuationOfInts xs)) : False
```

plus the `@[simp]` computation lemmas for `valuationOfInts` on a cons-list, which are what
stop a reflected goal stalling on `valuationOfInts [x, y, z] 0` as an opaque term. Those
lemmas are not decoration: without them the row obligation is finite but not mechanical.

**The per-goal obligation closes by automation, and that is the de-risking result.** The
knapsack has been proved at the `Prop` level, taking `knap.Infeasible` as a hypothesis:

```lean
theorem knapsack_no_int_solution (hinf : knap.Infeasible) :
    ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                   6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1
```

no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`. The recipe is exactly what a
tactic would emit, which is the point of having done it by hand first:

1. `rintro` the existential, then `refine Mip.absurd_of_infeasible hinf [x, y, z] ?_`.
2. `exact_mod_cast` each integer hypothesis into `ℝ`, since that is where rows live.
3. `have hcs : m.conSLes = [...] := by rfl` — `conSLes` *computes*, which is worth knowing.
4. Split the membership and close each row with `norm_num` then `linarith`.

So the remaining work in a front end is syntax matching in metacode, which carries no
proof obligation of its own. The `m.Infeasible` this consumes is now supplied by
`Thm/Encoder/Pipeline.lean`, and the two compose — see "The chain closes" below.

## Module plan

Following the existing `Spec` / `Impl` / `Thm` split — nothing in `Spec` executable,
nothing in `Impl` trusted, every theorem in `Thm` with `Spec` on one side.

| file | holds | status |
|---|---|---|
| `Spec/Mip.lean` | `Mip` and its semantics; `RelaxesRows`/`Relaxes`/`Relaxed`/`SameProblem`; `ObjAgrees`; `valuationOfInts` | **done** |
| `Spec/Syntax/Mps.lean` | the grammar of an MPS file and which `Mip` it denotes, plus `EncodableNames` | **done, builds; denotation validated by evaluation** |
| `Impl/Encoder/Mps.lean` | `Mip → String`: the emitter | **done, builds, validated against exact SCIP** |
| `Thm/Reflect.lean` | `Mip.Infeasible` → a `Prop` about integer tuples | **done, builds, proved** |
| `Impl/Encoder/Agree.lean` | `agreesWith`, `relaxedByWith`, `sameProblemAs`, `objAgreesWith`; `σ`/`τ` recovery | **done, accepts both real certificates** |
| `Thm/Encoder/Emit.lean` | tokenization half of `mpsRoundTrip`, proved; denotation half remaining | **partial** |
| `Thm/Encoder/Agree.lean` | `RelaxesRows.transfer` and both directions; `SameProblem.feasible_iff`; objective transfer | **done, proved** |
| `Thm/Encoder/Pipeline.lean` | `pipeline_infeasible`; `pipeline_lower_bound`/`_upper_bound`; `pipeline_optimum_within_*`; `pipeline_optimal_*`; `feasible_of_solution` | **done, proved** |

`Spec/Mip.lean` is deliberately shaped so the agreement proof is about two lists of
`SLe` and not two unrelated semantics: `Mip.conSLes` and
`LeanVIPR.Semantics.Lower.conSLes` have the same type, and `Mip.Feasible` is
definitionally the same shape as `Vipr.Feasible`.

`Mip.boundSLes` emits lower bound before upper, in variable-index order, and exact SCIP
emits its `B` rows in that same shape — one row per finite bound, lower first, in
ascending index order. **But the earlier claim here that the common case therefore
compares without sorting is wrong, and measurably so.** SCIP permutes the variables, so
the `B` rows come back in ascending *SCIP* index order, which is our order composed with
`π`. On the knapsack our `boundSLes` is `x_lo x_hi y_lo y_hi z_lo z_hi` while the
certificate's is `y_lo y_hi x_lo x_hi z_lo z_hi`. `agreesWith` has to compare the rows as
a multiset, or sort under `π`, not walk two lists in step.

### The two theorems the branch aims at

Encoder correctness, stated against the MPS *grammar* rather than against our own reader,
for the same reason `Thm/Parser` is stated against `Spec/Syntax/Grammar`:

```lean
theorem mpsRoundTrip (m : Mip) (h : m.WellFormed) :
    MpsDenotes (encodeMps m) m
```

and the one that matters to a user:

```lean
theorem pipeline_infeasible (m : Mip) (v : Vipr)
    (hagree : agreesWith m v = true)
    (haccept : checkVipr v = true)
    (hrtp : v.rtp = .infeas) :
    m.Infeasible
```

with the `RTP range` companion stated against `RangeBoundValid` (the bound at every
feasible point), since that is the stronger thing a valid certificate gives;
`Mip.OptimumWithin` follows.

### What a user can conclude, in increasing strength

1. `m.Infeasible` — from `RTP infeas`. This is `pipeline_infeasible` above.
2. `m.OptimumWithin lb ub` — from `RTP range`. **Done.** `pipeline_lower_bound` and
   `pipeline_upper_bound` give the dual bound at
   every feasible point, which is the stronger statement, and
   `pipeline_optimum_within_min`/`_max` derive `Mip.OptimumWithin` from it. Validated
   end-to-end on the `RTP range (some 0) (some 0)` certificate exact SCIP emitted for the
   mixed problem, `#print axioms` clean. `objAgreesWith` is the extra check this needs
   beyond `agreesWith`: the certificate's objective must be our objective as a *linear
   function* once the renaming is undone, compared through `formEq` rather than as a list.
   The objective *sense* is an explicit hypothesis rather than part of the agreement
   check, since which end of the interval a certificate establishes is a property of the
   claim, not of whether the problems match.
3. **A verified optimal point. Done.** `pipeline_optimal_min` and
   `pipeline_optimal_max` conclude `Mip.IsOptimal a` from a tight certificate
   (`RTP range (some z) (some z)`) together with a feasible point attaining `z` — the dual
   bound rules out anything better, the point supplies the primal side.
   `feasible_of_solution` is what produces such a point from the certificate's own `SOL`
   section, via the `Relaxed` direction. Earlier sketch, now superseded:

```lean
theorem pipeline_optimal (m : Mip) (v : Vipr) (a : RealValuation)
    (hagree : agreesWith m v = true)
    (haccept : checkVipr v = true)
    (hsol : …a is one of v's SOL entries…)
    (htight : v.rtp = .range (some z) (some z)) :
    m.IsOptimal a
```

A pure LP — a `Mip` with no integer variables — is the easiest case of all three: the
certificate is Farkas duality, so only `asm`/`lin`/`sol` reasons appear, no `rnd`, and no
`lin weak` rows, which means the completion search in `Spec/Semantics/Lower.lean` is never
reached. If a short, clean headline result is wanted, "exact LP solving with a verified
optimality certificate" has the shortest trusted path.

Note what the pipeline is *not*: a decision procedure. There is no totality theorem, and
there will not be one. Exact SCIP can time out, or return a certificate that fails
agreement or checking, and then the tactic fails. This is the same status `bv_decide`,
`polyrith` and Trestle have, and it is worth saying rather than leaving a reader to
discover.

## Where the proof gets checked, and what it costs

`viprcheck` already has all four combinations of two independent axes — whether the slice
or the whole certificate is checked, and whether the kernel reduces the checker or
compiled code runs it. They are often conflated; they are orthogonal.

| | full certificate | backward-sliced |
|---|---|---|
| **kernel** (`decide +kernel`) | `--kernel-mode full` | `--kernel-mode reconstruct` |
| **compiled** (untrusted) | `--native-mode full` | `--native-mode slice` |

Slicing is **not** a native-only optimisation. `--kernel-mode reconstruct` is the sliced
*kernel* mode: `sliceVipr` runs as untrusted compiled search, four small facts about the
slice are each proved by `decide +kernel` (`slicedInfeas`, `sameIntVars`, `rowsSubset`,
`acceptedSlice`), and `checkViprInfeasibleSubset_sound` lifts the result to the original.
Search in compiled code, verify a small certificate in the kernel — structurally the same
thing `omega` does.

The axiom story is settled by measurement rather than by analogy. Both kernel modes emit
`#print axioms certified` and report `[propext, Classical.choice, Quot.sound]` — the
standard three, nothing native. For reference, in this project at mathlib `v4.35.0`:

```
omega        [propext, Quot.sound]
linarith     [propext, Classical.choice, Quot.sound]
ring         [propext, Classical.choice, Quot.sound]
decide       (no axioms)
native_decide  [t._native.native_decide.ax_1_1]     ← the only one that adds anything
```

So `omega` and `linarith` are axiom-free, and `native_decide` adds a *generated
per-theorem* axiom that shows up by name in `#print axioms` and cannot be hidden from a
reviewer. Do not cite `omega` as precedent for `native_decide`; it points the other way.

### What the tactic should do

Target `--kernel-mode reconstruct`, performed in `MetaM` rather than by emitting a file:

1. Run the **native check as an untrusted precheck** in `IO`, to fail fast with a readable
   error. Its result never enters the proof term, so it costs no axiom. This is not a
   choice against kernel mode — it is both.
2. Slice in compiled code (untrusted, free).
3. Elaborate the sliced `Vipr` as a **literal term** (`Qq` is already a dependency) rather
   than running the parser in the kernel. `Impl/Parser.lean` has well-founded recursion in
   its main loop and `mergeSort` in its duplicate checks; `Impl/Checker` has neither, so
   keeping the parser out of the reduction path is what makes `decide +kernel` viable.
4. Kernel-reduce `agreesWith m v && checkVipr v`, then apply soundness.

Step 3 has a consequence worth stating in the paper. `LeanVIPRMain.lean` currently
concedes that "the generated theorem certifies the emitted certificate AST. Binding that
AST to the exact source bytes remains a frontend parser/runtime trust boundary." A
`Mip`-level tactic does not close that gap by binding bytes to AST — it makes the bytes
irrelevant, because `agreesWith m v` ties the AST to the `Mip` the user wrote in Lean.
The parser leaves the trusted path entirely, and the round-trip theorem becomes a
usability result rather than a soundness one.

## Order of work

1. ~~`Impl/Encoder/Agree.lean` + `Thm/Encoder/Agree.lean` + `Thm/Encoder/Pipeline.lean`~~
   — **done.** The soundness-critical half. With it the `.mps` may stay hand-written and
   the result is still a theorem about the Lean `Mip`.
2. ~~Re-derive `examples/uns_knapsack.mps` from a Lean `Mip` and check the existing
   certificate against it~~ — **done**, and the re-derived certificate is byte-identical,
   including the `t_` renaming and the variable permutation.
3. ~~`pipeline_optimal`~~ — **done**, together with the `Relaxed` direction it needed.
4. ~~`Spec/Syntax/Mps.lean` + the `Impl/Encoder/Mps.lean` token refactor~~ — **done**;
   `Thm/Encoder/Emit.lean` is partial (tokenization proved, denotation remaining).
5. **Next:** finish `Thm/Encoder/Emit.lean` — see the section below for exactly what is
   left. Buys honesty and completeness, not soundness.
6. **Next:** the `Prop` front end, in whichever of the two shapes wins. `Thm/Reflect.lean`
   already supplies all of its mathematical content, so this is metaprogramming only.

## What has actually been run

### A user's `Prop`, proved from a real certificate

From the real certificate exact SCIP emitted — the one declaring `t_y t_x t_z` where we
wrote `x y z`, renamed *and* permuted:

```lean
theorem agreed   : agreesWith knap cert = true := by decide +kernel
theorem accepted : checkVipr cert = true       := by decide +kernel
theorem isInfeas : cert.rtp = .infeas          := by decide +kernel

theorem knap_infeasible : knap.Infeasible :=
  Mip.pipeline_infeasible agreed accepted isInfeas

theorem knapsack_unsolvable :
    ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ … ∧ 6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1
```

`#print axioms knapsack_unsolvable` → `[propext, Classical.choice, Quot.sound]`. Nothing
beyond what every mathlib result assumes, and in particular no `native_decide`.

`recoverSigma` returned `#[1, 0, 2]`, correctly inverting SCIP's transposition. A negative
control — the same `Mip` with `c0`'s right-hand side changed from 23 to 24 — is rejected.

#### What the design turned out to need, and not need

Two simplifications over the plan sketched above, both found while proving it:

* **No bijectivity, no multiset equality, no `WellFormed`.** To conclude `m.Infeasible`
  it is enough that every `m`-feasible point gives rise to a *certificate*-feasible point,
  which needs only that each certificate row is implied by a row of `m` — a subset
  condition in one direction. And since `σ` maps the certificate's indices to ours,
  `a ∘ σ` is well defined for a completely arbitrary `σ`, so no property of the renaming
  is assumed anywhere. A wrong guess can only cause a rejection. That is what makes
  depending on the undocumented `t_` convention safe.
* **Domination, not equality, on rows.** List equality on `SLe` is too brittle: a renamed
  row carries its terms in the certificate's index order, so the knapsack's `C0` renames
  to a form listing `(1,10)` before `(0,6)` where ours lists `(0,6)` first — the same
  linear constraint, a different list. This was the one real bug in the first attempt
  (`agreesWith` returned `false` on a correct certificate). The fix reuses the checker's
  own `domSLe`, whose `formEq` is insensitive to term order and repeated indices, and
  which additionally accepts a tighter `m` bound implying a looser certificate bound.

### The emitter reproduces the checked-in certificate

`examples/uns_knapsack.mps` was re-derived from a Lean `Mip` and pushed all the way
through. The knapsack of the example — `6x + 10y + 15z = 23`, `x + y + z ≥ 1`, integer
`x ∈ [0,3]`, `y ∈ [0,2]`, `z ∈ [0,1]` — written as a `Mip` and run through
`encodeMps`, then exact SCIP with `certificate filename` set, yields a `.vipr` that is
**byte-identical to the checked-in `examples/uns_knapsack.vipr`**, and `viprcheck` accepts
it. So the emitter produces a file that SCIP reads as the same problem the hand-written one
denotes, which is step 3 of the order of work, done.

A second problem exercising a continuous column, marker toggling, an infinite bound, a
free variable, a fixed variable and an `RTP range` result also round-trips and is
accepted. Its certificate comes back as `RTP range 0 0` with a populated `SOL` section —
that is, a tight bound plus the attaining point, which is exactly the input
`pipeline_optimal` needs. The result is reachable from real solver output, not only in
principle.

### Reflection does not scale; slicing is not optional

Wall-clock on this machine, every certificate in `benchmarks/` plus the example. All seven
are accepted in every mode that finishes; the kernel cap is time, not correctness.

| certificate | lines | RTP | `--native-mode full` | `--native-mode slice` | `--kernel-mode reconstruct` |
|---|---|---|---|---|---|
| `uns_knapsack` | 55 | infeas | <1s | <1s | 9s |
| `alu6_4` | 3181 | infeas | <1s | <1s | 22s |
| `alu5_5` | 6405 | infeas | <1s | <1s | 98s |
| `flugpl` | 7627 | range | <1s | <1s | **TIMEOUT > 900s** |
| `alu6_1` | 34664 | infeas | 3.6s | <1s | **TIMEOUT > 900s** |
| `alu4_9` | 42454 | range | 5.6s | 5.1s | **TIMEOUT > 900s** |
| `alu4_1` | 66433 | infeas | 50s | <1s | **TIMEOUT > 900s** |

Three things fall out of this.

**Kernel reduction is roughly quadratic and caps out around 6–7k lines.** From `alu6_4` to
`alu5_5` the certificate grows 2.01× and the time grows 4.45×. Extrapolating that to
`alu4_1` gives something near three hours, which is consistent with every larger row
timing out. The 9s floor on the smallest case is `lean` startup plus importing
`Thm.Checker.Sound` — a cost a tactic would not pay, being already inside a Lean process —
so the usable budget is a little better than it looks, but not by an order of magnitude.
This is the number that justifies building the reconstructor rather than tuning this path.

**`--kernel-mode full` was dropped from the sweep** after timing out at 1200s on `alu6_4`,
the smallest real benchmark, against 22s for the sliced mode on the same file. It is not a
viable mode on anything but toys.

**Slicing is worth up to 100× on the compiled path too.** `alu4_1` is 50s full and under a
second sliced. That matters for the CLI product independently of the tactic. Note it is
certificate-dependent rather than size-dependent: `alu4_9` barely benefits (5.6s → 5.1s)
while `alu4_1` collapses to nothing.

Range certificates are the weak spot, as expected from `reconstruct` being
`RTP infeas`-only: `flugpl` times out at 7627 lines while the infeasibility certificate
`alu5_5` finishes at 6405.

### The MPS format is not DIMACS

Measured on the same input file, `max x` subject to `x ≤ 1/2`:

| build | reports |
|---|---|
| homebrew `scip` 10.0.3, `[precision: 8 byte]` | `1.0` — reads `1/2` as `1`, silently |
| `scipoptsuite-10.0.1` with `-DEXACTSOLVE=ON` | `0.5` |

Two builds of the same solver version, same file, different problem, no warning. Full
detail in `docs/SCIP-SETUP.md`. The consequence for this branch is the argument *for* the
design rather than against it: the reason `agreesWith` exists is that the chain
`m → file → SCIP's internal problem → certificate` is not trustworthy, and this is that
untrustworthiness measured rather than assumed. If a reader misparses the file, SCIP
solves a different problem, emits a certificate about *that* problem, and `agreesWith`
rejects it against `m`. The ambiguity is absorbed, not trusted.

It also bounds what `mpsRoundTrip` may claim. There is no single MPS grammar to state it
against — the format is name-based rather than positional, and readers disagree about the
default upper bound on marker-delimited integer columns, about a negative `UP` on a
variable with a default lower bound, about `RANGES` on an `E` row, and about the sign of
an objective constant. So `Spec/Syntax/Mps.lean` should be labelled for what it is: *our
formalization of the subset exact SCIP's reader accepts*, exactly as
`Spec/Syntax/Grammar` is for `.vipr`. The "choices forced by MPS" list in
`Impl/Encoder/Mps.lean` is best read as a defensive subset — every item on it is one of
those ambiguities refused.

## `mpsRoundTrip`: what is in place and what the proof needs

`Spec/Syntax/Mps.lean` is written and builds. It follows `Spec/Syntax/Grammar.lean`'s
style exactly — concatenation equations with existentially supplied splits, pure functions
of the fields for denotations, and no mention of the emitter — and it reuses
`IsTokenization`, `IsNumTok` and `IsSeq` wholesale rather than restating them.

Three things about it are worth knowing before proving anything against it.

**It is stated over tokens, not lines.** In the subset we emit, every section is
introduced by a keyword and every entry's token count is fixed by its own first or middle
token, so line structure carries no information. The price is `IsNameTok`: names must
avoid the tokens read structurally. That turns the prose precondition in
`Impl/Encoder/Mps.lean` into `EncodableNames`, which is what `mpsRoundTrip` will assume.
`encodeMps` does not check it, which is harmless for the usual reason — a violation yields
a file SCIP reads as a different problem, and `agreesWith` rejects the certificate.

**It transposes.** MPS is column-major and a `Mip` carries coefficients inside rows, so
`rowForm` rebuilds each row from the column entries and the comparison to `m` is by
`FormEqReal`, not list equality.

**The denotation was checked by evaluation before any proof was attempted.** Transcribing
the `COLUMNS`, `RHS` and `BOUNDS` entries that `encodeMps knap` actually emits and running
the grammar's own functions on them gives

```
intColumns → ["x","x","y","y","z","z"]      (so DeclaresInt holds for x, y, z)
rowForm … "c0" → [(0,6), (1,10), (2,15)]    list-identical to knap's c0 form
rowForm … "c1" → [(0,1), (1,1), (2,1)]      likewise
rowForm … "obj" → []                        the empty objective
rhsOf → (23, 1)
bounds → x ↦ (some 0, some 3), y ↦ (some 0, some 2), z ↦ (some 0, some 1)
```

Note `rowForm` reproduces the forms *list-identically* in the common case, so many of the
`FormEqReal` obligations should fall to `rfl` rather than needing the semantic argument.

### Done: the tokenization half

`isTokenization_encodeMps` is proved:

```lean
theorem isTokenization_encodeMps (name : String) (m : Mip)
    (hp : Printable (mpsToks name m)) (hi : IndentsWhitespace (mpsLines name m)) :
    IsTokenization (encodeMpsNamed name m).toList (mpsToks name m)
```

So the emitted text provably tokenizes to exactly the tokens the file carries. What is
left for `mpsRoundTrip` is that those tokens derive `m` under `IsMpsToks`, plus the two
hypotheses above.

Getting there needed four small generalizations of the existing machinery, all in
`Thm/Encoder/Emit.lean`: `isTokenization_wsPrefix` (leading whitespace contributes no
tokens, which is what makes indentation invisible), `isTokenization_consTok` (one token
then whitespace then the rest), `isTokenization_unwordsChars_append` (a space-joined run
as a *prefix* of the input rather than the whole of it — the lemma
`unwordsChars_isTokenization` does not give), and `isTokenization_renderLines` (the
induction over lines).

And one refactor of the emitter, which is the part worth knowing about.
`Impl/Encoder/Mps.lean` now builds `List Line`, where `Line := String × Toks` is an
indentation paired with that line's tokens, renders via `renderLineChars` at the character
level, and applies `String.ofList` only at the boundary — the same shape
`Impl/Parser/Printer.lean` uses for `print`. That turns the proof into a list induction
instead of an argument about `String.join`. **The rendered output is byte-identical**:
every line is `indent ++ unwords toks`, which is character-for-character what the previous
string-building version produced, verified by re-emitting all three test problems and
diffing against the files exact SCIP accepted.

It also closed a real gap in the grammar. `IsNameTok` did not exclude a name beginning
with `%`, but `IsTokenization` reads a leading `%` as commenting out the rest of the line,
so such a name could never survive a round trip. `IsNameTok` now rules it out, and
`printableTok_of_isNameTok` is the one-line bridge showing the grammar's notion of an
acceptable name and the printer's notion of an emittable token coincide — they were
arrived at from opposite ends and they agree, which is why `EncodableNames` is the only
name precondition the round trip needs.

### Remaining: the denotation half

Two hypotheses to discharge and one theorem to prove.

* ~~`IndentsWhitespace (mpsLines name m)`~~ — **gone, not proved.** `Encoder.Indent` is now
  a three-constructor type rather than a raw `String`, so `allWhitespace_indent` discharges
  it once by cases and the hypothesis has disappeared from `isTokenization_encodeMps`. A
  new section of the emitter cannot introduce a bad indent for a later proof to rule out.
  The first attempt was a lemma per section, each a brittle `rcases` over membership in a
  literal list; the type made all of them unnecessary.
* ~~`Printable (mpsToks name m)`~~ — **proved**, as `printable_mpsToks`. Unlike the
  indents this could *not* be made structural, because the tokens include names taken from
  the user's `Mip`; it genuinely needs hypotheses, bundled as `Mps.Emittable` (the problem
  name, the variable and row names, and the sense restriction from `Mip.WellFormed`).
  Compositional: one lemma per kind of token (`printableTok_mpsRat`,
  `printableTok_markerName`, `printableTok_sense`) and one per section. A
  `Decidable (Printable ts)` instance makes every all-literal line — the section headers
  and the fixed vocabulary `BND`, `rhs`, `'MARKER'` — fall to `decide`.

So the tokenization half is now **unconditional** apart from the names:

```lean
theorem isTokenization_encodeMps' {n : String} (m : Mip) (h : Emittable m n) :
    IsTokenization (Encoder.encodeMpsNamed n m).toList (Encoder.mpsToks n m)
```
* `IsMpsToks (mpsToks name m) m` — the real remaining work, section by section against
  the predicates in `Spec/Syntax/Mps.lean`.

Worth keeping in view while deciding how much this is worth: it buys **honesty and
completeness, not soundness**. `pipeline_infeasible` does not mention `encodeMps`, so an
emitter fault makes `agreesWith` reject rather than making a theorem wrong.

## Open questions

- ~~**Renaming discipline.**~~ **Answered by measurement.** Exact SCIP emits `t_` + the
  original name, *and* permutes the variables. It also writes a `.vipr_ori` companion file
  alongside the certificate, carrying the same problem under the original names with the
  same permutation. So there are three ways to guess `π`: strip `t_`, read `_ori`, or match
  structurally. The real finding is that **the choice does not affect soundness** —
  however `π` is guessed, `agreesWith` verifies that it makes the two row sets equal, so a
  bad guess is rejected rather than believed. This is a completeness-and-speed question,
  not a trust one. Plan: try the `t_` strip first since it is linear and has worked on
  every certificate seen so far, fall back to a structural search, and depend on neither.

- ~~**Bound rows vs. `CON` rows.**~~ **Answered, and `Var.boundSLes` is already exactly
  right.** Bounds come back as `CON` rows, with the `CON n b` header declaring that `b` of
  the `n` rows are bounds — which `Vipr.numCon` and `numBounds` already carry. On a problem
  with an infinite upper bound, a fully free variable and a fixed variable, exact SCIP
  emitted one `G` row for the variable bounded only below, **no rows at all** for the free
  variable, and **two rows, `G` then `L`**, for the fixed variable rather than a single `E`
  row. That is precisely what `Var.boundSLes` produces, down to the `none => []` cases. No
  spec change needed; the one correction is the ordering claim above.

- **Which `Prop` front end.** Reflection tactic or Trestle-style verified-encoding monad
  (see above). Not blocking anything, but the answer changes what step 6 is.

- ~~**The performance gate.**~~ **Measured, and reflection loses.** `--kernel-mode full`
  times out at 1200s on the smallest real benchmark; `--kernel-mode reconstruct` is
  roughly quadratic and caps out near 6–7k lines, against certificates in `benchmarks/`
  that run to 66k. Build the reconstructor. The axiom-free story survives either way —
  both routes stay within `[propext, Classical.choice, Quot.sound]`, so `native_decide`
  is not needed as a fallback and should not be reached for.

- **Slicing for `RTP range`** — still open, but now with a number attached. `reconstruct`
  is `RTP infeas`-only, and `flugpl` (range, 7627 lines) times out where `alu5_5`
  (infeas, 6405) finishes in 98s. If the reconstructor is built, this question may
  dissolve: replay handles infeas and range uniformly, so the range-specific slicer is
  only needed if the reflection path is kept alive for some reason.

- **How far the reconstructor actually gets.** The quadratic blowup above is kernel
  *reduction* of the whole checker. Replay turns that into N small per-row reductions, so
  the expectation is near-linear — but that is a prediction, not a measurement. The first
  thing to do once a reconstructor exists is to run exactly this table again and check the
  curve, because the per-row ℚ side conditions (`linCheck … = true` and friends) are still
  kernel arithmetic and could carry a worse constant than expected.
