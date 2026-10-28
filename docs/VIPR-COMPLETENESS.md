# VIPR proof-system completeness

The completeness-only Lean modules live under `LeanVIPR/Completeness/` and
are collected by `LeanVIPR/Completeness.lean`. Checker execution, soundness,
termination, and complexity remain under `LeanVIPR/Cert/`.

This note develops proof-system completeness, the mathematical theorem that
would complement LeanVIPR's existing soundness theorem.  The target is
existence of a finite declaratively valid VIPR proof.  It does not include an
obligation for an executable search procedure, Boolean checker, or parser to
find or accept every such proof.

## 1. Correct statement

The current definition

```lean
def ProofSystemComplete : Prop :=
  ∀ (base : List SLe) (intVars : List Nat),
    SemanticallyInfeasible base intVars →
    HasViprRefutation base intVars
```

is too broad.  `satReal` interprets a row with an unrecognized sense as false,
whereas the VIPR rules are intended only for senses `L`, `G`, and `E`.  Thus a
malformed base can be semantically infeasible merely because it contains an
invalid sense, without providing a mathematical inequality from which a VIPR
contradiction can be derived.

Define

```text
ValidSense(c) := c.sense ∈ {L,G,E}
RowsWellFormed(base) := every row in base has a valid sense.
```

The target infeasibility theorem is:

> **VIPR infeasibility completeness.** Let `base` be a finite well-formed list
> of linear constraints with rational coefficients, and let `intVars` be a
> finite list of variables required to be integral.  If no real valuation
> satisfies `base` while assigning integers to `intVars`, then there is a
> finite, closed VIPR v1.0 derivation ending in an absurdity.

In the current Lean vocabulary:

```lean
theorem proofSystem_complete
    (hrows : RowsWellFormed base)
    (hinfeas : SemanticallyInfeasible base intVars) :
    HasViprRefutation base intVars
```

This statement concerns a parsed mathematical problem.  It does not assert that
an arbitrary solver terminates, that SCIP emits a certificate, or that a
textual parser accepts every serialization.

## 2. Rational Farkas lemma

First normalize every row to a `≤` inequality:

- retain `a x ≤ b`;
- replace `a x ≥ b` by `-a x ≤ -b`;
- replace `a x = b` by `a x ≤ b` and `-a x ≤ -b`.

For a finite rational system `A x ≤ b`, rational Farkas completeness states:

> If `A x ≤ b` has no real solution, then there is a rational vector
> `λ ≥ 0` such that `λᵀ A = 0` and `λᵀ b < 0`.

The usual real Farkas lemma gives real multipliers.  Rational multipliers follow
because, after rescaling the strict inequality to `λᵀ b ≤ -1`, the multiplier
conditions form a nonempty rational polyhedron, and every nonempty rational
polyhedron contains a rational point.

Mapping the normalized multipliers back to the original row senses produces a
VIPR-suitable signed combination:

- a multiplier of a `≤` row remains nonnegative;
- a multiplier of a `≥` row becomes nonpositive;
- the two multipliers associated with an equality are combined into one signed
  multiplier.

The resulting `lin` step has zero left-hand side and negative right-hand side.
This proves unconditional completeness of the rational LP fragment.

This layer is now formalized constructively:

- `FourierMotzkin.feasible_eliminate_iff` proves exact one-variable rational
  projection.
- `FarkasCompleteness.rationalFarkas_complete_le` iterates elimination while
  tracking nonnegative multipliers back to the original `≤` rows.
- `ViprCompleteness.rationalFarkas_complete` maps the multipliers through
  `L`/`G`/`E` normalization.
- `ViprCompleteness.lpFragment_complete` constructs a closed one-step VIPR
  refutation for every infeasible well-formed rational LP.

These theorems contain no `sorry` and use only Lean's standard logical axioms.

## 3. Elementary bounded-MILP completeness

There is a direct completeness proof when every declared integer variable has
explicit finite integral lower and upper bounds.

Assume that for every integer variable `x_j`, the base contains

```text
L_j ≤ x_j
x_j ≤ U_j
```

for integers `L_j ≤ U_j`.

Construct a finite branch-and-bound tree:

1. Repeatedly split on `x_j ≤ k` versus `x_j ≥ k+1`.
2. Use the explicit bounds to discard branches outside `[L_j,U_j]`.
3. Continue until every surviving leaf fixes every integer variable to one
   integer value.
4. At such a leaf, all integer variables are fixed to integers.  If its LP
   relaxation were feasible, its real solution would be a feasible
   mixed-integer solution of the original problem.  Hence every leaf LP is
   infeasible.
5. Apply rational Farkas completeness at every leaf.
6. Flatten the tree to VIPR:
   - `asm` introduces the two branch bounds;
   - `lin` emits each leaf contradiction;
   - `uns` combines two identical contradictions and discharges the
     complementary bounds.

The tree is finite because there are finitely many integer variables and each
has a finite domain.  This proves:

> **Bounded VIPR completeness.** Every infeasible well-formed rational MILP
> with explicit finite integral bounds on all integer variables has a finite
> VIPR refutation using only `asm`, `lin`, and `uns`.

This theorem closely matches the finite bounded-integer branching argument used
by certificate-construction algorithms.  It is a useful first Lean milestone,
but it is not completeness for arbitrary unbounded rational MILPs.

The unbounded one-integer-variable case is also formalized.  After exact
projection of every continuous variable, an LP-feasible but integer-infeasible
one-dimensional system must contain both a lower-bound row and an upper-bound
row.  Scaling and rounding those rows derives finite integral bounds, after
which bounded completeness applies.  Consequently
`OneDimensionalCompleteness.oneIntegerVariable_proof_complete` covers any
finite number of continuous variables and one declared integer variable.

## 4. General rational-MILP completeness

The general theorem can be reduced to the classical finite-rank theorem for
Chvátal--Gomory cuts.

Let the original feasible polyhedron be

```text
P := {x ∈ ℝⁿ | A x ≤ b},
```

and let `I` be the integer coordinates.  Let

```text
Q := projection_I(P).
```

Because `P` is a rational polyhedron, `Q` is a rational polyhedron.  The
original MILP is feasible exactly when `Q` contains an integer point.
Therefore semantic infeasibility gives

```text
Q ∩ ℤᴵ = ∅.
```

The finite Chvátal--Gomory rank theorem for rational polyhedra gives a finite
sequence

```text
Q = Q⁰ ⊇ Q¹ ⊇ ... ⊇ Qʳ = conv(Q ∩ ℤᴵ) = ∅,
```

where `Qᵗ⁺¹` is the Chvátal--Gomory closure of `Qᵗ`.  Each closure is again a
rational polyhedron and has a finite description by CG cuts.

Compile this sequence into VIPR:

1. Choose a finite rational inequality description of `Q`.  Every such
   inequality, lifted by assigning coefficient zero to each continuous
   variable, is valid for `P`.  If `P` is nonempty, the valid-inequality form
   of Farkas' lemma expresses it as a suitable rational combination of the
   original rows, so a VIPR `lin` step derives it.  If `P` is empty, ordinary
   Farkas already gives the final contradiction.
2. A CG cut for a current rational system first forms a suitable rational
   combination whose left-hand side has integer coefficients on integer
   variables and zero coefficients on continuous variables.  It then rounds
   the right-hand side down for `≤` or up for `≥`.  This is exactly the VIPR
   `rnd` rule.
3. Derive a finite description of each `Qᵗ⁺¹` from the already derived
   description of `Qᵗ`.
4. Since `Qʳ` is empty, rational Farkas completeness supplies a final `lin`
   step deriving an absurdity.

No branch assumptions are needed for this proof.  Thus `lin` and `rnd` alone
are complete for rational MILP infeasibility, provided the finite CG-rank and
rational-polyhedral ingredients are available.

`ChvatalGomory.Cut` now models an arbitrary semantic CG cut, including cuts
whose coefficients become integral only after aggregation.
`ChvatalGomory.refutation_proof_complete` compiles every finite CG derivation
ending in rational infeasibility into a closed declaratively valid VIPR proof.
`ValidInequalityCompleteness.validInequality_complete` constructively proves
the valid-inequality form of rational Farkas completeness by introducing one
fresh variable, projecting the original variables with Fourier--Motzkin
elimination, selecting a supporting projected row, and recovering its
nonnegative original-row combination.
`ValidInequalityCompleteness.proofSystem_complete_of_semanticRank` therefore
reduces the full theorem exactly to the semantic finite-CG-rank statement.
`FiniteRankCriterion.ClosureOperator.refutation_of_eventually_infeasible`
formalizes the finite assembly step of the classical rank argument: if each
semantic closure round has a finite description and every row in some finite
rationally infeasible integer-hull description appears after finitely many
rounds, then one common finite round is already rationally infeasible.
`FinitePolyhedron.noIntSolution_iff_finite` transfers the sparse checker
semantics to the genuinely finite-dimensional rational space indexed by the
declared integer variables.  Thus subsequent integer-hull geometry applies to
the same row systems and can be transferred back without an additional
semantic assumption.  `FinitePolyhedron.evalLinear` realizes each sparse form
as a rational linear map, and `FinitePolyhedron.polyhedron_convex` proves that
the finite feasible region is convex.  `FinitePolyhedron.integerHull` is the
rational convex hull of its integral feasible points, and
`FinitePolyhedron.integerHull_empty_iff` proves that this hull is empty exactly
when the finite row system has no integral solution.
`FinitePolyhedron.cgClosure` intersects the relaxation with every semantic CG
cut.  Its convexity and the verified rounding theorem yield
`FinitePolyhedron.integerHull_subset_cgClosure`: every CG round preserves the
entire integer hull.  `FinitePolyhedron.recessionCone` records the homogeneous
row directions, and `FinitePolyhedron.mem_recessionCone_iff` proves that, for a
nonempty relaxation, these are exactly the directions along which every
nonnegative displacement preserves feasibility.

An alternative proof uses finite split rank.  A split cut can be compiled by
introducing complementary bounds with `asm`, deriving the cut in each branch
with `lin`, and combining the branches with `uns`.  The CG route is closer to
the existing `RndValid` definition and avoids assumption-index bookkeeping.

## 5. Exact external mathematical ingredients

A complete pen-and-paper proof must cite or prove the following results:

1. normalization of mixed-sense rational rows;
2. rational Farkas infeasibility;
3. rational Farkas certificates for valid inequalities;
4. projection of a rational polyhedron is a rational polyhedron;
5. every nonempty rational polyhedron contains a rational point;
6. polyhedrality and finite generation of one CG closure;
7. finite Chvátal--Gomory rank of every rational polyhedron.

The original VIPR paper uses the checking directions of linear programming
duality, rounding, and branch disjunctions, but does not assemble these results
into a completeness theorem.  Schrijver's finite-rank theorem, or the
equivalent finite-split-rank result, supplies the missing global existence
argument.

Relevant sources:

- Cheung, Gleixner, and Steffy, *Verifying Integer Programming Results*, 2017.
- Schrijver, *On Cutting Planes*, 1980.
- Pashkovich, *Every Rational Polyhedron Has Finite Split Rank*, 2016.
- Mexi et al., *Constructing VIPR Certificates from Black-Box ILP Solvers*,
  2026, for the bounded-branching construction.

## 6. Lean development plan

### Phase A: correct the statement

- Add `ValidSense` and `RowsWellFormed`.
- Strengthen `ProofSystemComplete` with a `RowsWellFormed` hypothesis.
- Remove the unsupported comment that the existing `RefTree` is already known
  complete.

### Phase B: rational LP completeness — complete

- Define normalization from `SLe` to canonical `≤` rows.
- Formalize rational Farkas completeness.
- Map normalized multipliers back to a `RationalFarkasWitness`.
- Prove `lpFragment_complete` without an assumed hypothesis.

The implementation uses constructive Fourier--Motzkin elimination over `ℚ`
with explicit original-row provenance.

### Phase C: bounded MILP completeness — complete at the declarative format level

- Define a high-level refutation tree with rational Farkas leaves and integral
  split nodes.
- Prove that explicit finite bounds produce such a finite tree.
- Compile a valid tree into flat `SStep` replay with correct assumption sets and
  indices.
- Conclude a bounded specialization of `ProofSystemComplete`.

`BoundedCompleteness.bounded_refTree_complete_noDerive` constructs the finite
split tree.  `RefTreeCompile.compileTree` now flattens every valid `RefTree`,
including `derive`/`rnd` nodes, into indexed `SStep` replay while proving
`DerivationValid`, final absurdity, last-entry placement, and exact assumption
support.  Consequently `RefTreeCompile.bounded_proof_complete` proves that
every explicitly bounded infeasible system in this model has a closed flat
VIPR proof.

### Phase D: general MILP completeness

- Define semantic CG cuts and finite derivations. — complete
- Prove that a finite CG refutation compiles to a closed VIPR proof. — complete
- Prove valid-inequality rational Farkas completeness and compile every
  semantic cut to the concrete VIPR `rnd` rule. — complete
- Prove the finite common-rank criterion for an eventually derived, finite
  rationally infeasible integer-hull description. — complete
- Prove exact restriction/extension equivalence between sparse valuations and
  the finite-dimensional rational variable space. — complete
- Realize sparse forms as finite-dimensional rational linear maps and prove
  convexity of every finite row polyhedron. — complete
- Define the rational integer hull and identify its emptiness exactly with
  mixed-integer infeasibility. — complete
- Define semantic CG closure and prove that it contains the integer hull. —
  complete
- Define the rational recession cone and prove its exact operational
  characterization. — complete
- Prove that every rational recession direction has a positive integral
  multiple and that integral feasible points are closed under natural
  displacements along such directions. — complete
- Construct positive common-denominator scales for sparse rational rows and
  prove that each scaled row evaluates integrally on every lattice point. This
  is the arithmetic prerequisite for the Gordan-lemma encoding of recession
  directions. — complete
- Construct one common positive scale for an entire finite row system and
  natural slack witnesses for every scaled inequality at each integral
  recession direction. — complete
- Define the finite natural-number encoding with positive, negative, and row
  slack coordinates; prove that decoding is additive and always yields an
  integral direction. — complete
- Define the additive scaled-row equation and its zero-locus submonoid; prove
  that every element of this solution monoid decodes to an integral recession
  direction. — complete
- Encode every integral recession direction by signed natural coordinates and
  verified natural row slacks, and prove that the decoded solution monoid is
  exactly the set of integral recession directions. — complete
- Apply the formal Gordan lemma to the finite natural-coordinate equation
  kernel and prove that its solution monoid is finitely generated. — complete
- Decode a finite Gordan generating set and prove that its additive closure
  contains every integral recession direction. — complete
- Lift the integral result by positive denominator scaling and characterize
  the full rational recession cone exactly by finite rational generation from
  the decoded Gordan family. — complete
- Construct one common affine scale for all row coefficients and right-hand
  sides, and natural slack witnesses for every integral feasible point. This
  is the arithmetic layer for the inhomogeneous Gordan/Dickson encoding. —
  complete
- Define the affine natural-number solution fiber; prove that its decoded
  image is exactly the integral feasible set, and that adding a homogeneous
  recession encoding preserves this fiber. — complete
- Apply Dickson's lemma to prove that the affine fiber has finitely many
  minimal encodings, and prove that every affine encoding is one of these
  finite bases plus a homogeneous recession encoding. — complete
- Decode the finite affine bases and homogeneous generators to prove that the
  integral feasible set is a finite union of translates of one finitely
  generated integral recession monoid. — complete
- Prove the exact Minkowski-sum identity for the integral feasible set and,
  by convex-hull additivity, the corresponding decomposition of the rational
  integer hull into a finite base polytope plus the convex hull of the
  generated recession monoid. — complete
- Prove generally that the convex hull of a generated additive monoid is the
  rational cone hull of zero and its generators. — complete
- Characterize membership in a finitely generated rational cone by
  nonnegative rational weights, and combine this with the affine
  Gordan--Dickson decomposition to express the integer hull exactly as a
  finite base polytope plus a finitely generated rational cone. — complete
- Encode a finite polytope-plus-cone description as a rational extended
  formulation, eliminate all auxiliary weights by verified
  Fourier--Motzkin projection, and obtain an exact finite halfspace
  description of every rational integer hull. — complete
- Scale and round a finite integer-hull description to finitely many
  integral-left-hand-side rows; prove that they remain valid on all integral
  feasible points and remain jointly rationally infeasible when the integer
  hull is empty. — complete
- Reduce full VIPR completeness to the exact classical finite-rank statement
  that one finitely described semantic CG-closure sequence eventually derives
  every integral inequality valid on the integer points. — complete
- Prove the lattice-free affine-hull base case: if a rational relaxation
  forces an integer-valued form to equal a nonintegral constant, two opposite
  CG cuts give a rank-one rational refutation. — complete
- Prove monotonicity of finite semantic CG refutations under strengthening of
  the initial row context, with early termination if the stronger context is
  already rationally infeasible. — complete
- Prove that explicit integral coordinate bounds make the integral feasible
  set finite, and hence give a finite generating set for the integer hull. —
  complete
- Formalize finite generation of each CG closure and eventual derivation of
  every inequality in a finite integer-hull description.

## 7. Range certificates

Infeasibility completeness does not immediately establish completeness for
every `RTP range` result.

For a feasible rational MILP with a finite optimum:

1. the mixed-integer hull is a rational polyhedron;
2. the valid objective-bound inequality has a finite CG derivation;
3. an optimal solution can be chosen rational after fixing its integer
   coordinates;
4. the bound derivation and rational witness can therefore be encoded in a
   range certificate.

Unboundedness requires separate treatment.  VIPR's range format checks listed
feasible solutions and a one-sided derived objective bound; it does not, by
itself, provide a general recession-ray certificate establishing
unboundedness.  The full completeness claim should therefore state precisely
which finite range claims are covered.
