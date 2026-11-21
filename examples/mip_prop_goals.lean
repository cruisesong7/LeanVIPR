import LeanVIPRTactic

/-!
# The goals `mip` has to take directly

This file is the **goal surface**: the `Prop`s a user writes, in the shapes they write
them in. Stage 4 of `docs/TACTIC-TODO.md` is the metacode that recognizes these and builds
the `Mip`; stage 5 is the tactic that then closes them. Until those exist, each theorem
here is proved by the recipe a tactic would emit, so the file doubles as the acceptance
list for the reflector: every statement below must become `by mip`, and the proof beside
it is what `mip` has to produce.

Three sections, with different jobs:

1. **One problem, five phrasings.** All five must reflect to the same `Mip`. This is the
   syntactic work, and it carries no mathematical content — which is the point.
2. **Where this is the only route.** A goal with rational coefficients over `ℝ`, proved
   end to end from a real certificate. `omega` cannot state it; `linarith` cannot prove it,
   because the LP relaxation is feasible and only integrality rules the point out.
3. **What `omega` already does.** Measured, and honestly: on section 1's goal `omega` wins.
   Saying where the MIP route earns its place matters more than pretending it always does.
-/

open LeanVIPR LeanVIPR.Parser LeanVIPR.Checker LeanVIPR.Impl.Encoder
open LeanVIPR.Semantics LeanVIPR.Semantics.System

/-! ## 1. One problem, five ways a user might state it

`6x + 10y + 15z = 23`, `x + y + z ≥ 1`, integer `x ∈ [0,3]`, `y ∈ [0,2]`, `z ∈ [0,1]`. -/

def knapsack : Mip where
  vars := #[{ name := "x", isInt := true, lo := some 0, hi := some 3 },
            { name := "y", isInt := true, lo := some 0, hi := some 2 },
            { name := "z", isInt := true, lo := some 0, hi := some 1 }]
  objSense := .min
  obj := []
  rows := #[{ name := "c0", sense := 'E', rhs := 23,
              form := [⟨0, 6⟩, ⟨1, 10⟩, ⟨2, 15⟩] },
            { name := "c1", sense := 'G', rhs := 1,
              form := [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] }]

/-- **The row obligation, once.** Every phrasing below funnels into this: an integer tuple
satisfying the user's constraints satisfies every row of `conSLes`, bounds included. This
is the half of stage 4 that is arithmetic rather than syntax, and the half a tactic has to
emit per goal. Stated over `ℤ` hypotheses because that is how a user states them; the
casts into `ℝ` happen here, in one place. -/
theorem knapsack_rows {x y z : ℤ}
    (hx0 : 0 ≤ x) (hx3 : x ≤ 3) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (heq : 6 * x + 10 * y + 15 * z = 23) (hge : 1 ≤ x + y + z) :
    ∀ c ∈ knapsack.conSLes, satReal c (Mip.valuationOfInts [x, y, z]) := by
  have hx0' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx3' : (x : ℝ) ≤ 3 := by exact_mod_cast hx3
  have hy0' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
  have hy2' : (y : ℝ) ≤ 2 := by exact_mod_cast hy2
  have hz0' : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz0
  have hz1' : (z : ℝ) ≤ 1 := by exact_mod_cast hz1
  have heq' : 6 * (x : ℝ) + 10 * (y : ℝ) + 15 * (z : ℝ) = 23 := by exact_mod_cast heq
  have hge' : 1 ≤ (x : ℝ) + (y : ℝ) + (z : ℝ) := by exact_mod_cast hge
  intro c hc
  have hcs : knapsack.conSLes =
      [⟨'E', [⟨0, 6⟩, ⟨1, 10⟩, ⟨2, 15⟩], 23⟩,
       ⟨'G', [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], 1⟩,
       ⟨'G', [⟨0, 1⟩], 0⟩, ⟨'L', [⟨0, 1⟩], 3⟩,
       ⟨'G', [⟨1, 1⟩], 0⟩, ⟨'L', [⟨1, 1⟩], 2⟩,
       ⟨'G', [⟨2, 1⟩], 0⟩, ⟨'L', [⟨2, 1⟩], 1⟩] := by rfl
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [satReal, evalReal, List.map, List.sum_cons, List.sum_nil,
      Mip.valuationOfInts_cons_zero, Mip.valuationOfInts_cons_succ]
    norm_num
    linarith

/-! Each theorem below takes `knapsack.Infeasible` as a hypothesis. It is discharged from
a real certificate in `examples/mip_prop_demo.lean`; taking it as a hypothesis here keeps
this file free of a 280-line certificate literal and of any need for a solver. The point
of these five is the *goal shape*, not where infeasibility comes from. -/

/-- **The canonical shape.** A negated existential over `ℤ`, bounds and rows as one
conjunction. -/
theorem knapsack_unsolvable (hinf : knapsack.Infeasible) :
    ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                   6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by
  rintro ⟨x, y, z, hx0, hx3, hy0, hy2, hz0, hz1, heq, hge⟩
  exact Mip.absurd_of_infeasible hinf [x, y, z]
    (knapsack_rows hx0 hx3 hy0 hy2 hz0 hz1 heq hge)

/-- The same thing with the quantifier the other way up, which is how it reads when it
comes out of a larger development. -/
theorem knapsack_forall_false (hinf : knapsack.Infeasible) :
    ∀ x y z : ℤ, 0 ≤ x → x ≤ 3 → 0 ≤ y → y ≤ 2 → 0 ≤ z → z ≤ 1 →
      6*x + 10*y + 15*z = 23 → x + y + z ≥ 1 → False := by
  intro x y z hx0 hx3 hy0 hy2 hz0 hz1 heq hge
  exact Mip.absurd_of_infeasible hinf [x, y, z]
    (knapsack_rows hx0 hx3 hy0 hy2 hz0 hz1 heq hge)

/-- One row moved into the conclusion as a `≠`. The reflector has to put it back: a goal
`f ≠ c` is the row `f = c` on the hypothesis side. -/
theorem knapsack_ne (hinf : knapsack.Infeasible) :
    ∀ x y z : ℤ, 0 ≤ x → x ≤ 3 → 0 ≤ y → y ≤ 2 → 0 ≤ z → z ≤ 1 → x + y + z ≥ 1 →
      6*x + 10*y + 15*z ≠ 23 := by
  intro x y z hx0 hx3 hy0 hy2 hz0 hz1 hge heq
  exact Mip.absurd_of_infeasible hinf [x, y, z]
    (knapsack_rows hx0 hx3 hy0 hy2 hz0 hz1 heq hge)

/-- Strict bounds, which over `ℤ` are the same bounds. `x < 4` has to become `hi := 3`,
not a row — a strict row is not expressible in MPS, and `omega` is what closes the gap
in the emitted proof. -/
theorem knapsack_strict_bounds (hinf : knapsack.Infeasible) :
    ¬ ∃ x y z : ℤ, -1 < x ∧ x < 4 ∧ -1 < y ∧ y < 3 ∧ -1 < z ∧ z < 2 ∧
                   6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by
  rintro ⟨x, y, z, hx0, hx3, hy0, hy2, hz0, hz1, heq, hge⟩
  exact Mip.absurd_of_infeasible hinf [x, y, z]
    (knapsack_rows (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      heq hge)

/-- Rows written the other way round, with constants on the left and a subtraction. Same
problem; the reflector normalizes. -/
theorem knapsack_rearranged (hinf : knapsack.Infeasible) :
    ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                   23 = 6*x + 10*y + 15*z ∧ 1 - x - y ≤ z := by
  rintro ⟨x, y, z, hx0, hx3, hy0, hy2, hz0, hz1, heq, hge⟩
  exact Mip.absurd_of_infeasible hinf [x, y, z]
    (knapsack_rows hx0 hx3 hy0 hy2 hz0 hz1 (by omega) (by omega))

/-! ## 2. Where this is the only route: rational coefficients

`(1/2)x + (1/3)y = 3/4`, integer `x, y ∈ [0,2]`. The LP relaxation is feasible —
`x = 3/2, y = 0` — so no amount of `linarith` closes it; the integers `{0,1,2}²` give
`0, 1/3, 2/3, 1/2, 5/6, 7/6, 1, 4/3, 5/3` and never `3/4`. And `omega` cannot state the
goal at all: the coefficients are not integers.

This one is proved **end to end**, with the certificate exact SCIP returned inlined, so
nothing here is hypothetical. Sixteen derivations, four of them `rnd` — the integer
rounding rule is exactly what does the work `linarith` cannot.

Worth looking at the numbers in that certificate: `-6004799503160661/9007199254740992` is
the double nearest `-2/3`, written exactly. Exact SCIP derives bounds in floating point
and records them as the exact dyadic rationals they are, then `rnd` lifts them to integer
bounds. Exact does not mean tidy. -/

def frac : Mip where
  vars := #[{ name := "x", isInt := true, lo := some 0, hi := some 2 },
            { name := "y", isInt := true, lo := some 0, hi := some 2 }]
  objSense := .min
  obj := []
  rows := #[{ name := "c0", sense := 'E', rhs := 3/4, form := [⟨0, 1/2⟩, ⟨1, 1/3⟩] }]

def fracCert : Vipr :=
  { version := "1.0",
    varNames := #["t_x", "t_y"],
    intVars := [0, 1],
    objSense := "min",
    objTerms := [],
    numCon := 5,
    numBounds := 4,
    cons := #[{ name := "C0",
                sense := 'E',
                rhs := (3 : Rat)/4,
                form := [{ idx := 0, coeff := (1 : Rat)/2 }, { idx := 1, coeff := (1 : Rat)/3 }],
                usesObj := false },
              { name := "B1", sense := 'G', rhs := 0, form := [{ idx := 0, coeff := 1 }], usesObj := false },
              { name := "B2", sense := 'L', rhs := 2, form := [{ idx := 0, coeff := 1 }], usesObj := false },
              { name := "B3", sense := 'G', rhs := 0, form := [{ idx := 1, coeff := 1 }], usesObj := false },
              { name := "B4", sense := 'L', rhs := 2, form := [{ idx := 1, coeff := 1 }], usesObj := false }],
    rtp := LeanVIPR.Parser.ViprRtp.infeas,
    numSol := 0,
    sols := #[],
    ders := #[{ name := "ACT_L5",
                sense := 'G',
                rhs := (-3 : Rat)/4,
                form := [{ idx := 0, coeff := (-1 : Rat)/2 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (3, (1 : Rat)/3)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L6",
                sense := 'L',
                rhs := (3 : Rat)/2,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(5, -2)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R7",
                sense := 'L',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(6, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "GlobalBound_8",
                sense := 'L',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(7, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.global },
              { name := "ACT_L9",
                sense := 'L',
                rhs := (-375299968947541 : Rat)/4503599627370496,
                form := [{ idx := 0, coeff := (-1 : Rat)/2 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (4, (1 : Rat)/3)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L10",
                sense := 'G',
                rhs := (375299968947541 : Rat)/2251799813685248,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(9, -2)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R11",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(10, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "GlobalBound_12",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(11, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.global },
              { name := "ACT_L13",
                sense := 'G',
                rhs := (-6755399441055745 : Rat)/27021597764222976,
                form := [{ idx := 1, coeff := (-1 : Rat)/3 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (11, (1 : Rat)/2)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L14",
                sense := 'L',
                rhs := (6755399441055745 : Rat)/9007199254740992,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(13, -3)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R15",
                sense := 'L',
                rhs := 0,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(14, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "GlobalBound_16",
                sense := 'L',
                rhs := 0,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(15, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.global },
              { name := "ACT_L17",
                sense := 'L',
                rhs := (-6755399441055743 : Rat)/27021597764222976,
                form := [{ idx := 1, coeff := (-1 : Rat)/3 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (7, (1 : Rat)/2)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L18",
                sense := 'G',
                rhs := (6755399441055743 : Rat)/9007199254740992,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(17, -3)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R19",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(18, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ActivityConflict20",
                sense := 'L',
                rhs := (-1 : Rat)/4,
                form := [],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (7, (1 : Rat)/2), (15, (1 : Rat)/3)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent }] }

theorem frac_agreed   : agreesWith frac fracCert = true := by decide +kernel
theorem frac_accepted : checkVipr fracCert = true       := by decide +kernel
theorem frac_infeas   : fracCert.rtp = .infeas          := by decide +kernel

theorem frac_infeasible : frac.Infeasible :=
  Mip.pipeline_infeasible frac_agreed frac_accepted frac_infeas

/-- **The goal, proved.** Integer unknowns, rational coefficients, stated over `ℝ` because
that is where the rows live. This is the shape `mip` has to take directly, and the one
with no alternative in mathlib today. -/
theorem frac_unsolvable :
    ¬ ∃ x y : ℤ, 0 ≤ x ∧ x ≤ 2 ∧ 0 ≤ y ∧ y ≤ 2 ∧
                 (1/2 : ℝ) * (x : ℝ) + (1/3 : ℝ) * (y : ℝ) = 3/4 := by
  rintro ⟨x, y, hx0, hx2, hy0, hy2, heq⟩
  refine Mip.absurd_of_infeasible frac_infeasible [x, y] ?_
  have hx0' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx2' : (x : ℝ) ≤ 2 := by exact_mod_cast hx2
  have hy0' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
  have hy2' : (y : ℝ) ≤ 2 := by exact_mod_cast hy2
  intro c hc
  have hcs : frac.conSLes =
      [⟨'E', [⟨0, 1/2⟩, ⟨1, 1/3⟩], 3/4⟩,
       ⟨'G', [⟨0, 1⟩], 0⟩, ⟨'L', [⟨0, 1⟩], 2⟩,
       ⟨'G', [⟨1, 1⟩], 0⟩, ⟨'L', [⟨1, 1⟩], 2⟩] := by rfl
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [satReal, evalReal, List.map, List.sum_cons, List.sum_nil,
      Mip.valuationOfInts_cons_zero, Mip.valuationOfInts_cons_succ]
    norm_num
    linarith

#print axioms frac_unsolvable

/-! ## 3. What `omega` already does

Measured: `omega` closes section 1's goal outright, in well under a second. It decides
linear integer arithmetic, and a bounded all-integer feasibility question is squarely
inside that. Anyone shown the knapsack and told it needs a solver is being misled. -/

example : ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                         6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by
  rintro ⟨x, y, z, hx0, hx3, hy0, hy2, hz0, hz1, heq, hge⟩
  omega

/-! So what the MIP route adds is not "integer arithmetic", it is:

* **data `omega` has no language for** — rational coefficients, as in section 2, and
  continuous variables alongside integer ones, which is the `Mip` in its general form;
* **claims that are not feasibility** — an objective bound, or an optimal point with a
  certificate for its optimality (`pipeline_lower_bound`, `pipeline_optimal_min`);
* **scale** — `omega`'s cost is in the formula; ours is in checking a certificate someone
  else searched for. `benchmarks/` holds certificates with tens of thousands of steps,
  from problems no decision procedure in mathlib will touch.

The honest framing for a paper, and for a user: `mip` is not a better `omega`. It is the
tactic for when the question has left `omega`'s language. -/
