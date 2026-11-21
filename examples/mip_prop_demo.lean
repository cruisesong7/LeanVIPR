import LeanVIPRTactic

/-!
# From a user's `Prop` to a solver certificate, by hand

What stages 3 to 5 of `docs/TACTIC-TODO.md` will automate, written out. Nothing here is
a tactic: it is the proof term a tactic has to build, which is why it is worth having
first. The whole file is `sorry`-free and its axioms are the standard three.

The certificate below was produced by exact SCIP from this very `Mip`, with
`#mip_scip knapsack` (see `examples/mip_scip_smoke.lean`) and dumped as a Lean literal.
Pasting it in is exactly what stage 3 removes: a tactic will elaborate the same data with
`Qq` and never write a file.

Note what SCIP handed back: it named the variables `t_y t_x t_z` — renamed *and*
permuted — so `C0` lists `(0, 10)` before `(1, 6)` where our `c0` lists `6x` first.
`agreesWith` recovers the renaming itself and compares rows as linear functions, which is
why none of that has to be dealt with here.
-/

open LeanVIPR LeanVIPR.Parser LeanVIPR.Checker LeanVIPR.Impl.Encoder
open LeanVIPR.Semantics LeanVIPR.Semantics.System

/-! ## 1. The problem, in Lean

`6x + 10y + 15z = 23`, `x + y + z ≥ 1`, integer `x ∈ [0,3]`, `y ∈ [0,2]`, `z ∈ [0,1]`.
The linear relaxation is feasible, so the certificate has to branch. -/

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

/-! ## 2. What exact SCIP returned -/

def cert : Vipr :=
  { version := "1.0",
    varNames := #["t_y", "t_x", "t_z"],
    intVars := [0, 1, 2],
    objSense := "min",
    objTerms := [],
    numCon := 8,
    numBounds := 6,
    cons := #[{ name := "C0",
                sense := 'E',
                rhs := 23,
                form := [{ idx := 0, coeff := 10 }, { idx := 1, coeff := 6 }, { idx := 2, coeff := 15 }],
                usesObj := false },
              { name := "C1",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }, { idx := 1, coeff := 1 }, { idx := 2, coeff := 1 }],
                usesObj := false },
              { name := "B2", sense := 'G', rhs := 0, form := [{ idx := 0, coeff := 1 }], usesObj := false },
              { name := "B3", sense := 'L', rhs := 2, form := [{ idx := 0, coeff := 1 }], usesObj := false },
              { name := "B4", sense := 'G', rhs := 0, form := [{ idx := 1, coeff := 1 }], usesObj := false },
              { name := "B5", sense := 'L', rhs := 3, form := [{ idx := 1, coeff := 1 }], usesObj := false },
              { name := "B6", sense := 'G', rhs := 0, form := [{ idx := 2, coeff := 1 }], usesObj := false },
              { name := "B7", sense := 'L', rhs := 1, form := [{ idx := 2, coeff := 1 }], usesObj := false }],
    rtp := LeanVIPR.Parser.ViprRtp.infeas,
    numSol := 0,
    sols := #[],
    ders := #[{ name := "DualBound_8",
                sense := 'G',
                rhs := 0,
                form := [],
                usesObj := true,
                reason := LeanVIPR.Parser.ViprReason.lin [],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "A9",
                sense := 'L',
                rhs := 0,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.asm,
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "A10",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.asm,
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "DualBound_11",
                sense := 'G',
                rhs := 0,
                form := [],
                usesObj := true,
                reason := LeanVIPR.Parser.ViprReason.lin [],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L12",
                sense := 'G',
                rhs := (-58546795155816465 : Rat)/4503599627370496,
                form := [{ idx := 2, coeff := -15 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (10, 10), (4, 6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L13",
                sense := 'L',
                rhs := (3903119677054431 : Rat)/4503599627370496,
                form := [{ idx := 2, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(12, (-1 : Rat)/15)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R14",
                sense := 'L',
                rhs := 0,
                form := [{ idx := 2, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(13, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L15",
                sense := 'G',
                rhs := (-7318349394477057 : Rat)/562949953421312,
                form := [{ idx := 1, coeff := -6 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (6, 15), (10, 10)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L16",
                sense := 'L',
                rhs := (2439449798159019 : Rat)/1125899906842624,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(15, (-1 : Rat)/6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R17",
                sense := 'L',
                rhs := 2,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(16, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L18",
                sense := 'L',
                rhs := (-27021597764222973 : Rat)/9007199254740992,
                form := [{ idx := 1, coeff := -6 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (14, 15), (3, 10)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L19",
                sense := 'G',
                rhs := (9007199254740991 : Rat)/18014398509481984,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(18, (-1 : Rat)/6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R20",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(19, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L21",
                sense := 'G',
                rhs := (-9570149208162305 : Rat)/562949953421312,
                form := [{ idx := 0, coeff := -10 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (6, 15), (20, 6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L22",
                sense := 'L',
                rhs := (1914029841632461 : Rat)/1125899906842624,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(21, (-1 : Rat)/10)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R23",
                sense := 'L',
                rhs := 1,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(22, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L24",
                sense := 'L',
                rhs := (-24769797950537725 : Rat)/2251799813685248,
                form := [{ idx := 0, coeff := -10 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (14, 15), (17, 6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L25",
                sense := 'G',
                rhs := (4953959590107545 : Rat)/4503599627370496,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(24, (-1 : Rat)/10)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R26",
                sense := 'G',
                rhs := 2,
                form := [{ idx := 0, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(25, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ActivityConflict27",
                sense := 'L',
                rhs := -1,
                form := [],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (23, 10), (17, 6), (14, 15)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "DualBound_28",
                sense := 'G',
                rhs := 0,
                form := [],
                usesObj := true,
                reason := LeanVIPR.Parser.ViprReason.lin [],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L29",
                sense := 'L',
                rhs := (-90071992547409915 : Rat)/18014398509481984,
                form := [{ idx := 2, coeff := -15 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (9, 10), (5, 6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L30",
                sense := 'G',
                rhs := (6004799503160661 : Rat)/18014398509481984,
                form := [{ idx := 2, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(29, (-1 : Rat)/15)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R31",
                sense := 'G',
                rhs := 1,
                form := [{ idx := 2, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(30, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L32",
                sense := 'G',
                rhs := (-9007199254740993 : Rat)/1125899906842624,
                form := [{ idx := 1, coeff := -6 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (31, 15), (2, 10)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L33",
                sense := 'L',
                rhs := (3002399751580331 : Rat)/2251799813685248,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(32, (-1 : Rat)/6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R34",
                sense := 'L',
                rhs := 1,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(33, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L35",
                sense := 'L',
                rhs := (-18014398509481983 : Rat)/2251799813685248,
                form := [{ idx := 1, coeff := -6 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (7, 15), (9, 10)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_L36",
                sense := 'G',
                rhs := (6004799503160661 : Rat)/4503599627370496,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(35, (-1 : Rat)/6)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ACT_R37",
                sense := 'G',
                rhs := 2,
                form := [{ idx := 1, coeff := 1 }],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.rnd [(36, 1)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "ActivityConflict38",
                sense := 'L',
                rhs := -2,
                form := [],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.lin [(0, -1), (9, 10), (34, 6), (7, 15)],
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent },
              { name := "UnsplitNode1_39",
                sense := 'G',
                rhs := 1,
                form := [],
                usesObj := false,
                reason := LeanVIPR.Parser.ViprReason.uns 27 10 38 9,
                idx := -1,
                scope := LeanVIPR.Parser.ViprScope.absent }] }

/-! ## 3. The two `Bool`s, decided by the kernel

These are the only hypotheses `pipeline_infeasible` has, and both are decided against the
`Mip` and the `Vipr` as data — no file, no solver, no parser in sight. `decide +kernel`
rather than `decide` because the whole point is that Lean's kernel, not its compiler,
performs the check; `native_decide` would add a per-theorem axiom and is not used
anywhere in this development. -/

theorem agreed : agreesWith knapsack cert = true := by decide +kernel

theorem accepted : checkVipr cert = true := by decide +kernel

theorem isInfeas : cert.rtp = .infeas := by decide +kernel

/-! ## 4. The problem is infeasible -/

theorem knapsack_infeasible : knapsack.Infeasible :=
  Mip.pipeline_infeasible agreed accepted isInfeas

/-! ## 5. The statement a user would have written

`Mip.Infeasible` is about *real* valuations with the declared variables integral;
this is about integer tuples. `Mip.absurd_of_infeasible` is the bridge, and integrality
costs nothing there — a valuation built by casting integers is integral at every index.
What remains is per-row, finite, and closes by automation. -/

theorem knapsack_unsolvable :
    ¬ ∃ x y z : ℤ, 0 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 2 ∧ 0 ≤ z ∧ z ≤ 1 ∧
                   6*x + 10*y + 15*z = 23 ∧ x + y + z ≥ 1 := by
  rintro ⟨x, y, z, hx0, hx3, hy0, hy2, hz0, hz1, heq, hge⟩
  refine Mip.absurd_of_infeasible knapsack_infeasible [x, y, z] ?_
  -- the rows live over ℝ, so move each integer hypothesis across the cast
  have hx0' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx3' : (x : ℝ) ≤ 3 := by exact_mod_cast hx3
  have hy0' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
  have hy2' : (y : ℝ) ≤ 2 := by exact_mod_cast hy2
  have hz0' : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz0
  have hz1' : (z : ℝ) ≤ 1 := by exact_mod_cast hz1
  have heq' : 6 * (x : ℝ) + 10 * (y : ℝ) + 15 * (z : ℝ) = 23 := by exact_mod_cast heq
  have hge' : 1 ≤ (x : ℝ) + (y : ℝ) + (z : ℝ) := by exact_mod_cast hge
  intro c hc
  -- `conSLes` computes: the two explicit rows, then one row per finite variable bound,
  -- lower before upper, in index order.
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

#print axioms knapsack_unsolvable
