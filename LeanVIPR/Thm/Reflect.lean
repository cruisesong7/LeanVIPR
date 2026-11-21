module

public import LeanVIPR.Spec.Mip

@[expose] public section

/-!
# From an infeasible `Mip` to a `Prop` about integers

`Mip.Infeasible` says no *real* valuation with the declared variables integral is
feasible. A user asks something narrower-looking: that no tuple of integers satisfies
their constraints. This file is the bridge, and it is the whole mathematical content of a
`Prop`-level front end — everything else such a front end does is syntax matching, which
belongs in metacode and carries no proof obligation of its own.

The bridge is short because integrality comes for free. A valuation built by casting
integers satisfies `IsIntReal` at *every* index, not merely at the declared integer ones,
so the first component of `Mip.Feasible` is discharged without reference to `intVars`.
What remains for a caller to supply is exactly the interesting part: that the rows hold.

Nothing here mentions MPS or certificates. It is the `Prop`-facing end of `Spec/Mip.lean`,
usable the moment a pipeline theorem produces an `m.Infeasible`.
-/

namespace LeanVIPR.Mip

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Semantics.System

/-! ## Computing a witness valuation

Without these a reflected goal stalls on `valuationOfInts [x, y, z] 0` as an opaque term,
so they are what makes the row obligation mechanical rather than merely finite. -/

@[simp] theorem valuationOfInts_cons_zero (x : ℤ) (xs : List ℤ) :
    valuationOfInts (x :: xs) 0 = (x : ℝ) := rfl

@[simp] theorem valuationOfInts_cons_succ (x : ℤ) (xs : List ℤ) (j : Nat) :
    valuationOfInts (x :: xs) (j + 1) = valuationOfInts xs j := rfl

@[simp] theorem valuationOfInts_nil (j : Nat) : valuationOfInts [] j = 0 := by
  simp [valuationOfInts]

/-- A valuation built from integers is integral at every index. -/
theorem isIntReal_valuationOfInts (xs : List ℤ) (j : Nat) :
    IsIntReal (valuationOfInts xs j) :=
  ⟨xs.getD j 0, rfl⟩

/-- An integer tuple satisfying every row is a feasible point. The integrality half of
`Feasible` needs no hypothesis. -/
theorem feasible_valuationOfInts {m : Mip} {xs : List ℤ}
    (hrows : ∀ c ∈ m.conSLes, satReal c (valuationOfInts xs)) :
    m.Feasible (valuationOfInts xs) :=
  ⟨fun j _ => isIntReal_valuationOfInts xs j, hrows⟩

/-- **The front end's bridge.** An infeasible `Mip` rules out every integer tuple. A
tactic reflecting a goal `¬ ∃ x y z : ℤ, …` into `m` discharges it by this, leaving only
`hrows` — a finite, concrete list of real inequalities over integer casts — to close. -/
theorem absurd_of_infeasible {m : Mip} (h : m.Infeasible) (xs : List ℤ)
    (hrows : ∀ c ∈ m.conSLes, satReal c (valuationOfInts xs)) : False :=
  h _ (feasible_valuationOfInts hrows)

/-! ## Mixed problems

When some variables are rational or real, integrality no longer comes for free: only the
declared integer variables are integral, so the caller supplies that half as well. The
valuation is a list of reals — the user's variables, each cast to `ℝ` — so a natural, an
integer, a rational and a real variable can sit in one problem. -/

/-- The valuation sending variable `j` to the `j`-th entry of `xs`, and `0` past the end. -/
def valuationOfReals (xs : List ℝ) : RealValuation := fun j => xs.getD j 0

@[simp] theorem valuationOfReals_cons_zero (x : ℝ) (xs : List ℝ) :
    valuationOfReals (x :: xs) 0 = x := rfl

@[simp] theorem valuationOfReals_cons_succ (x : ℝ) (xs : List ℝ) (j : Nat) :
    valuationOfReals (x :: xs) (j + 1) = valuationOfReals xs j := rfl

@[simp] theorem valuationOfReals_nil (j : Nat) : valuationOfReals [] j = 0 := by
  simp [valuationOfReals]

/-! Literal indices: `simp` folds `0 + 1` to `1` before `valuationOfReals_cons_succ` can see
the `+ 1`, so an index that arrives as a numeral needs its own lemmas. -/

theorem valuationOfReals_cons_pos (x : ℝ) (xs : List ℝ) {j : Nat} (hj : 0 < j) :
    valuationOfReals (x :: xs) j = valuationOfReals xs (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rfl

@[simp] theorem valuationOfReals_cons_one (x : ℝ) (xs : List ℝ) :
    valuationOfReals (x :: xs) 1 = valuationOfReals xs 0 := rfl

@[simp] theorem valuationOfReals_cons_ofNat (x : ℝ) (xs : List ℝ) (n : Nat) [n.AtLeastTwo] :
    valuationOfReals (x :: xs) (OfNat.ofNat n) = valuationOfReals xs (OfNat.ofNat n - 1) :=
  valuationOfReals_cons_pos x xs (by have := Nat.AtLeastTwo.prop (n := n); show 0 < n; omega)

theorem isIntReal_intCast (z : ℤ) : IsIntReal (z : ℝ) := ⟨z, rfl⟩

theorem isIntReal_natCast (n : ℕ) : IsIntReal (n : ℝ) := ⟨n, by push_cast; rfl⟩

/-- **The bridge for mixed problems.** An infeasible `Mip` rules out every real tuple that
is integral where the problem declares integer variables and satisfies every row. -/
theorem absurd_of_infeasible_real {m : Mip} (h : m.Infeasible) (xs : List ℝ)
    (hint : ∀ j ∈ m.intVars, IsIntReal (valuationOfReals xs j))
    (hrows : ∀ c ∈ m.conSLes, satReal c (valuationOfReals xs)) : False :=
  h _ ⟨hint, hrows⟩

/-- With the integer variables first — `zs` their values, `rs` the rest, cast to `ℝ` —
integrality holds by construction. What is left to check about it is that every declared
integer variable is among the first `n`, a decidable fact about the problem alone, and that
there are `n` integer values. -/
theorem feasible_mixed {m : Mip} (n : Nat)
    (hint : ∀ j ∈ m.intVars, j < n) (zs : List ℤ) (hlen : zs.length = n) (rs : List ℝ)
    (hrows : ∀ c ∈ m.conSLes,
      satReal c (valuationOfReals (zs.map (Int.cast : ℤ → ℝ) ++ rs))) :
    m.Feasible (valuationOfReals (zs.map (Int.cast : ℤ → ℝ) ++ rs)) := by
  refine ⟨fun j hj => ?_, hrows⟩
  have hlt : j < zs.length := hlen ▸ hint j hj
  have hlt' : j < (zs.map (Int.cast : ℤ → ℝ)).length := by simpa using hlt
  refine ⟨zs[j], ?_⟩
  simp only [valuationOfReals, List.getD_append _ _ _ _ hlt', List.getD_eq_getElem _ _ hlt',
    List.getElem_map]

/-- **The bridge `mip` uses.** An infeasible `Mip` rules out the user's values, given in
the order of `feasible_mixed`. -/
theorem absurd_of_infeasible_mixed {m : Mip} (h : m.Infeasible) (n : Nat)
    (hint : ∀ j ∈ m.intVars, j < n) (zs : List ℤ) (hlen : zs.length = n) (rs : List ℝ)
    (hrows : ∀ c ∈ m.conSLes,
      satReal c (valuationOfReals (zs.map (Int.cast : ℤ → ℝ) ++ rs))) : False :=
  h _ (feasible_mixed n hint zs hlen rs hrows)

/-! ## Building a problem with its specification attached

The analogue of Trestle's `VEncCNF` index, at the layer where it belongs: between the
user's predicate and the reified problem. (Not between the problem and the MPS text —
Trestle does not verify its DIMACS printing either, and for the same reason we need not
verify ours: the returned proof is checked against the reified data, so a bad print causes
a rejection rather than a wrong theorem.)

`VRows P` is a row list carrying, in its type, the proof that those rows denote exactly
`P`. Rows are added with `VRows.cons`, and the index conjoins automatically, so there is
never a separate theorem to prove about the finished list — which is the whole point of
the discipline.
-/

namespace Build

/-- A list of rows together with the predicate it denotes. -/
structure VRows (P : RealValuation → Prop) where
  rows : List SLe
  spec : ∀ a, (∀ c ∈ rows, satReal c a) ↔ P a

/-- No rows constrain nothing. -/
def nil : VRows (fun _ => True) where
  rows := []
  spec := by simp

/-- One more row conjoins one more conjunct onto the index. -/
def cons (c : SLe) {P : RealValuation → Prop} (v : VRows P) :
    VRows (fun a => satReal c a ∧ P a) where
  rows := c :: v.rows
  spec := by
    intro a
    constructor
    · intro h
      exact ⟨h c (by simp), (v.spec a).mp (fun d hd => h d (by simp [hd]))⟩
    · intro ⟨hc, hP⟩ d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact (v.spec a).mpr hP d hd

/-! ### What the index buys

`absurd_of_infeasible` asks a caller for `∀ c ∈ m.conSLes, satReal c (valuationOfInts xs)`,
which for a concrete problem means discharging each row by hand. With a `VRows P` the rows
half comes from the index instead, so a caller supplies `P` — their own predicate, in their
own terms — and nothing about rows at all. -/

/-- A problem whose explicit rows were built with their specification attached: if an
integer tuple satisfies `P` and the variable bounds, the valuation is feasible. -/
theorem feasible_of_spec {P : RealValuation → Prop} (v : VRows P) (m : Mip)
    (hrows : m.rowSLes = v.rows) (xs : List ℤ)
    (hP : P (valuationOfInts xs))
    (hb : ∀ c ∈ m.boundSLes, satReal c (valuationOfInts xs)) :
    m.Feasible (valuationOfInts xs) := by
  refine feasible_valuationOfInts ?_
  intro c hc
  rcases List.mem_append.mp (by simpa [Mip.conSLes] using hc) with h | h
  · exact (v.spec _).mpr hP c (by rwa [hrows] at h)
  · exact hb c h

/-- **The front end's bridge, with the rows discharged by the index.** An infeasible
problem rules out every integer tuple satisfying the predicate its rows were built from. -/
theorem absurd_of_spec {P : RealValuation → Prop} (v : VRows P) {m : Mip}
    (hinf : m.Infeasible) (hrows : m.rowSLes = v.rows) (xs : List ℤ)
    (hP : P (valuationOfInts xs))
    (hb : ∀ c ∈ m.boundSLes, satReal c (valuationOfInts xs)) : False :=
  hinf _ (feasible_of_spec v m hrows xs hP hb)

end Build

end LeanVIPR.Mip
