module

public import LeanVIPR.Completeness.FarkasCompleteness

@[expose] public section

/-!
# Completeness for explicitly bounded integer variables

This module constructs a finite `RefTree` whenever every remaining integer
variable has an explicit finite integral interval.  The tree branches through
each interval and closes its leaves using constructive rational Farkas
completeness.
-/

namespace LeanVIPR.Completeness.BoundedCompleteness

open LeanVIPR.Cert LeanVIPR.Completeness.FarkasCompleteness

/-- A finite integral interval `[lower, lower + width]` for one variable. -/
structure Interval where
  idx : Nat
  lower : ℤ
  width : Nat
  deriving DecidableEq

def Interval.lowerRow (s : Interval) : Le :=
  leUpper s.idx (((s.lower - 1 : ℤ) : ℚ))

def Interval.upperRow (s : Interval) : Le :=
  leLower s.idx (((s.lower + (s.width : ℤ) : ℤ) : ℚ))

def BoundsPresent (rows : List Le) (specs : List Interval) : Prop :=
  ∀ s ∈ specs, s.lowerRow ∈ rows ∧ s.upperRow ∈ rows

def NoIntSolution (specs : List Interval) (rows : List Le) : Prop :=
  ∀ a : Valuation,
    (∀ s ∈ specs, IsIntVal (a s.idx)) →
    (∀ c ∈ rows, Le.sat c a) →
    False

def intervalMeasure (specs : List Interval) : Nat :=
  (specs.map fun s => s.width + 1).sum

theorem lowerRow_sat {s : Interval} {a : Valuation}
    (h : Le.sat s.lowerRow a) :
    (s.lower : ℚ) ≤ a s.idx := by
  have h' := (sat_leUpper a s.idx (((s.lower - 1 : ℤ) : ℚ))).mp h
  norm_num at h' ⊢
  exact h'

theorem upperRow_sat {s : Interval} {a : Valuation}
    (h : Le.sat s.upperRow a) :
    a s.idx ≤ ((s.lower + (s.width : ℤ) : ℤ) : ℚ) := by
  exact (sat_leLower a s.idx (((s.lower + (s.width : ℤ) : ℤ) : ℚ))).mp h

theorem fixed_of_zero_width {s : Interval} (hwidth : s.width = 0)
    {a : Valuation} (hlower : Le.sat s.lowerRow a)
    (hupper : Le.sat s.upperRow a) :
    a s.idx = (s.lower : ℚ) := by
  have hlo := lowerRow_sat hlower
  have hup := upperRow_sat hupper
  simp [hwidth] at hup
  exact le_antisymm hup hlo

theorem successor_upperRow {idx : Nat} {lower : ℤ} {width : Nat} :
    (Interval.mk idx (lower + 1) width).upperRow =
      (Interval.mk idx lower (width + 1)).upperRow := by
  unfold Interval.upperRow leLower
  apply congrArg (fun rhs : ℚ => (Le.mk [⟨idx, 1⟩] rhs))
  push_cast
  ring

theorem next_lowerRow (s : Interval) (width : Nat) :
    (Interval.mk s.idx (s.lower + 1) width).lowerRow =
      leUpper s.idx (s.lower : ℚ) := by
  simp [Interval.lowerRow, leUpper]

theorem next_upperRow (s : Interval) {width : Nat} (hwidth : s.width = width + 1) :
    (Interval.mk s.idx (s.lower + 1) width).upperRow = s.upperRow := by
  cases s with
  | mk idx lower oldWidth =>
      simp only at hwidth
      subst oldWidth
      exact successor_upperRow

noncomputable def buildTree (isInt : Nat → Prop) (specs : List Interval)
    (rows : List Le)
    (hIsInt : ∀ s ∈ specs, isInt s.idx)
    (hBounds : BoundsPresent rows specs)
    (hinfeasible : NoIntSolution specs rows) :
    {tree : RefTree // RefTree.Valid isInt rows tree ∧ tree.NoDerive} := by
  match specs with
  | [] =>
      have hrat : RatInfeasible rows := by
        intro a hrows
        exact hinfeasible a (by simp) hrows
      let cert := Classical.choice (rationalFarkas_complete_le hrat)
      exact ⟨.leaf (resolveLe rows cert.comb), cert.refTreeValid isInt, trivial⟩
  | s :: rest =>
      match hwidth : s.width with
      | 0 =>
          have hrestBounds : BoundsPresent rows rest := by
            intro t ht
            exact hBounds t (by simp [ht])
          have hrestIsInt : ∀ t ∈ rest, isInt t.idx := by
            intro t ht
            exact hIsInt t (by simp [ht])
          have hrestInfeasible : NoIntSolution rest rows := by
            intro a hint hrows
            have hsBounds := hBounds s (by simp)
            have hsFixed :=
              fixed_of_zero_width hwidth (hrows s.lowerRow hsBounds.1)
                (hrows s.upperRow hsBounds.2)
            apply hinfeasible a
            · intro t ht
              rcases List.mem_cons.mp ht with ht | ht
              · have hidx : t.idx = s.idx := congrArg Interval.idx ht
                rw [hidx]
                exact ⟨s.lower, hsFixed⟩
              · exact hint t ht
            · exact hrows
          exact buildTree isInt rest rows hrestIsInt hrestBounds hrestInfeasible
      | width + 1 =>
          let lowerBranch := leLower s.idx (s.lower : ℚ)
          let upperBranch := leUpper s.idx (s.lower : ℚ)
          let next : Interval := ⟨s.idx, s.lower + 1, width⟩
          have hsInt : isInt s.idx := hIsInt s (by simp)
          have hsBounds := hBounds s (by simp)
          have hloBounds : BoundsPresent (lowerBranch :: rows) rest := by
            intro t ht
            obtain ⟨htLower, htUpper⟩ := hBounds t (by simp [ht])
            exact ⟨List.mem_cons_of_mem _ htLower, List.mem_cons_of_mem _ htUpper⟩
          have hloIsInt : ∀ t ∈ rest, isInt t.idx := by
            intro t ht
            exact hIsInt t (by simp [ht])
          have hloInfeasible : NoIntSolution rest (lowerBranch :: rows) := by
            intro a hint hrows
            have hbranch : a s.idx ≤ (s.lower : ℚ) := by
              exact (sat_leLower a s.idx (s.lower : ℚ)).mp
                (hrows lowerBranch (by simp [lowerBranch]))
            have hlower : (s.lower : ℚ) ≤ a s.idx :=
              lowerRow_sat (hrows s.lowerRow (by simp [hsBounds.1]))
            have hsFixed : a s.idx = (s.lower : ℚ) := le_antisymm hbranch hlower
            apply hinfeasible a
            · intro t ht
              rcases List.mem_cons.mp ht with ht | ht
              · have hidx : t.idx = s.idx := congrArg Interval.idx ht
                rw [hidx]
                exact ⟨s.lower, hsFixed⟩
              · exact hint t ht
            · intro c hc
              exact hrows c (List.mem_cons_of_mem _ hc)
          let lo := buildTree isInt rest (lowerBranch :: rows) hloIsInt
            hloBounds hloInfeasible
          have hhiBounds : BoundsPresent (upperBranch :: rows) (next :: rest) := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · constructor
              · rw [next_lowerRow]
                exact List.mem_cons_self
              · apply List.mem_cons_of_mem
                rw [next_upperRow s hwidth]
                exact hsBounds.2
            · obtain ⟨htLower, htUpper⟩ := hBounds t (by simp [ht])
              exact ⟨List.mem_cons_of_mem _ htLower, List.mem_cons_of_mem _ htUpper⟩
          have hhiIsInt : ∀ t ∈ next :: rest, isInt t.idx := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact hsInt
            · exact hIsInt t (by simp [ht])
          have hhiInfeasible : NoIntSolution (next :: rest) (upperBranch :: rows) := by
            intro a hint hrows
            apply hinfeasible a
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · exact hint next (by simp)
              · exact hint t (by simp [ht])
            · intro c hc
              exact hrows c (List.mem_cons_of_mem _ hc)
          let hi := buildTree isInt (next :: rest) (upperBranch :: rows)
            hhiIsInt hhiBounds hhiInfeasible
          exact ⟨.split s.idx s.lower lo.val hi.val,
            ⟨hsInt, lo.property.1, hi.property.1⟩,
            lo.property.2, hi.property.2⟩
termination_by intervalMeasure specs
decreasing_by
  all_goals simp [intervalMeasure]
  all_goals omega

/-- Explicit finite bounds make the branch-and-bound proof system complete. -/
theorem bounded_refTree_complete (isInt : Nat → Prop) (specs : List Interval)
    (rows : List Le)
    (hIsInt : ∀ s ∈ specs, isInt s.idx)
    (hBounds : BoundsPresent rows specs)
    (hinfeasible : NoIntSolution specs rows) :
    ∃ tree, RefTree.Valid isInt rows tree :=
  ⟨(buildTree isInt specs rows hIsInt hBounds hinfeasible).val,
    (buildTree isInt specs rows hIsInt hBounds hinfeasible).property.1⟩

/-- The bounded construction lies entirely in the split-and-Farkas fragment. -/
theorem bounded_refTree_complete_noDerive (isInt : Nat → Prop)
    (specs : List Interval) (rows : List Le)
    (hIsInt : ∀ s ∈ specs, isInt s.idx)
    (hBounds : BoundsPresent rows specs)
    (hinfeasible : NoIntSolution specs rows) :
    ∃ tree, RefTree.Valid isInt rows tree ∧ tree.NoDerive :=
  ⟨(buildTree isInt specs rows hIsInt hBounds hinfeasible).val,
    (buildTree isInt specs rows hIsInt hBounds hinfeasible).property⟩

end LeanVIPR.Completeness.BoundedCompleteness
