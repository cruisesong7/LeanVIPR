module

public import LeanVIPR.Thm.Checker.Complete

@[expose] public section

/-!
# The parallel checker agrees with the sequential one

`LeanVIPR.Checker.checkViprPar` runs each step's rule check against the finished pool, in
parallel, instead of against the growing pool, in order. `checkViprPar_eq` says the two
return the same `Bool`, so every theorem proved about `checkVipr` applies verbatim and
soundness is not restated for the parallel path.

Three facts carry the proof.

* Chunking loses nothing: `chunk` partitions the step list, so a conjunction evaluated per
  chunk is the conjunction over the whole (`parAll_eq`). `Task` does not appear in this
  argument at all, because `Task.spawn fn` is `{ get := fn () }` in Lean's logic -- the
  parallelism is an evaluation strategy the logic cannot see, which is exactly why no new
  axiom appears.
* Rows never change: `buildPool` only pushes, so an entry at an index already in the pool
  reads the same afterwards (`poolEntry_buildPool`).
* Hence a step whose references all point into the past cannot tell the two pools apart
  (`ruleCheckB_congr`), which is where `boundsOkB` earns its keep: it is what establishes
  that hypothesis, and it is the one half that must still run in order.
-/

namespace LeanVIPR.Checker

open LeanVIPR.Parser LeanVIPR.Semantics

/-! ## Chunking a conjunction -/

theorem chunk_flatten : ∀ (n : Nat) (xs : List SStep), (chunk n xs).flatten = xs
  | _, [] => by rw [chunk]; simp
  | n, s :: ss => by
      rw [chunk, List.flatten_cons, chunk_flatten n ((s :: ss).drop (max n 1)),
        List.take_append_drop]
  termination_by _ xs => xs.length
  decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Evaluating a conjunction one chunk per task gives the conjunction. -/
theorem parAll_eq (n : Nat) (p : SStep → Bool) (xs : List SStep) :
    parAll n p xs = xs.all p := by
  conv_rhs => rw [← chunk_flatten n xs]
  rw [List.all_flatten, parAll]
  match chunk n xs with
  | [] => simp
  | [c] => simp
  | c₁ :: c₂ :: cs =>
      show (List.map (fun c => Task.spawn (fun _ => c.all p)) (c₁ :: c₂ :: cs)).all Task.get
        = (c₁ :: c₂ :: cs).all (fun c => c.all p)
      rw [List.all_map]
      rfl

/-! ## The pool only grows -/

theorem size_buildPool : ∀ (v : Vipr) (pool : CheckerPool) (ss : List SStep),
    (buildPool v pool ss).size = pool.size + ss.length
  | _, _, [] => by rw [buildPool]; simp
  | v, pool, s :: ss => by
      rw [buildPool, size_buildPool v _ ss, Array.size_push, List.length_cons]
      omega

private theorem poolEntry_push {pool : CheckerPool} {e : CheckerEntry} {j : Nat}
    (h : j < pool.size) : poolEntry (pool.push e) j = poolEntry pool j := by
  have h' : j < (pool.push e).size := by rw [Array.size_push]; omega
  simp only [poolEntry, Array.getD, h, h', dif_pos]
  exact Array.getElem_push_lt h

theorem poolEntry_buildPool : ∀ (v : Vipr) (pool : CheckerPool) (ss : List SStep) (j : Nat),
    j < pool.size → poolEntry (buildPool v pool ss) j = poolEntry pool j
  | _, _, [], _, _ => by rw [buildPool]
  | v, pool, s :: ss, j, hj => by
      rw [buildPool,
        poolEntry_buildPool v _ ss j (by rw [Array.size_push]; omega),
        poolEntry_push hj]

theorem poolRow_buildPool {v : Vipr} {pool : CheckerPool} {ss : List SStep} {j : Nat}
    (hj : j < pool.size) : poolRow (buildPool v pool ss) j = poolRow pool j := by
  rw [poolRow, poolRow, poolEntry_buildPool v pool ss j hj]

/-! ## A step cannot tell the two pools apart

`referencesPastB` reads nothing of the pool but its size, so it is `refsBelowB` on that
size; and `ruleCheckB` reads nothing but rows. -/

theorem referencesPastB_eq_refsBelowB (pool : CheckerPool) (r : SReason) :
    referencesPastB pool r = refsBelowB pool.size r := by
  cases r <;> rfl

private theorem resolveRefs_congr {p q : CheckerPool} {comb : List (ℚ × Nat)}
    (hrow : ∀ j, j < p.size → poolRow p j = poolRow q j)
    (hb : comb.all (fun x => decide (x.2 < p.size)) = true) :
    resolveRefs p comb = resolveRefs q comb := by
  rw [resolveRefs, resolveRefs]
  refine List.map_congr_left ?_
  intro x hx
  have : x.2 < p.size := by
    have := List.all_eq_true.mp hb x hx
    simpa using this
  rw [hrow x.2 this]

/-- A step whose references all point below `p.size` gets the same answer from any pool
that agrees with `p` on those rows. -/
theorem ruleCheckB_congr {v : Vipr} {p q : CheckerPool} {s : SStep}
    (hrow : ∀ j, j < p.size → poolRow p j = poolRow q j)
    (hrefs : refsBelowB p.size s.reason = true) :
    ruleCheckB v p s = ruleCheckB v q s := by
  cases hr : s.reason with
  | asm => simp only [ruleCheckB, hr]
  | lin comb =>
      rw [hr] at hrefs
      simp only [ruleCheckB, hr]
      rw [resolveRefs_congr hrow (by simpa [refsBelowB] using hrefs)]
  | rnd comb =>
      rw [hr] at hrefs
      simp only [ruleCheckB, hr]
      rw [resolveRefs_congr hrow (by simpa [refsBelowB] using hrefs)]
  | uns i1 l1 i2 l2 =>
      rw [hr] at hrefs
      simp only [refsBelowB, Bool.and_eq_true, decide_eq_true_eq] at hrefs
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hrefs
      simp only [ruleCheckB, hr]
      rw [hrow i1 h1, hrow i2 h3, hrow l1 h2, hrow l2 h4]
  | sol => simp only [ruleCheckB, hr]

/-! ## Replay in order equals bounds in order plus rule checks anywhere -/

theorem replaySteps?_eq : ∀ (v : Vipr) (pool : CheckerPool) (ss : List SStep),
    replaySteps? v pool ss
      = if boundsOkB pool.size ss && ss.all (fun s => ruleCheckB v (buildPool v pool ss) s)
        then some (buildPool v pool ss) else none
  | _, _, [] => by rw [replaySteps?, buildPool, boundsOkB]; simp
  | v, pool, s :: ss => by
      have hrow : ∀ j, j < pool.size →
          poolRow pool j = poolRow (buildPool v (pool.push (entryOf pool s)) ss) j := by
        intro j hj
        simp only [poolRow]
        rw [poolEntry_buildPool v _ ss j (by rw [Array.size_push]; omega),
          poolEntry_push hj]
      rw [replaySteps?, replaySteps?_eq v (pool.push (entryOf pool s)) ss, stepValidB,
        referencesPastB_eq_refsBelowB, buildPool, boundsOkB, Array.size_push,
        List.all_cons]
      by_cases hb : refsBelowB pool.size s.reason = true
      · have hcongr : ruleCheckB v pool s
            = ruleCheckB v (buildPool v (pool.push (entryOf pool s)) ss) s :=
          ruleCheckB_congr hrow hb
        rw [hb, hcongr]
        by_cases hr : ruleCheckB v (buildPool v (pool.push (entryOf pool s)) ss) s = true
        · rw [hr]; simp
        · rw [Bool.eq_false_iff.mpr hr]; simp
      · rw [Bool.eq_false_iff.mpr hb]; simp

/-! ## The headline equality -/

/-- The parallel checker returns exactly what the sequential one returns, for any number
of tasks. Nothing about the verdict depends on how the work is divided. -/
theorem checkViprPar_eq (tasks : Nat) (v : Vipr) : checkViprPar tasks v = checkVipr v := by
  simp only [checkViprPar, checkVipr, replay?, replaySteps?_eq, parAll_eq]
  by_cases hsol : v.solSectionB = true
  · rw [hsol]
    by_cases hb : boundsOkB (initialPool v).size (Lower.viprSteps v) = true
    · by_cases hr : (Lower.viprSteps v).all
          (fun s => ruleCheckB v (buildPool v (initialPool v) (Lower.viprSteps v)) s) = true
      · rw [hb, hr]; simp
      · rw [hb, Bool.eq_false_iff.mpr hr]; simp
    · rw [Bool.eq_false_iff.mpr hb]; simp
  · rw [Bool.eq_false_iff.mpr hsol]; simp

/-- The same for the sliced-certificate checker. -/
theorem checkViprSlicePar_eq (tasks : Nat) (original sliced : Vipr) :
    checkViprSlicePar tasks original sliced = checkViprSlice original sliced := by
  rw [checkViprSlicePar, checkViprSlice, checkViprPar_eq]

end LeanVIPR.Checker
