import LeanVIPRTactic

/-!
# `mip (cert := "…")`: proofs that build without SCIP

Every call here reads certificates that `mip?` or `mip_maximize?` saved next to this file
(`mip_cert_tests-*.vipr`), so the file checks with no solver installed:

```
lake env lean examples/mip_cert_tests.lean
```

To re-record a case, write `mip?` in place of `mip (cert := "…")` and run it once with a
certifying SCIP (`docs/TACTIC.md`); the suggestion is the call to paste back. A saved
certificate is still checked in the kernel against the problem the call builds, so a stale
file makes the proof fail, never succeed wrongly.
-/

-- 1. Pugh's example, which needs the omega test's dark shadow
theorem pugh (x y : ℤ) (h1 : 27 ≤ 11*x + 13*y) (h2 : 11*x + 13*y ≤ 45)
    (h3 : -10 ≤ 7*x - 9*y) (h4 : 7*x - 9*y ≤ 4) : False := by
  mip (cert := "mip_cert_tests-pugh-22-2.vipr")

-- 2. a case split: one certificate per case, in one file
theorem split (x : ℤ) (h : x = 1 ∨ x = 2) (h2 : 3 ≤ x) : False := by
  mip (cert := "mip_cert_tests-split-26-2.vipr")

-- 3. a goal `m.Infeasible`, for a `Mip` written by hand
def knapsack : LeanVIPR.Mip where
  vars := #[{ name := "x", isInt := true, lo := some 0, hi := some 3 },
            { name := "y", isInt := true, lo := some 0, hi := some 2 },
            { name := "z", isInt := true, lo := some 0, hi := some 1 }]
  objSense := .min
  obj := []
  rows := #[{ name := "c0", sense := 'E', rhs := 23, form := [⟨0, 6⟩, ⟨1, 10⟩, ⟨2, 15⟩] },
            { name := "c1", sense := 'G', rhs := 1, form := [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] }]

theorem knap : knapsack.Infeasible := by
  mip (cert := "mip_cert_tests-knap-39-2.vipr")

-- 4. a bound, from a range certificate
theorem maxRange (x y : ℤ) (h1 : x + y ≤ 4) (h2 : x - y ≤ 1) (h3 : 0 ≤ y) :
    2*x + y ≤ 6 := by
  mip_maximize (cert := "mip_cert_tests-maxRange-44-2.vipr") h : 2*x + y
  exact h

-- 5. a bound through the integer fallback: a range certificate, then an infeasibility one
theorem maxFallback (n : ℕ) (h : 2 * n ≤ 7) : n ≤ 3 := by
  mip_maximize (cert := "mip_cert_tests-maxFallback-49-2.vipr") n
  exact hbound

-- 6. an indicator: `lp`'s `maximize` bounds this profit by 30; the optimum is 19
theorem production (z : ℤ) (x : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 10) (off : z = 0 → x ≤ 0) (cap : x + 4 * (z : ℝ) ≤ 12) :
    3 * x - 5 * (z : ℝ) ≤ 19 := by
  mip_maximize (cert := "mip_cert_tests-production-56-2.vipr") 3 * x - 5 * (z : ℝ)
  exact hbound

-- 7. a saved certificate offered for another problem is rejected
/-- is not about this problem -/
#guard_msgs (substring := true) in
example (x y : ℤ) (h1 : 27 ≤ 11*x + 13*y) (h2 : 11*x + 13*y ≤ 45) : False := by
  mip (cert := "mip_cert_tests-pugh-22-2.vipr")

-- 8. so is a missing file
/-- cannot be read -/
#guard_msgs (substring := true) in
example (x : ℤ) (h : 2 * x = 1) : False := by
  mip (cert := "no-such-file.vipr")

-- 9. `#mip_scip` reports on a saved certificate
/-- pipeline_infeasible applies: true -/
#guard_msgs (substring := true) in
#mip_scip (cert := "mip_cert_tests-knap-39-2.vipr") knapsack

-- 10. a certificate too large for the kernel (1482 derivations, over five minutes) is
-- checked by compiled code under `+native`, in seconds. Proving its 50 rows back from the
-- hypotheses takes past the default heartbeats.
set_option maxHeartbeats 1000000 in
theorem pigeon (a b c d e : ℤ) (ha : 1 ≤ a) (ha' : a ≤ 4) (hb : 1 ≤ b) (hb' : b ≤ 4)
    (hc : 1 ≤ c) (hc' : c ≤ 4) (hd : 1 ≤ d) (hd' : d ≤ 4) (he : 1 ≤ e) (he' : e ≤ 4)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e) (h5 : b ≠ c) (h6 : b ≠ d)
    (h7 : b ≠ e) (h8 : c ≠ d) (h9 : c ≠ e) (h10 : d ≠ e) : False := by
  mip +native (cert := "mip_cert_tests-pigeon-84-2.vipr")

-- the proofs use the standard three axioms
/-- info: 'pugh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pugh
/-- info: 'production' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms production
-- except under `+native`, which adds one per check
/-- pigeon._native.decide.ax -/
#guard_msgs (substring := true) in #print axioms pigeon
