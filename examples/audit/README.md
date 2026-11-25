# Adversarial and edge-case certificates

Expected results with `viprcheck --native-mode full`:

| File | Expected | Why |
|---|---|---|
| `range_garbage.vipr` | parse error | `1e9` is not an exact number; it must not be read as an infinite bound |
| `range_inf_lower.vipr` | parse error | only `-inf` denotes an unbounded lower bound |
| `lone_minus.vipr` | parse error | a lone `-` is not the number 0 |
| `dup_index.vipr` | parse error | duplicate variable index in a row has no agreed meaning |
| `oob_index.vipr` | parse error | variable index beyond `VAR` count |
| `trailing.vipr` | parse error | tokens after the `DER` section |
| `spec_final_use_hint.vipr` | parse error | upstream `paper_eg3.vipr` with C8's final-use index changed from 13 to 11, so C10 (index 13) uses C8 after its hint. The derivations are all sound and the claim is true, but the spec requires the trailing field to be `-1` or an index no later user exceeds; `viprchk` rejects it as a trashed constraint |
| `comments.vipr` | accept | leading `%` comment lines are permitted by the spec |
| `comments_inline.vipr` | accept | a token starting with `%` begins a comment to the end of the line (end-of-line and interleaved comments, as in the reference examples); a `%` inside a token is ordinary |
| `dup_multiplier.vipr` | parse error | the spec requires distinct constraint indices in a `lin`/`rnd` reason |
| `range_neg.vipr` | accept (native and kernel mode) | negative integer range bound |
| `lin_eq.vipr` | accept | `lin` with all multipliers on equality rows derives an equality row (spec: suitable combination with every λ·s(C) = 0) |
| `viprchk_cont_rnd.vipr` | reject | rounds a continuous variable; the problem is feasible (`x = 1/2`), but upstream `viprchk` reports infeasibility verified |
| `viprchk_false_optimum.vipr` | reject | `min x` s.t. `x ≥ 1/2`, `x` continuous: true optimum 1/2; rounding `x ≥ 1/2` up to `x ≥ 1` lets upstream `viprchk` verify the false range `[1, 1]` |
| `viprchk_frac_coeff.vipr` | reject | rounds `x/2 ≤ 1/4` to `x/2 ≤ 0` with fractional coefficient on continuous `x`; feasible (`x = 1/2`), but upstream `viprchk` verifies infeasibility |

Found by differential testing (`benchmarks/difftest/`) against upstream `viprchk` and
`viprchk_parallel` at scipopt/vipr `master` (`99eec19`) and PR #25 (`b0e56a5`). Every file
below is a false claim; all are accepted by the listed upstream checker and rejected by LeanVIPR.

| File | Accepted by | Why the claim is false |
|---|---|---|
| `viprchk_max_sol_direction.vipr` | `viprchk`, `viprchk_parallel` | `max x`, `0 ≤ x ≤ 2`: optimum 2, claim `[0, 0]`. The `{ sol }` cutoff is `OBJ ≤ best` even for maximization |
| `viprchk_cutoff_false_lb.vipr` | `viprchk`, `viprchk_parallel` | `min x`, `x ≥ 5`, `x` integer: optimum 5, claim `[100, 100]`. The integral cutoff `OBJ ≤ best − 1` is used to derive `OBJ ≥ 100`; the lower bound is never compared with `best` |
| `viprchkpar_cutoff_absurd_lb.vipr` | `viprchk_parallel` | same problem; the cutoff yields an absurdity, which the parallel checker accepts as proof of any lower bound |
| `viprchkpar_unchecked_solution.vipr` | `viprchk_parallel` | `min x`, `x ≥ 0`, `x ≥ 2`: optimum 2, claim `[0, 0]` with the infeasible solution `x = 0`. Solution `i` is checked only against constraint `i` (`constraint[i]` for `constraint[j]`) |
| `viprchkpar_no_primal_solution.vipr` | `viprchk_parallel` | `min x`, `x ≥ 2`: claim `[0, 0]` with no solution listed for the upper bound |
| `viprchkpar_failed_lb_exit0.vipr` | `viprchk_parallel` | prints "Failed to derive lower bound." but exits 0 |
| `viprchkpar_failure_exit0.vipr` | `viprchk_parallel` | feasible `x ≥ 0` claimed infeasible with no contradiction; prints "Failed to verify infeasibility." but exits 0 (sequential `viprchk` rejects it by crashing with SIGSEGV) |
| `viprchkpar_uns_drops_assumption.vipr` | `viprchk_parallel` | `0 ≤ x ≤ 5`, `x` integer (feasible) claimed infeasible; `uns` keeps only the second-branch assumptions already present in the first, so the unjustified assumption `x ≥ 10` is dropped |
