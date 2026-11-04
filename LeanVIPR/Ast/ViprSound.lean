module

public import LeanVIPR.Ast.Vipr
public import LeanVIPR.Ast.NumberSound

@[expose] public section

/-!
# Properties of the certificate reader

What the tokenizer guarantees to every later stage: tokens are nonempty and contain no
whitespace, and a comment at a token boundary contributes nothing. The parser's grammar
correspondence will be stated here too.
-/

namespace LeanVIPR.Ast

/-! ## Tokenizer -/

theorem takeToken_no_ws : ∀ (cs : List Char), ∀ c ∈ (takeToken cs).1, ¬ c.isWhitespace
  | [], c, hc => by simp [takeToken] at hc
  | d :: ds, c, hc => by
      by_cases h : d.isWhitespace
      · simp [takeToken, h] at hc
      · simp only [takeToken, h, Bool.false_eq_true, ite_false] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · simpa using h
        · exact takeToken_no_ws ds c hc

/-- Every token is nonempty. -/
theorem wsTokens_ne_empty (cs : List Char) : ∀ t ∈ wsTokens cs, t ≠ "" := by
  induction cs using wsTokens.induct with
  | case1 => simp [wsTokens]
  | case2 c cs hws ih => rw [wsTokens]; simpa [hws] using ih
  | case3 c cs hws hpct ih =>
      rw [wsTokens]
      simpa [hws, hpct] using ih
  | case4 c cs hws hpct t r hr ih =>
      rw [wsTokens]
      simp only [hws, hpct, Bool.false_eq_true, ite_false, hr]
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · intro hempty
        exact absurd (congrArg String.length hempty) (by simp)
      · exact ih s hs

/-- No token contains whitespace. -/
theorem wsTokens_no_ws (cs : List Char) :
    ∀ t ∈ wsTokens cs, ∀ c ∈ t.toList, ¬ c.isWhitespace := by
  induction cs using wsTokens.induct with
  | case1 => simp [wsTokens]
  | case2 c cs hws ih => rw [wsTokens]; simpa [hws] using ih
  | case3 c cs hws hpct ih => rw [wsTokens]; simpa [hws, hpct] using ih
  | case4 c cs hws hpct t r hr ih =>
      rw [wsTokens]
      simp only [hws, hpct, Bool.false_eq_true, ite_false, hr]
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · intro d hd
        simp only [String.toList_ofList] at hd
        rcases List.mem_cons.mp hd with rfl | hd
        · simpa using hws
        · have := takeToken_no_ws cs d (by rw [hr] at *; exact hd)
          simpa using this
      · exact ih s hs

/-- A comment at a token boundary contributes nothing. -/
theorem wsTokens_comment (body rest : List Char) (h : '\n' ∉ body) :
    wsTokens ('%' :: (body ++ '\n' :: rest)) = wsTokens ('\n' :: rest) := by
  have hdrop : dropComment (body ++ '\n' :: rest) = '\n' :: rest := by
    induction body with
    | nil => simp [dropComment]
    | cons d ds ih =>
        have hd : ¬ (d == '\n') = true := by
          simp only [beq_iff_eq]
          exact fun hdd => h (by simp [hdd])
        have hds : '\n' ∉ ds := fun hm => h (by simp [hm])
        simpa [dropComment, hd] using ih hds
  rw [wsTokens]
  simp [hdrop]

end LeanVIPR.Ast
