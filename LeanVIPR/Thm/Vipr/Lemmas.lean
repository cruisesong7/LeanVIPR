module

public import LeanVIPR.Ast.Vipr
public import LeanVIPR.Thm.Vipr.Grammar
public import LeanVIPR.Thm.Number

@[expose] public section

/-!
# Bridging lemmas for the certificate parser

Proof scaffolding only; the statements that matter are in `LeanVIPR.Thm.Vipr`, and the
grammar they are stated against is in `LeanVIPR.Thm.Vipr.Grammar`.
-/

namespace LeanVIPR.Ast

/-- The tokenizer's one-token step never captures whitespace. -/
theorem takeToken_no_ws : ∀ (cs : List Char), ∀ c ∈ (takeToken cs).1, ¬ c.isWhitespace
  | [], c, hc => by simp [takeToken] at hc
  | d :: ds, c, hc => by
      by_cases h : d.isWhitespace
      · simp [takeToken, h] at hc
      · simp only [takeToken, h, Bool.false_eq_true, ite_false] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · simpa using h
        · exact takeToken_no_ws ds c hc

/-- A comment body is dropped up to, but not including, its terminating newline. -/
theorem dropComment_append {body rest : List Char} (h : '\n' ∉ body) :
    dropComment (body ++ '\n' :: rest) = '\n' :: rest := by
  induction body with
  | nil => simp [dropComment]
  | cons d ds ih =>
      have hd : ¬ (d == '\n') = true := by
        simp only [beq_iff_eq]
        exact fun hdd => h (by simp [hdd])
      have hds : '\n' ∉ ds := fun hm => h (by simp [hm])
      simpa [dropComment, hd] using ih hds

end LeanVIPR.Ast
