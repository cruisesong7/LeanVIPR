module

public import LeanVIPR.Parser
public import LeanVIPR.Thm.Parser.Grammar

@[expose] public section

/-!
# The tokenizer implements the tokenization grammar

`isTokenization_iff` says the tokenizer produces the one tokenization the grammar of
`LeanVIPR.Thm.Parser.Grammar` allows, so `IsTokenization` can replace `wsTokens` in the
statement of the parser's correctness. That substitution is the point: a theorem phrased
in terms of `wsTokens` would take the tokenizer's own output as the definition of
tokenization and so could not detect a tokenizer that dropped, merged, or truncated
tokens.

`wsTokens_ne_empty` and `wsTokens_no_ws` survive as corollaries, but they are no longer
load-bearing: each is satisfied by tokenizers that are badly wrong, which is exactly why
invariants are not a specification.
-/

namespace LeanVIPR.Parser

/-! ## Comments -/

theorem dropComment_nil : ∀ {cs : List Char}, '\n' ∉ cs → dropComment cs = []
  | [], _ => by simp [dropComment]
  | c :: cs, h => by
      have hc : ¬ (c == '\n') = true := by
        simp only [beq_iff_eq]; exact fun he => h (by simp [he])
      have hcs : '\n' ∉ cs := fun hm => h (by simp [hm])
      simpa [dropComment, hc] using dropComment_nil hcs

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

/-- Either the comment has a terminating newline, or it runs to the end of the input. -/
theorem dropComment_cases : ∀ cs : List Char,
    (∃ body rest, cs = body ++ '\n' :: rest ∧ '\n' ∉ body ∧
      dropComment cs = '\n' :: rest) ∨ ('\n' ∉ cs ∧ dropComment cs = [])
  | [] => Or.inr ⟨by simp, by simp [dropComment]⟩
  | c :: cs => by
      by_cases h : c = '\n'
      · subst h
        exact Or.inl ⟨[], cs, by simp, by simp, by simp [dropComment]⟩
      · rcases dropComment_cases cs with ⟨body, rest, hcs, hn, hdc⟩ | ⟨hn, hdc⟩
        · refine Or.inl ⟨c :: body, rest, by rw [hcs]; simp, ?_,
            by simpa [dropComment, h] using hdc⟩
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm h, hn⟩
        · refine Or.inr ⟨?_, by simpa [dropComment, h] using hdc⟩
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm h, hn⟩

/-! ## One token -/

theorem takeToken_no_ws : ∀ (cs : List Char), NoWhitespace (takeToken cs).1
  | [], c, hc => by simp [takeToken] at hc
  | d :: ds, c, hc => by
      by_cases h : d.isWhitespace
      · simp [takeToken, h] at hc
      · simp only [takeToken, h, Bool.false_eq_true, ite_false] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · simpa using h
        · exact takeToken_no_ws ds c hc

theorem takeToken_split : ∀ cs : List Char, cs = (takeToken cs).1 ++ (takeToken cs).2
  | [] => by simp [takeToken]
  | c :: cs => by
      by_cases h : c.isWhitespace
      · simp [takeToken, h]
      · simp only [takeToken, h, Bool.false_eq_true, ite_false, List.cons_append]
        exact congrArg (c :: ·) (takeToken_split cs)

theorem takeToken_atEnd : ∀ cs : List Char, AtTokenEnd (takeToken cs).2
  | [] => by simp [takeToken, AtTokenEnd]
  | c :: cs => by
      by_cases h : c.isWhitespace
      · intro d hd
        simp only [takeToken, h, ite_true, List.head?_cons, Option.mem_def,
          Option.some.injEq] at hd
        exact hd ▸ h
      · simpa only [takeToken, h, Bool.false_eq_true, ite_false] using takeToken_atEnd cs

/-- A maximal run of non-whitespace characters is read back exactly. -/
theorem takeToken_append : ∀ {t rest : List Char}, NoWhitespace t → AtTokenEnd rest →
    takeToken (t ++ rest) = (t, rest)
  | [], rest, _, hend => by
      cases rest with
      | nil => rfl
      | cons c cs =>
          have hw : c.isWhitespace := hend c (by simp)
          simp [takeToken, hw]
  | c :: t, rest, hnw, hend => by
      have hc : ¬ c.isWhitespace := hnw c (by simp)
      have ih := takeToken_append (t := t) (fun d hd => hnw d (by simp [hd])) hend
      simp [takeToken, hc, ih]

/-- A comment at a token boundary contributes nothing. -/
theorem wsTokens_comment (body rest : List Char) (h : '\n' ∉ body) :
    wsTokens ('%' :: (body ++ '\n' :: rest)) = wsTokens ('\n' :: rest) := by
  rw [wsTokens]
  simp [dropComment_append h]

/-! ## The tokenizer agrees with the grammar -/

private theorem newline_ws : ('\n' : Char).isWhitespace := by decide
private theorem percent_not_ws : ¬ ('%' : Char).isWhitespace := by decide

private theorem wsTokens_aux : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    IsTokenization cs (wsTokens cs)
  | _, [], _ => by rw [wsTokens]; exact .nil
  | 0, c :: cs, h => absurd h (by simp)
  | n + 1, c :: cs, h => by
      have hlen : cs.length ≤ n := by simpa using h
      by_cases hw : c.isWhitespace
      · rw [wsTokens]
        simp only [hw, ite_true]
        exact .space hw (wsTokens_aux n cs hlen)
      · by_cases hp : c = '%'
        · subst hp
          rcases dropComment_cases cs with ⟨body, rest, hcs, hn, hdc⟩ | ⟨hn, hdc⟩
          · have hrest : rest.length ≤ n := by
              have : cs.length = body.length + 1 + rest.length := by
                rw [hcs]; simp; omega
              omega
            have hgoal : wsTokens ('%' :: cs) = wsTokens rest := by
              rw [wsTokens]
              simp only [percent_not_ws, Bool.false_eq_true, ite_false, beq_self_eq_true,
                ite_true, hdc]
              rw [wsTokens]
              simp [newline_ws]
            rw [hgoal, hcs]
            exact .commentLine hn (wsTokens_aux n rest hrest)
          · have hgoal : wsTokens ('%' :: cs) = [] := by
              rw [wsTokens]
              simp only [percent_not_ws, Bool.false_eq_true, ite_false, beq_self_eq_true,
                ite_true, hdc]
              rw [wsTokens]
            rw [hgoal]
            exact .commentEnd hn
        · have hrest : (takeToken cs).2.length ≤ n := by
            have hsp := congrArg List.length (takeToken_split cs)
            simp only [List.length_append] at hsp
            omega
          have hsplit : c :: cs = (c :: (takeToken cs).1) ++ (takeToken cs).2 := by
            simpa using congrArg (c :: ·) (takeToken_split cs)
          have hgoal : wsTokens (c :: cs)
              = String.ofList (c :: (takeToken cs).1) :: wsTokens (takeToken cs).2 := by
            rw [wsTokens]
            simp only [hw, Bool.false_eq_true, ite_false, show (c == '%') = false from by
              simpa using hp]
          rw [hgoal, hsplit]
          refine .token (by simp) ?_ (by simp [hp]) (takeToken_atEnd cs)
            (wsTokens_aux n (takeToken cs).2 hrest)
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hw
          · exact takeToken_no_ws cs d hd

/-- **The tokenizer produces a tokenization.** -/
theorem wsTokens_isTokenization (cs : List Char) : IsTokenization cs (wsTokens cs) :=
  wsTokens_aux cs.length cs le_rfl

/-- **Tokenization is unique**, so the grammar determines the token stream and the
tokenizer has no latitude. -/
theorem isTokenization_eq {cs : List Char} {ts : Toks} (h : IsTokenization cs ts) :
    ts = wsTokens cs := by
  induction h with
  | nil => rw [wsTokens]
  | @space c cs ts hw h ih =>
      rw [wsTokens]
      simp only [hw, ite_true]
      exact ih
  | @commentLine body rest ts hn h ih =>
      rw [wsTokens_comment body rest hn, wsTokens]
      simp only [newline_ws, ite_true]
      exact ih
  | @commentEnd body hn =>
      rw [wsTokens]
      simp only [percent_not_ws, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true,
        dropComment_nil hn]
      rw [wsTokens]
  | @token t rest ts hne hnw hpct hend h ih =>
      cases t with
      | nil => exact absurd rfl hne
      | cons c t' =>
          have hc : ¬ c.isWhitespace := hnw c (by simp)
          have hp : (c == '%') = false := by
            simpa using fun he : c = '%' => hpct (by simp [he])
          have hnw' : NoWhitespace t' := fun d hd => hnw d (by simp [hd])
          rw [List.cons_append, wsTokens]
          simp only [hc, Bool.false_eq_true, ite_false, hp,
            takeToken_append hnw' hend]
          exact congrArg (String.ofList (c :: t') :: ·) ih

theorem isTokenization_iff {cs : List Char} {ts : Toks} :
    IsTokenization cs ts ↔ ts = wsTokens cs :=
  ⟨isTokenization_eq, fun h => h ▸ wsTokens_isTokenization cs⟩

theorem isTokenization_unique {cs : List Char} {ts ts' : Toks}
    (h : IsTokenization cs ts) (h' : IsTokenization cs ts') : ts = ts' :=
  (isTokenization_eq h).trans (isTokenization_eq h').symm

/-! ## Corollaries

Properties of *tokenizations*, transferred to the tokenizer for free. Each was
previously proved by induction on `wsTokens`; with the characterization in hand they are
facts about the grammar, where they are visible as constructor fields. -/

/-- Every token is nonempty: the `hne` field of `IsTokenization.token`. -/
theorem IsTokenization.ne_empty {cs : List Char} {ts : Toks} (h : IsTokenization cs ts) :
    ∀ t ∈ ts, t ≠ "" := by
  induction h with
  | nil => simp
  | space _ _ ih => exact ih
  | commentLine _ _ ih => exact ih
  | commentEnd => simp
  | @token t rest ts hne hnw hpct hend h ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · intro he
        exact hne (by simpa using congrArg String.toList he)
      · exact ih s hs

/-- No token contains whitespace: the `hnw` field of `IsTokenization.token`. -/
theorem IsTokenization.no_ws {cs : List Char} {ts : Toks} (h : IsTokenization cs ts) :
    ∀ t ∈ ts, ∀ c ∈ t.toList, ¬ c.isWhitespace := by
  induction h with
  | nil => simp
  | space _ _ ih => exact ih
  | commentLine _ _ ih => exact ih
  | commentEnd => simp
  | @token t rest ts hne hnw hpct hend h ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · intro c hc
        exact hnw c (by simpa using hc)
      · exact ih s hs

theorem wsTokens_ne_empty (cs : List Char) : ∀ t ∈ wsTokens cs, t ≠ "" :=
  (wsTokens_isTokenization cs).ne_empty

theorem wsTokens_no_ws (cs : List Char) :
    ∀ t ∈ wsTokens cs, ∀ c ∈ t.toList, ¬ c.isWhitespace :=
  (wsTokens_isTokenization cs).no_ws

end LeanVIPR.Parser
