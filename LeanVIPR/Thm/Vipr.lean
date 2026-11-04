module

public import LeanVIPR.Thm.Vipr.Lemmas

@[expose] public section

/-!
# The certificate parser implements the certificate grammar

Two groups of results.

**Tokenizer.** What every later stage may assume about the token stream: tokens are
nonempty, no token contains whitespace, and a comment at a token boundary contributes
nothing.

**Terminals.** For each terminal, an `iff` saying the consumer reads exactly the tokens
the grammar derives, returns exactly the value the grammar assigns, and leaves exactly
the rest of the stream. Each pairs with a `_nil` lemma: an exhausted stream is always an
error, never a silent success. Since each `iff` is stated against
`LeanVIPR.Thm.Vipr.Grammar` and never against another parser function, the consumers
need not be read.
-/

namespace LeanVIPR.Ast

/-! ## Tokenizer -/

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
  rw [wsTokens]
  simp [dropComment_append h]

/-! ## Terminals -/

theorem takeTok_nil : ∃ e, takeTok [] = .error e := ⟨_, rfl⟩

theorem takeTok_cons {t u : String} {ts ts' : Toks} :
    takeTok (t :: ts) = .ok (u, ts') ↔ (u = t ∧ ts' = ts) := by
  simp [takeTok, eq_comm]

theorem expectTok_nil {s : String} : ∃ e, expectTok s [] = .error e := ⟨_, rfl⟩

theorem expectTok_cons {s t : String} {ts ts' : Toks} :
    expectTok s (t :: ts) = .ok ts' ↔ (t = s ∧ ts' = ts) := by
  by_cases h : t = s
  · subst h; simp [expectTok, eq_comm]
  · simp [expectTok, h]

theorem takeNat_nil : ∃ e, takeNat [] = .error e := ⟨_, rfl⟩

/-- The natural-number consumer reads exactly a `Nat` terminal. -/
theorem takeNat_cons {t : String} {ts ts' : Toks} {n : Nat} :
    takeNat (t :: ts) = .ok (n, ts') ↔ (IsNatTok t n ∧ ts' = ts) := by
  have key : takeNat (t :: ts) = .ok (n, ts') ↔
      (natOfDigits? t.toList = some n ∧ ts' = ts) := by
    simp only [takeNat, takeTok, bind, Except.bind]
    cases hu : natOfDigits? t.toList with
    | none => simp
    | some m => simp [eq_comm]
  rw [key, parseNat_eq_some_iff, IsNatTok]

theorem takeInt_nil : ∃ e, takeInt [] = .error e := ⟨_, rfl⟩

/-- The integer consumer reads exactly an `Int` terminal. -/
theorem takeInt_cons {t : String} {ts ts' : Toks} {z : ℤ} :
    takeInt (t :: ts) = .ok (z, ts') ↔ (IsIntTok t z ∧ ts' = ts) := by
  have key : takeInt (t :: ts) = .ok (z, ts') ↔
      (parseIntChars? t.toList = some z ∧ ts' = ts) := by
    simp only [takeInt, takeTok, bind, Except.bind,
      show parseInt? t = parseIntChars? t.toList from rfl]
    cases hu : parseIntChars? t.toList with
    | none => simp
    | some w => simp [eq_comm]
  rw [key, parseInt_eq_some_iff, IsIntTok]

theorem takeNum_nil : ∃ e, takeNum [] = .error e := ⟨_, rfl⟩

/-- The rational consumer reads exactly a `Num` terminal. -/
theorem takeNum_cons {t : String} {ts ts' : Toks} {q : ℚ} :
    takeNum (t :: ts) = .ok (q, ts') ↔ (IsNumTok t q ∧ ts' = ts) := by
  have key : takeNum (t :: ts) = .ok (q, ts') ↔
      (parseNumChars? t.toList = some q ∧ ts' = ts) := by
    simp only [takeNum, takeTok, bind, Except.bind,
      show parseNum? t = parseNumChars? t.toList from rfl]
    cases hu : parseNumChars? t.toList with
    | none => simp
    | some r => simp [eq_comm]
  rw [key, parseNum_eq_some_iff, IsNumTok]

theorem takeSense_nil : ∃ e, takeSense [] = .error e := ⟨_, rfl⟩

private theorem sense_good {t : String} {ts ts' : Toks} {c d : Char}
    (hl : t.toList = [d]) (hd : d = 'E' ∨ d = 'L' ∨ d = 'G') :
    ((Except.ok (d, ts) : Except String (Char × Toks)) = .ok (c, ts'))
      ↔ (IsSenseTok t c ∧ ts' = ts) := by
  unfold IsSenseTok
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ : d = c ∧ ts = ts' := by simpa using h
    exact ⟨⟨hl, hd⟩, rfl⟩
  · rintro ⟨⟨htl, -⟩, rfl⟩
    rw [hl] at htl
    obtain rfl : d = c := by simpa using htl
    rfl

/-- The sense consumer reads exactly a `Sense` terminal. -/
theorem takeSense_cons {t : String} {ts ts' : Toks} {c : Char} :
    takeSense (t :: ts) = .ok (c, ts') ↔ (IsSenseTok t c ∧ ts' = ts) := by
  have hcons : takeSense (t :: ts) =
      (match t.toList with
       | ['E'] => .ok ('E', ts)
       | ['L'] => .ok ('L', ts)
       | ['G'] => .ok ('G', ts)
       | _ => .error s!"expected sense E/L/G, got '{t}'") := rfl
  rw [hcons]
  rcases hl : t.toList with _ | ⟨d, rest⟩
  · simp [IsSenseTok, hl]
  · rcases rest with _ | ⟨e, rest2⟩
    · by_cases h1 : d = 'E'
      · subst h1; exact sense_good hl (Or.inl rfl)
      · by_cases h2 : d = 'L'
        · subst h2; exact sense_good hl (Or.inr (Or.inl rfl))
        · by_cases h3 : d = 'G'
          · subst h3; exact sense_good hl (Or.inr (Or.inr rfl))
          · constructor
            · intro hh
              exact absurd hh (by simp [h1, h2, h3])
            · rintro ⟨⟨hwl, hc⟩, -⟩
              rw [hl] at hwl
              obtain rfl : d = c := by simpa using hwl
              rcases hc with rfl | rfl | rfl
              · exact absurd rfl h1
              · exact absurd rfl h2
              · exact absurd rfl h3
    · simp [IsSenseTok, hl]

/-- The bound consumer reads exactly a `Bound` terminal. It consumes no stream, so it
has no `_nil` case. -/
theorem takeBound_eq_ok_iff {infinity t : String} {b : Option ℚ} :
    takeBound infinity t = .ok b ↔ IsBoundTok infinity t b := by
  unfold takeBound IsBoundTok
  by_cases h : t = infinity
  · subst h
    constructor
    · intro hh
      exact Or.inl ⟨rfl, by simpa using hh.symm⟩
    · rintro (⟨-, rfl⟩ | ⟨hne, -⟩)
      · simp
      · exact absurd rfl hne
  · have hbeq : (t == infinity) = false := by simpa using h
    simp only [hbeq, Bool.false_eq_true, ite_false,
      show parseNum? t = parseNumChars? t.toList from rfl]
    cases hq : parseNumChars? t.toList with
    | none =>
        constructor
        · intro hh; exact absurd hh (by simp)
        · rintro (⟨hE, -⟩ | ⟨-, r, hd, -⟩)
          · exact absurd hE h
          · rw [parseNum_complete hd] at hq
            exact absurd hq (by simp)
    | some r =>
        constructor
        · intro hh
          exact Or.inr ⟨h, r, parseNum_sound hq, by simpa using hh.symm⟩
        · rintro (⟨hE, -⟩ | ⟨-, r', hd, rfl⟩)
          · exact absurd hE h
          · rw [parseNum_complete hd] at hq
            simp [Option.some.inj hq]

end LeanVIPR.Ast
