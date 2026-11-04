module

public import LeanVIPR.Ast.Vipr
public import LeanVIPR.Ast.ViprDenote
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

/-! ## Token-level consumers

Each lemma is an `iff`, so the consumer reads exactly what the grammar says and rejects
exactly what it does not. Together with `LeanVIPR.Ast.NumberSound` these connect the
token stream to exact rational values with no appeal to the implementation. -/

theorem takeTok_eq_ok_iff {ts ts' : Toks} {t : String} :
    takeTok ts = .ok (t, ts') ↔ ReadsTok ts t ts' := by
  cases ts with
  | nil => simp [takeTok, ReadsTok]
  | cons u us => simp [takeTok, ReadsTok]

theorem expectTok_eq_ok_iff {s : String} {ts ts' : Toks} :
    expectTok s ts = .ok ts' ↔ ReadsLit s ts ts' := by
  cases ts with
  | nil => simp [expectTok, ReadsLit]
  | cons u us =>
      by_cases h : u = s
      · subst h; simp [expectTok, ReadsLit, eq_comm]
      · simp [expectTok, ReadsLit, h]

theorem takeNat_eq_ok_iff {ts ts' : Toks} {n : Nat} :
    takeNat ts = .ok (n, ts') ↔ ReadsNat ts n ts' := by
  cases ts with
  | nil => simp [takeNat, takeTok, ReadsNat, bind, Except.bind]
  | cons u us =>
      have key : takeNat (u :: us) = .ok (n, ts') ↔
          (natOfDigits? u.toList = some n ∧ us = ts') := by
        simp only [takeNat, takeTok, bind, Except.bind]
        cases hu : natOfDigits? u.toList with
        | none => simp
        | some m => simp [eq_comm]
      rw [key]
      constructor
      · rintro ⟨hd, rfl⟩
        obtain ⟨hne, hdig, hv⟩ := natOfDigits?_eq_some_iff.mp hd
        exact ⟨u, rfl, hne, hdig, hv⟩
      · rintro ⟨t, ht, hne, hdig, hv⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj ht
        exact ⟨natOfDigits?_eq_some_iff.mpr ⟨hne, hdig, hv⟩, rfl⟩

theorem takeInt_eq_ok_iff {ts ts' : Toks} {z : ℤ} :
    takeInt ts = .ok (z, ts') ↔ ReadsInt ts z ts' := by
  cases ts with
  | nil => simp [takeInt, takeTok, ReadsInt, bind, Except.bind]
  | cons u us =>
      have key : takeInt (u :: us) = .ok (z, ts') ↔
          (parseIntChars? u.toList = some z ∧ us = ts') := by
        simp only [takeInt, takeTok, bind, Except.bind,
          show parseInt? u = parseIntChars? u.toList from rfl]
        cases hu : parseIntChars? u.toList with
        | none => simp
        | some w => simp [eq_comm]
      rw [key]
      constructor
      · rintro ⟨hd, rfl⟩
        exact ⟨u, rfl, parseIntChars?_eq_some_iff.mp hd⟩
      · rintro ⟨t, ht, hd⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj ht
        exact ⟨parseIntChars?_eq_some_iff.mpr hd, rfl⟩

theorem takeNum_eq_ok_iff {ts ts' : Toks} {q : ℚ} :
    takeNum ts = .ok (q, ts') ↔ ReadsNum ts q ts' := by
  cases ts with
  | nil => simp [takeNum, takeTok, ReadsNum, bind, Except.bind]
  | cons u us =>
      have key : takeNum (u :: us) = .ok (q, ts') ↔
          (parseNumChars? u.toList = some q ∧ us = ts') := by
        simp only [takeNum, takeTok, bind, Except.bind,
          show parseNum? u = parseNumChars? u.toList from rfl]
        cases hu : parseNumChars? u.toList with
        | none => simp
        | some r => simp [eq_comm]
      rw [key]
      constructor
      · rintro ⟨hd, rfl⟩
        exact ⟨u, rfl, parseNumChars?_eq_some_iff.mp hd⟩
      · rintro ⟨t, ht, hd⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj ht
        exact ⟨parseNumChars?_eq_some_iff.mpr hd, rfl⟩

private theorem sense_good {u : String} {us ts' : Toks} {c d : Char}
    (hl : u.toList = [d]) (hd : d = 'E' ∨ d = 'L' ∨ d = 'G') :
    ((Except.ok (d, us) : Except String (Char × Toks)) = .ok (c, ts'))
      ↔ ReadsSense (u :: us) c ts' := by
  unfold ReadsSense
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ : d = c ∧ us = ts' := by simpa using h
    exact ⟨u, rfl, hl, hd⟩
  · rintro ⟨t, ht, htl, -⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj ht
    rw [hl] at htl
    obtain rfl : d = c := by simpa using htl
    rfl

theorem takeSense_eq_ok_iff {ts ts' : Toks} {c : Char} :
    takeSense ts = .ok (c, ts') ↔ ReadsSense ts c ts' := by
  cases ts with
  | nil => simp [takeSense, takeTok, ReadsSense, bind, Except.bind]
  | cons u us =>
      have hcons : takeSense (u :: us) =
          (match u.toList with
           | ['E'] => .ok ('E', us)
           | ['L'] => .ok ('L', us)
           | ['G'] => .ok ('G', us)
           | _ => .error s!"expected sense E/L/G, got '{u}'") := rfl
      rw [hcons]
      rcases hl : u.toList with _ | ⟨d, rest⟩
      · simp [ReadsSense, hl]
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
                · rintro ⟨w, hw, hwl, hc⟩
                  obtain ⟨rfl, rfl⟩ := List.cons.inj hw
                  rw [hl] at hwl
                  obtain rfl : d = c := by simpa using hwl
                  rcases hc with rfl | rfl | rfl
                  · exact absurd rfl h1
                  · exact absurd rfl h2
                  · exact absurd rfl h3
        · simp [ReadsSense, hl]

theorem takeBound_eq_ok_iff {infinity t : String} {b : Option ℚ} :
    takeBound infinity t = .ok b ↔ ReadsBound infinity t b := by
  unfold takeBound ReadsBound
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
          · rw [parseNumChars?_eq_some_iff.mpr hd] at hq
            exact absurd hq (by simp)
    | some r =>
        constructor
        · intro hh
          exact Or.inr ⟨h, r, parseNumChars?_eq_some_iff.mp hq, by simpa using hh.symm⟩
        · rintro (⟨hE, -⟩ | ⟨-, r', hd, rfl⟩)
          · exact absurd hE h
          · rw [parseNumChars?_eq_some_iff.mpr hd] at hq
            simp [Option.some.inj hq]

end LeanVIPR.Ast
