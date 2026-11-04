module

public import LeanVIPR.Thm.Number.Lemmas

@[expose] public section

/-!
# The number reader implements the number grammar

The reader of `LeanVIPR.Parser.Number` agrees with the grammar of
`LeanVIPR.Thm.Number.Grammar` in both directions:

* `parseNum_sound` — it never returns a value the grammar does not assign, so a token
  is never misread;
* `parseNum_complete` — it never rejects a well-formed token, so the checker's verdict
  is not an artefact of a narrow reader;
* `parseNum_eq_none_iff` — it rejects exactly the ill-formed tokens.

Together these make the reader irrelevant to review: `IsNumValue` says everything
about which token denotes which rational. `isNumValue_unique` records that the grammar
is unambiguous, so "the" value of a token is well defined.
-/

namespace LeanVIPR.Parser

/-! ## Naturals -/

theorem parseNat_eq_some_iff {l : List Char} {n : Nat} :
    natOfDigits? l = some n ↔ (IsDigits l ∧ n = digitsValue l) := by
  rw [natOfDigits?_eq_some_iff, IsDigits]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

theorem parseNat_eq_none_iff {l : List Char} :
    natOfDigits? l = none ↔ ¬ IsDigits l := by
  constructor
  · intro h hd
    have hs := parseNat_eq_some_iff.mpr (⟨hd, rfl⟩ : IsDigits l ∧ digitsValue l = digitsValue l)
    rw [h] at hs
    exact absurd hs (by simp)
  · intro h
    cases hn : natOfDigits? l with
    | none => rfl
    | some n => exact absurd (parseNat_eq_some_iff.mp hn).1 h

/-! ## Signed integers -/

/-- **Soundness.** A token the reader accepts is a well-formed `Integer` denoting
exactly the integer it returned. -/
theorem parseInt_sound {cs : List Char} {z : ℤ} (h : parseIntChars? cs = some z) :
    IsIntValue cs z :=
  intDenotes_iff_isIntValue.mp (parseIntChars?_eq_some_iff.mp h)

/-- **Completeness.** The reader accepts every well-formed `Integer`, returning the
integer the grammar assigns it. -/
theorem parseInt_complete {cs : List Char} {z : ℤ} (h : IsIntValue cs z) :
    parseIntChars? cs = some z :=
  parseIntChars?_eq_some_iff.mpr (intDenotes_iff_isIntValue.mpr h)

theorem parseInt_eq_some_iff {cs : List Char} {z : ℤ} :
    parseIntChars? cs = some z ↔ IsIntValue cs z :=
  ⟨parseInt_sound, parseInt_complete⟩

theorem isWfInt_iff_exists_value {cs : List Char} :
    IsWfInt cs ↔ ∃ z, IsIntValue cs z := by
  constructor
  · rintro ⟨sign, ds, hp⟩; exact ⟨intValue sign ds, sign, ds, hp, rfl⟩
  · rintro ⟨z, sign, ds, hp, -⟩; exact ⟨sign, ds, hp⟩

/-- The reader rejects exactly the tokens the grammar does not derive. -/
theorem parseInt_eq_none_iff {cs : List Char} :
    parseIntChars? cs = none ↔ ¬ IsWfInt cs := by
  constructor
  · intro h hwf
    obtain ⟨z, hz⟩ := isWfInt_iff_exists_value.mp hwf
    have hs := parseInt_complete hz
    rw [h] at hs
    exact absurd hs (by simp)
  · intro h
    cases hn : parseIntChars? cs with
    | none => rfl
    | some z => exact absurd (isWfInt_iff_exists_value.mpr ⟨z, parseInt_sound hn⟩) h

/-- The `Integer` grammar is unambiguous. -/
theorem isIntValue_unique {cs : List Char} {z z' : ℤ}
    (h : IsIntValue cs z) (h' : IsIntValue cs z') : z = z' := by
  have := parseInt_complete h
  rw [parseInt_complete h'] at this
  exact (Option.some.inj this).symm

/-! ## Numbers -/

/-- **Soundness.** A token the reader accepts is a well-formed `Number` denoting
exactly the rational it returned.

This is the direction soundness of the checker cannot replace. A structurally damaged
certificate usually fails to replay, but a token read as the wrong value silently
substitutes a different mixed-integer problem. -/
theorem parseNum_sound {cs : List Char} {q : ℚ} (h : parseNumChars? cs = some q) :
    IsNumValue cs q :=
  numDenotes_iff_isNumValue.mp (parseNumChars?_eq_some_iff.mp h)

/-- **Completeness.** The reader accepts every well-formed `Number`, returning the
rational the grammar assigns it. -/
theorem parseNum_complete {cs : List Char} {q : ℚ} (h : IsNumValue cs q) :
    parseNumChars? cs = some q :=
  parseNumChars?_eq_some_iff.mpr (numDenotes_iff_isNumValue.mpr h)

theorem parseNum_eq_some_iff {cs : List Char} {q : ℚ} :
    parseNumChars? cs = some q ↔ IsNumValue cs q :=
  ⟨parseNum_sound, parseNum_complete⟩

theorem isWfNum_iff_exists_value {cs : List Char} :
    IsWfNum cs ↔ ∃ q, IsNumValue cs q := by
  constructor
  · rintro (⟨sign, ds, hp⟩ | ⟨sign, i, f, hp⟩ | ⟨sn, nd, sd, dd, hp⟩)
    · exact ⟨(intValue sign ds : ℚ), Or.inl ⟨sign, ds, hp, rfl⟩⟩
    · exact ⟨decValue sign i f, Or.inr (Or.inl ⟨sign, i, f, hp, rfl⟩)⟩
    · exact ⟨quotValue sn nd sd dd, Or.inr (Or.inr ⟨sn, nd, sd, dd, hp, rfl⟩)⟩
  · rintro ⟨q, (⟨sign, ds, hp, -⟩ | ⟨sign, i, f, hp, -⟩ | ⟨sn, nd, sd, dd, hp, -⟩)⟩
    · exact Or.inl ⟨sign, ds, hp⟩
    · exact Or.inr (Or.inl ⟨sign, i, f, hp⟩)
    · exact Or.inr (Or.inr ⟨sn, nd, sd, dd, hp⟩)

/-- The reader rejects exactly the tokens the grammar does not derive. -/
theorem parseNum_eq_none_iff {cs : List Char} :
    parseNumChars? cs = none ↔ ¬ IsWfNum cs := by
  constructor
  · intro h hwf
    obtain ⟨q, hq⟩ := isWfNum_iff_exists_value.mp hwf
    have hs := parseNum_complete hq
    rw [h] at hs
    exact absurd hs (by simp)
  · intro h
    cases hn : parseNumChars? cs with
    | none => rfl
    | some q => exact absurd (isWfNum_iff_exists_value.mpr ⟨q, parseNum_sound hn⟩) h

/-- The `Number` grammar is unambiguous: a token denotes at most one rational, so the
three alternatives cannot disagree. -/
theorem isNumValue_unique {cs : List Char} {q q' : ℚ}
    (h : IsNumValue cs q) (h' : IsNumValue cs q') : q = q' := by
  have := parseNum_complete h
  rw [parseNum_complete h'] at this
  exact (Option.some.inj this).symm

/-! ## String-level corollaries

The certificate reader works on `String` tokens; these are the same statements for it. -/

theorem parseInt?_eq_some_iff {s : String} {z : ℤ} :
    parseInt? s = some z ↔ IsIntValue s.toList z := parseInt_eq_some_iff

theorem parseNum?_eq_some_iff' {s : String} {q : ℚ} :
    parseNum? s = some q ↔ IsNumValue s.toList q := parseNum_eq_some_iff

end LeanVIPR.Parser
