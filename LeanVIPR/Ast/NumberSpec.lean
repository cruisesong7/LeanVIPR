module

public import LeanVIPR.Ast.Number
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# What a VIPR number token denotes

The parser reads numbers with an accumulator loop. This module says, independently,
*which rational a token denotes*, and proves the two agree in both directions.

The point of the exercise is that a misread number is the one parser fault the
soundness theorem cannot catch: a structurally damaged certificate usually fails to
replay, but a token read as the wrong value silently substitutes a different
mixed-integer problem, and `checkVipr_sound` would then establish a true claim about
the wrong problem. So the denotation below is written positionally — each digit
weighted by a power of ten, a fraction as `i + f / 10 ^ |f|` — rather than as the
left-to-right fold the implementation uses.

Sign handling mirrors the format rather than the implementation: a token carries at
most one leading sign, so `--5` denotes nothing.
-/

namespace LeanVIPR.Ast

/-- Every character is an ASCII digit. -/
def AllDigits (l : List Char) : Prop := ∀ c ∈ l, c.isDigit

instance (l : List Char) : Decidable (AllDigits l) := by
  unfold AllDigits; infer_instance

/-- The value of a digit list read most significant first, each digit weighted by its
positional power of ten. -/
def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - '0'.toNat) * 10 ^ cs.length + digitsValue cs

/-- `UDenotes cs q`: the unsigned token `cs` denotes exactly the rational `q`. -/
inductive UDenotes : List Char → ℚ → Prop
  /-- A nonempty run of digits denotes its base-ten value. -/
  | nat {ds : List Char} (hne : ds ≠ []) (hd : AllDigits ds) :
      UDenotes ds (digitsValue ds)
  /-- `i.f` denotes `i + f / 10 ^ |f|`; at least one side must be present. -/
  | dec {i f : List Char} (hne : i ≠ [] ∨ f ≠ []) (hi : AllDigits i) (hf : AllDigits f) :
      UDenotes (i ++ '.' :: f)
        ((digitsValue i : ℚ) + (digitsValue f : ℚ) / (10 : ℚ) ^ f.length)

/-- `Denotes cs q`: the token `cs`, with at most one leading sign, denotes `q`.

The sign convention is shared with the implementation via `splitSign`: that a token
carries at most one leading sign is part of the format, and `splitSign` is three
pattern-matching lines. Everything that computes a *value* — positional digit weights
and the fraction `f / 10 ^ |f|` — is stated independently above. -/
def Denotes (cs : List Char) (q : ℚ) : Prop :=
  ∃ u, UDenotes (splitSign cs).2 u ∧ q = (if (splitSign cs).1 then -u else u)

/-! ## Digit lists -/

private def step (acc : Option Nat) (c : Char) : Option Nat :=
  match acc with
  | some n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none
  | none => none

private theorem natOfDigits_unfold (l : List Char) :
    natOfDigits? l = if l.isEmpty then none else l.foldl step (some 0) := rfl

private theorem foldl_step_none (l : List Char) : l.foldl step none = none := by
  induction l with
  | nil => rfl
  | cons c cs ih => simpa [step] using ih

/-- On a digit list the accumulator loop computes the positional value. -/
private theorem foldl_step_some (l : List Char) (hd : AllDigits l) :
    ∀ a : Nat, l.foldl step (some a) = some (a * 10 ^ l.length + digitsValue l) := by
  induction l with
  | nil => intro a; simp [digitsValue]
  | cons c cs ih =>
      intro a
      have hc : c.isDigit := hd c (by simp)
      have hcs : AllDigits cs := fun x hx => hd x (by simp [hx])
      have hstep : step (some a) c = some (a * 10 + (c.toNat - '0'.toNat)) := by
        simp [step, hc]
      rw [List.foldl_cons, hstep, ih hcs]
      simp only [digitsValue, List.length_cons, pow_succ, Option.some.injEq]
      ring

private theorem foldl_step_eq_none (l : List Char) (hd : ¬ AllDigits l) :
    ∀ o : Option Nat, l.foldl step o = none := by
  induction l with
  | nil => exact absurd (fun _ h => absurd h (by simp)) hd
  | cons c cs ih =>
      intro o
      cases o with
      | none => simpa using foldl_step_none (c :: cs)
      | some a =>
          by_cases hc : c.isDigit
          · have hcs : ¬ AllDigits cs := by
              intro h
              exact hd fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hc
                · exact h x hx
            simpa [step, hc] using ih hcs _
          · simpa [step, hc] using foldl_step_none cs

/-- The digit reader is exactly the positional value on nonempty digit lists, and
fails on everything else. -/
theorem natOfDigits?_eq_some_iff {l : List Char} {n : Nat} :
    natOfDigits? l = some n ↔ l ≠ [] ∧ AllDigits l ∧ n = digitsValue l := by
  rw [natOfDigits_unfold]
  cases l with
  | nil => simp
  | cons c cs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
      by_cases hd : AllDigits (c :: cs)
      · rw [foldl_step_some _ hd 0]
        simp [hd, eq_comm]
      · rw [foldl_step_eq_none _ hd]
        simp [hd]

theorem natOfDigitsOrZero?_eq_some_iff {l : List Char} {n : Nat} :
    natOfDigitsOrZero? l = some n ↔ AllDigits l ∧ n = digitsValue l := by
  unfold natOfDigitsOrZero?
  cases l with
  | nil =>
      have hall : AllDigits ([] : List Char) := fun c hc => absurd hc (by simp)
      constructor
      · intro h
        simp only [List.isEmpty_nil, ite_true, Option.some.injEq] at h
        exact ⟨hall, by simp [digitsValue, ← h]⟩
      · intro h
        simp only [List.isEmpty_nil, ite_true, Option.some.injEq]
        simpa [digitsValue] using h.2.symm
  | cons c cs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
      rw [natOfDigits?_eq_some_iff]
      simp

/-! ## Splitting on a separator

`splitOnChar` is pinned down by two facts: rejoining its parts recovers the input, and
no part contains the separator. Together they characterize the one- and two-part cases,
which is all the number grammar needs. -/

/-- Rejoin parts with a single separator between consecutive parts. -/
def joinOn (sep : Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ sep :: joinOn sep ps

private theorem joinOn_nil_cons (sep : Char) (r : List Char) (rs : List (List Char)) :
    joinOn sep ([] :: r :: rs) = sep :: joinOn sep (r :: rs) := rfl

theorem splitOnChar_ne_nil (sep : Char) (cs : List Char) : splitOnChar sep cs ≠ [] := by
  induction cs with
  | nil => simp [splitOnChar]
  | cons c cs ih =>
      unfold splitOnChar
      by_cases h : c == sep
      · simp [h]
      · cases hsp : splitOnChar sep cs with
        | nil => exact absurd hsp ih
        | cons r rs => simp [h]

/-- Rejoining the parts recovers the input. -/
theorem joinOn_splitOnChar (sep : Char) (cs : List Char) :
    joinOn sep (splitOnChar sep cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      unfold splitOnChar
      by_cases h : c == sep
      · have hc : c = sep := by simpa using h
        cases hsp : splitOnChar sep cs with
        | nil => exact absurd hsp (splitOnChar_ne_nil sep cs)
        | cons r rs =>
            rw [hsp] at ih
            simp only [h, ite_true]
            rw [joinOn_nil_cons, ih, hc]
      · cases hsp : splitOnChar sep cs with
        | nil => exact absurd hsp (splitOnChar_ne_nil sep cs)
        | cons r rs =>
            rw [hsp] at ih
            cases rs with
            | nil => simpa [h, joinOn] using ih
            | cons r2 rs2 => simpa [h, joinOn] using ih

/-- No part produced by a split contains the separator. -/
theorem splitOnChar_parts (sep : Char) (cs : List Char) :
    ∀ p ∈ splitOnChar sep cs, sep ∉ p := by
  induction cs with
  | nil => simp [splitOnChar]
  | cons c cs ih =>
      unfold splitOnChar
      by_cases h : c == sep
      · intro p hp
        rcases List.mem_cons.mp (by simpa [h] using hp) with rfl | hp
        · simp
        · exact ih p hp
      · have hc : c ≠ sep := by simpa using h
        cases hsp : splitOnChar sep cs with
        | nil => exact absurd hsp (splitOnChar_ne_nil sep cs)
        | cons r rs =>
            rw [hsp] at ih
            intro p hp
            rcases List.mem_cons.mp (by simpa [h, hsp] using hp) with rfl | hp
            · intro hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact hc rfl
              · exact ih r (by simp) hmem
            · exact ih p (by simp [hp])

/-- A separator-free list splits into exactly itself. -/
theorem splitOnChar_of_not_mem {sep : Char} {cs : List Char} (h : sep ∉ cs) :
    splitOnChar sep cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc : c ≠ sep := fun hc => h (by simp [hc])
      have hcs : sep ∉ cs := fun hm => h (by simp [hm])
      simp [splitOnChar, beq_iff_eq, hc, ih hcs]

/-- Splitting at the first separator peels off the prefix before it. -/
theorem splitOnChar_append {sep : Char} {a b : List Char} (h : sep ∉ a) :
    splitOnChar sep (a ++ sep :: b) = a :: splitOnChar sep b := by
  induction a with
  | nil => simp [splitOnChar]
  | cons c a ih =>
      have hc : c ≠ sep := fun hc => h (by simp [hc])
      have ha : sep ∉ a := fun hm => h (by simp [hm])
      cases hsp : splitOnChar sep b with
      | nil => exact absurd hsp (splitOnChar_ne_nil sep b)
      | cons r rs => simp [splitOnChar, beq_iff_eq, hc, ih ha, hsp]

/-- The two shapes the number grammar needs. -/
theorem splitOnChar_eq_single_iff {sep : Char} {cs p : List Char} :
    splitOnChar sep cs = [p] ↔ sep ∉ cs ∧ p = cs := by
  constructor
  · intro h
    have hj := joinOn_splitOnChar sep cs
    rw [h] at hj
    have hp : p = cs := by simpa [joinOn] using hj
    have hno := splitOnChar_parts sep cs p (by rw [h]; simp)
    rw [hp] at hno
    exact ⟨hno, hp⟩
  · rintro ⟨hmem, rfl⟩
    exact splitOnChar_of_not_mem hmem

theorem splitOnChar_eq_pair_iff {sep : Char} {cs a b : List Char} :
    splitOnChar sep cs = [a, b] ↔ sep ∉ a ∧ sep ∉ b ∧ cs = a ++ sep :: b := by
  constructor
  · intro h
    have hj := joinOn_splitOnChar sep cs
    rw [h] at hj
    refine ⟨splitOnChar_parts sep cs a (by rw [h]; simp),
      splitOnChar_parts sep cs b (by rw [h]; simp), ?_⟩
    simpa [joinOn] using hj.symm
  · rintro ⟨ha, hb, rfl⟩
    rw [splitOnChar_append ha, splitOnChar_of_not_mem hb]

/-! ## Decimals -/

theorem not_mem_of_allDigits {l : List Char} {c : Char} (h : AllDigits l)
    (hc : ¬ c.isDigit) : c ∉ l := fun hm => hc (h c hm)

private theorem dot_not_digit : ¬ ('.' : Char).isDigit := by decide

private theorem isEmpty_and_eq_false {i f : List Char} (h : i ≠ [] ∨ f ≠ []) :
    (i.isEmpty && f.isEmpty) = false := by
  rcases h with h | h
  · cases i with
    | nil => exact absurd rfl h
    | cons _ _ => rfl
  · cases f with
    | nil => exact absurd rfl h
    | cons _ _ => simp

/-- A nonempty digit run reads as its positional value. -/
theorem parseUDec?_nat {ds : List Char} (hne : ds ≠ []) (hd : AllDigits ds) :
    parseUDec? ds = some (digitsValue ds) := by
  unfold parseUDec?
  rw [splitOnChar_of_not_mem (not_mem_of_allDigits hd dot_not_digit)]
  dsimp only
  rw [natOfDigits?_eq_some_iff.mpr ⟨hne, hd, rfl⟩]
  rfl

/-- `i.f` reads as `i + f / 10 ^ |f|`. -/
theorem parseUDec?_dec {i f : List Char} (hne : i ≠ [] ∨ f ≠ [])
    (hi : AllDigits i) (hf : AllDigits f) :
    parseUDec? (i ++ '.' :: f) =
      some ((digitsValue i : ℚ) + (digitsValue f : ℚ) / (10 : ℚ) ^ f.length) := by
  unfold parseUDec?
  rw [splitOnChar_append (not_mem_of_allDigits hi dot_not_digit),
    splitOnChar_of_not_mem (not_mem_of_allDigits hf dot_not_digit)]
  dsimp only
  rw [isEmpty_and_eq_false hne]
  simp only [Bool.false_eq_true, ite_false]
  rw [natOfDigitsOrZero?_eq_some_iff.mpr ⟨hi, rfl⟩,
    natOfDigitsOrZero?_eq_some_iff.mpr ⟨hf, rfl⟩]

/-- The unsigned decimal reader returns exactly the denoted rational. -/
theorem parseUDec?_eq_some_iff {cs : List Char} {q : ℚ} :
    parseUDec? cs = some q ↔ UDenotes cs q := by
  constructor
  · intro h
    unfold parseUDec? at h
    cases hsp : splitOnChar '.' cs with
    | nil => rw [hsp] at h; dsimp only at h; exact absurd h (by simp)
    | cons i rest =>
        cases rest with
        | nil =>
            obtain ⟨_, hic⟩ := splitOnChar_eq_single_iff.mp hsp
            rw [hsp] at h
            dsimp only at h
            cases hn : natOfDigits? i with
            | none => rw [hn] at h; exact absurd h (by simp)
            | some n =>
                rw [hn] at h
                obtain ⟨hne, hd, hnv⟩ := natOfDigits?_eq_some_iff.mp hn
                have hq : q = (digitsValue i : ℚ) := by
                  simp only [Option.some.injEq] at h
                  rw [← h, hnv]
                subst hic
                rw [hq]
                exact UDenotes.nat hne hd
        | cons f rest2 =>
            cases rest2 with
            | cons _ _ => rw [hsp] at h; dsimp only at h; exact absurd h (by simp)
            | nil =>
                obtain ⟨_, _, hcs⟩ := splitOnChar_eq_pair_iff.mp hsp
                rw [hsp] at h
                dsimp only at h
                cases hemp : (i.isEmpty && f.isEmpty) with
                | true => rw [hemp] at h; simp only [ite_true] at h; exact absurd h (by simp)
                | false =>
                    rw [hemp] at h
                    simp only [Bool.false_eq_true, ite_false] at h
                    cases hni : natOfDigitsOrZero? i with
                    | none => rw [hni] at h; exact absurd h (by simp)
                    | some ni =>
                        cases hnf : natOfDigitsOrZero? f with
                        | none => rw [hni, hnf] at h; exact absurd h (by simp)
                        | some nf =>
                            rw [hni, hnf] at h
                            obtain ⟨hdi, hiv⟩ := natOfDigitsOrZero?_eq_some_iff.mp hni
                            obtain ⟨hdf, hfv⟩ := natOfDigitsOrZero?_eq_some_iff.mp hnf
                            have hne : i ≠ [] ∨ f ≠ [] := by
                              by_cases hi0 : i = []
                              · right
                                intro hf0
                                rw [hi0, hf0] at hemp
                                exact absurd hemp (by simp)
                              · exact Or.inl hi0
                            subst hcs
                            simp only [Option.some.injEq] at h
                            rw [← h, hiv, hfv]
                            exact UDenotes.dec hne hdi hdf
  · intro h
    cases h with
    | nat hne hd => exact parseUDec?_nat hne hd
    | dec hne hi hf => exact parseUDec?_dec hne hi hf

/-- The signed decimal reader returns exactly the denoted rational. -/
theorem parseRatChars?_eq_some_iff {cs : List Char} {q : ℚ} :
    parseRatChars? cs = some q ↔ Denotes cs q := by
  unfold parseRatChars? Denotes
  cases hsp : parseUDec? (splitSign cs).2 with
  | none =>
      simp only [hsp]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨u, hu, -⟩
        exact absurd (parseUDec?_eq_some_iff.mpr hu) (by simp [hsp])
  | some u =>
      have hu : UDenotes (splitSign cs).2 u := parseUDec?_eq_some_iff.mp hsp
      simp only [hsp, Option.some.injEq]
      constructor
      · intro h; exact ⟨u, hu, h.symm⟩
      · rintro ⟨u', hu', rfl⟩
        have heq : u' = u := by
          have h2 := parseUDec?_eq_some_iff.mpr hu'
          rw [hsp] at h2
          simpa using h2.symm
        rw [heq]

theorem parseRat?_eq_some_iff {s : String} {q : ℚ} :
    parseRat? s = some q ↔ Denotes s.toList q := parseRatChars?_eq_some_iff

/-! ## Signed integers and `p/q` -/

/-- `IntDenotes cs z`: the token `cs` denotes exactly the integer `z`. -/
def IntDenotes (cs : List Char) (z : ℤ) : Prop :=
  (splitSign cs).2 ≠ [] ∧ AllDigits (splitSign cs).2 ∧
    z = (if (splitSign cs).1 then -(digitsValue (splitSign cs).2 : ℤ)
         else (digitsValue (splitSign cs).2 : ℤ))

theorem parseIntChars?_eq_some_iff {cs : List Char} {z : ℤ} :
    parseIntChars? cs = some z ↔ IntDenotes cs z := by
  unfold parseIntChars? IntDenotes
  cases hn : natOfDigits? (splitSign cs).2 with
  | none =>
      simp only [hn]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨hne, hd, -⟩
        exact absurd (natOfDigits?_eq_some_iff.mpr ⟨hne, hd, rfl⟩) (by simp [hn])
  | some n =>
      obtain ⟨hne, hd, hnv⟩ := natOfDigits?_eq_some_iff.mp hn
      simp only [hn, Option.some.injEq]
      constructor
      · intro h; exact ⟨hne, hd, by rw [← h, hnv]⟩
      · rintro ⟨-, -, rfl⟩; rw [hnv]

/-- `NumDenotes cs q`: the number token `cs` denotes exactly `q`: either a signed
decimal with no `/`, or a quotient of two signed integers with a nonzero denominator. -/
def NumDenotes (cs : List Char) (q : ℚ) : Prop :=
  ('/' ∉ cs ∧ Denotes cs q) ∨
  (∃ a b za zb, cs = a ++ '/' :: b ∧ '/' ∉ a ∧ '/' ∉ b ∧
    IntDenotes a za ∧ IntDenotes b zb ∧ zb ≠ 0 ∧ q = (za : ℚ) / (zb : ℚ))

/-- **The number reader returns exactly the denoted rational.** -/
theorem parseNumChars?_eq_some_iff {cs : List Char} {q : ℚ} :
    parseNumChars? cs = some q ↔ NumDenotes cs q := by
  constructor
  · intro h
    unfold parseNumChars? at h
    cases hsp : splitOnChar '/' cs with
    | nil => rw [hsp] at h; dsimp only at h; exact absurd h (by simp)
    | cons a rest =>
        cases rest with
        | nil =>
            obtain ⟨hmem, -⟩ := splitOnChar_eq_single_iff.mp hsp
            rw [hsp] at h
            dsimp only at h
            exact Or.inl ⟨hmem, parseRatChars?_eq_some_iff.mp h⟩
        | cons b rest2 =>
            cases rest2 with
            | cons _ _ => rw [hsp] at h; dsimp only at h; exact absurd h (by simp)
            | nil =>
                obtain ⟨ha, hb, hcs⟩ := splitOnChar_eq_pair_iff.mp hsp
                rw [hsp] at h
                dsimp only at h
                cases hpa : parseIntChars? a with
                | none => rw [hpa] at h; exact absurd h (by simp)
                | some za =>
                    cases hpb : parseIntChars? b with
                    | none => rw [hpa, hpb] at h; exact absurd h (by simp)
                    | some zb =>
                        rw [hpa, hpb] at h
                        dsimp only at h
                        cases hz : (zb == 0) with
                        | true => rw [hz] at h; simp only [ite_true] at h; exact absurd h (by simp)
                        | false =>
                            rw [hz] at h
                            simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
                            refine Or.inr ⟨a, b, za, zb, hcs, ha, hb,
                              parseIntChars?_eq_some_iff.mp hpa,
                              parseIntChars?_eq_some_iff.mp hpb, ?_, h.symm⟩
                            simpa using hz
  · intro h
    unfold parseNumChars?
    rcases h with ⟨hmem, hden⟩ | ⟨a, b, za, zb, rfl, ha, hb, hda, hdb, hzb, rfl⟩
    · rw [splitOnChar_of_not_mem hmem]
      dsimp only
      exact parseRatChars?_eq_some_iff.mpr hden
    · rw [splitOnChar_append ha, splitOnChar_of_not_mem hb]
      dsimp only
      rw [parseIntChars?_eq_some_iff.mpr hda, parseIntChars?_eq_some_iff.mpr hdb]
      dsimp only
      rw [show (zb == 0) = false by simpa using hzb]
      simp only [Bool.false_eq_true, ite_false]

theorem parseNum?_eq_some_iff {s : String} {q : ℚ} :
    parseNum? s = some q ↔ NumDenotes s.toList q := parseNumChars?_eq_some_iff

end LeanVIPR.Ast
