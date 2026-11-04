module

public import LeanVIPR.Parser
public import LeanVIPR.Thm.Parser.Tokens
public import LeanVIPR.Thm.Parser.Grammar
public import LeanVIPR.Thm.Parser.Number

@[expose] public section

/-!
# Bridging lemmas for the certificate parser

Proof scaffolding only; the statements that matter are in `LeanVIPR.Thm.Parser.Certificate`, and the
grammar they are stated against is in `LeanVIPR.Thm.Parser.Grammar`.

Every consumer gets the same pair of lemmas, and nothing else is needed of it:

* `_complete` — if a segment renders `x`, the consumer reads it off the front of any
  stream beginning with that segment and leaves the rest untouched;
* `_sound` — if the consumer succeeds, what it consumed was a segment rendering what it
  returned.

Stated this way the two directions compose along the format: the suffix in `_complete`
is what lets one row's lemma be applied inside the next.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Semantics

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

/-! ## Inverting the `Except` monad -/

/-- Inversion for one `do`-step: a successful bind means the first action succeeded and
the continuation succeeded on its result. -/
theorem bind_eq_ok {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Terminals, as prefix consumers -/

theorem takeTok_prefix {t : String} {suf : Toks} : takeTok (t :: suf) = .ok (t, suf) := rfl

theorem expectTok_prefix {s : String} {suf : Toks} : expectTok s (s :: suf) = .ok suf :=
  expectTok_cons.mpr ⟨rfl, rfl⟩

theorem takeNat_prefix {t : String} {n : Nat} {suf : Toks} (h : IsNatTok t n) :
    takeNat (t :: suf) = .ok (n, suf) := takeNat_cons.mpr ⟨h, rfl⟩

theorem takeInt_prefix {t : String} {z : Int} {suf : Toks} (h : IsIntTok t z) :
    takeInt (t :: suf) = .ok (z, suf) := takeInt_cons.mpr ⟨h, rfl⟩

theorem takeNum_prefix {t : String} {q : ℚ} {suf : Toks} (h : IsNumTok t q) :
    takeNum (t :: suf) = .ok (q, suf) := takeNum_cons.mpr ⟨h, rfl⟩

theorem takeSense_prefix {t : String} {c : Char} {suf : Toks} (h : IsSenseTok t c) :
    takeSense (t :: suf) = .ok (c, suf) := takeSense_cons.mpr ⟨h, rfl⟩

theorem takeTok_sound {ts ts' : Toks} {t : String} (h : takeTok ts = .ok (t, ts')) :
    ts = t :: ts' := by
  cases ts with
  | nil => exact absurd h (by simp [takeTok])
  | cons u us => obtain ⟨rfl, rfl⟩ := takeTok_cons.mp h; rfl

theorem expectTok_sound {s : String} {ts ts' : Toks} (h : expectTok s ts = .ok ts') :
    ts = s :: ts' := by
  cases ts with
  | nil => exact absurd h (by simp [expectTok])
  | cons u us => obtain ⟨rfl, rfl⟩ := expectTok_cons.mp h; rfl

theorem takeNat_sound {ts ts' : Toks} {n : Nat} (h : takeNat ts = .ok (n, ts')) :
    ∃ t, ts = t :: ts' ∧ IsNatTok t n := by
  cases ts with
  | nil => exact absurd h (by simp [takeNat, takeTok, bind, Except.bind])
  | cons u us => obtain ⟨h1, rfl⟩ := takeNat_cons.mp h; exact ⟨u, rfl, h1⟩

theorem takeInt_sound {ts ts' : Toks} {z : Int} (h : takeInt ts = .ok (z, ts')) :
    ∃ t, ts = t :: ts' ∧ IsIntTok t z := by
  cases ts with
  | nil => exact absurd h (by simp [takeInt, takeTok, bind, Except.bind])
  | cons u us => obtain ⟨h1, rfl⟩ := takeInt_cons.mp h; exact ⟨u, rfl, h1⟩

theorem takeNum_sound {ts ts' : Toks} {q : ℚ} (h : takeNum ts = .ok (q, ts')) :
    ∃ t, ts = t :: ts' ∧ IsNumTok t q := by
  cases ts with
  | nil => exact absurd h (by simp [takeNum, takeTok, bind, Except.bind])
  | cons u us => obtain ⟨h1, rfl⟩ := takeNum_cons.mp h; exact ⟨u, rfl, h1⟩

theorem takeSense_sound {ts ts' : Toks} {c : Char} (h : takeSense ts = .ok (c, ts')) :
    ∃ t, ts = t :: ts' ∧ IsSenseTok t c := by
  cases ts with
  | nil => exact absurd h (by simp [takeSense, takeTok, bind, Except.bind])
  | cons u us => obtain ⟨h1, rfl⟩ := takeSense_cons.mp h; exact ⟨u, rfl, h1⟩

/-- A digit token is never one of the format's keywords, so no production that begins
with a count can be confused with one that begins with a keyword. -/
theorem natTok_ne {t s : String} {n : Nat} (h : IsNatTok t n)
    (hs : ¬ AllDigits s.toList) : t ≠ s := fun he => hs (he ▸ h.1.2)

theorem not_allDigits_OBJ : ¬ AllDigits "OBJ".toList := by decide
theorem not_allDigits_weak : ¬ AllDigits "weak".toList := by decide

/-! ## Repetition

Each counted list gets the same pair. Note that `_complete` is applied at the list's own
length, not at an independently supplied count: the count token is checked against
`List.length` by the production that writes it, so these lemmas never need to know what
the file claimed. -/

theorem takePairs_complete {seg suf : Toks} {prs : List (Nat × ℚ)}
    (h : IsSeq IsPair seg prs) : takePairs prs.length (seg ++ suf) = .ok (prs, suf) := by
  induction h with
  | nil => simp [takePairs]
  | @cons s rest p ps hp hs ih =>
      obtain ⟨it, vt, rfl, hi, hv⟩ := hp
      have he : ([it, vt] ++ rest) ++ suf = it :: vt :: (rest ++ suf) := by simp
      have h1 : takeNat (it :: vt :: (rest ++ suf)) = .ok (p.1, vt :: (rest ++ suf)) :=
        takeNat_prefix hi
      have h2 : takeNum (vt :: (rest ++ suf)) = .ok (p.2, rest ++ suf) := takeNum_prefix hv
      rw [he, List.length_cons, takePairs]
      simp only [bind, Except.bind, h1, h2, ih]

theorem takePairs_sound : ∀ {n : Nat} {ts ts' : Toks} {prs : List (Nat × ℚ)},
    takePairs n ts = .ok (prs, ts') →
      prs.length = n ∧ ∃ seg, ts = seg ++ ts' ∧ IsSeq IsPair seg prs
  | 0, ts, ts', prs, h => by
      obtain ⟨rfl, rfl⟩ : prs = [] ∧ ts = ts' := by
        simpa [takePairs, eq_comm] using h
      exact ⟨rfl, [], rfl, IsSeq.nil⟩
  | n + 1, ts, ts', prs, h => by
      rw [takePairs] at h
      obtain ⟨⟨i, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨c, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      obtain ⟨⟨rest, ts3⟩, hE, hF⟩ := bind_eq_ok hD
      dsimp only at hF
      simp only [Except.ok.injEq, Prod.mk.injEq] at hF
      obtain ⟨rfl, rfl⟩ := hF
      obtain ⟨it, rfl, hi⟩ := takeNat_sound hA
      obtain ⟨vt, rfl, hv⟩ := takeNum_sound hC
      obtain ⟨hlen, seg, rfl, hseg⟩ := takePairs_sound hE
      exact ⟨by simp [hlen], [it, vt] ++ seg, by simp, IsSeq.cons ⟨it, vt, rfl, hi, hv⟩ hseg⟩

theorem takeNats_complete {seg suf : Toks} {ns : List Nat}
    (h : IsSeq IsNatItem seg ns) : takeNats ns.length (seg ++ suf) = .ok (ns, suf) := by
  induction h with
  | nil => simp [takeNats]
  | @cons s rest n ns hn hs ih =>
      obtain ⟨t, rfl, hi⟩ := hn
      have he : ([t] ++ rest) ++ suf = t :: (rest ++ suf) := by simp
      rw [he, List.length_cons, takeNats]
      simp only [bind, Except.bind, takeNat_prefix hi, ih]

theorem takeNats_sound : ∀ {n : Nat} {ts ts' : Toks} {ns : List Nat},
    takeNats n ts = .ok (ns, ts') →
      ns.length = n ∧ ∃ seg, ts = seg ++ ts' ∧ IsSeq IsNatItem seg ns
  | 0, ts, ts', ns, h => by
      obtain ⟨rfl, rfl⟩ : ns = [] ∧ ts = ts' := by simpa [takeNats, eq_comm] using h
      exact ⟨rfl, [], rfl, IsSeq.nil⟩
  | n + 1, ts, ts', ns, h => by
      rw [takeNats] at h
      obtain ⟨⟨i, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨rest, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      dsimp only at hD
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      obtain ⟨t, rfl, hi⟩ := takeNat_sound hA
      obtain ⟨hlen, seg, rfl, hseg⟩ := takeNats_sound hC
      exact ⟨by simp [hlen], [t] ++ seg, by simp, IsSeq.cons ⟨t, rfl, hi⟩ hseg⟩

/-- Variable names are arbitrary tokens, so a name list is its own rendering. -/
theorem takeStrings_complete {names suf : Toks} :
    takeStrings names.length (names ++ suf) = .ok (names, suf) := by
  induction names with
  | nil => simp [takeStrings]
  | cons t rest ih =>
      rw [List.length_cons, List.cons_append, takeStrings]
      simp only [bind, Except.bind, takeTok_prefix, ih]

theorem takeStrings_sound : ∀ {n : Nat} {ts ts' names : Toks},
    takeStrings n ts = .ok (names, ts') → names.length = n ∧ ts = names ++ ts'
  | 0, ts, ts', names, h => by
      obtain ⟨rfl, rfl⟩ : names = [] ∧ ts = ts' := by simpa [takeStrings, eq_comm] using h
      exact ⟨rfl, rfl⟩
  | n + 1, ts, ts', names, h => by
      rw [takeStrings] at h
      obtain ⟨⟨t, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨rest, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      dsimp only at hD
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      obtain rfl := takeTok_sound hA
      obtain ⟨hlen, rfl⟩ := takeStrings_sound hC
      exact ⟨by simp [hlen], by simp⟩

/-! ## Row bodies -/

theorem takeBody_complete {seg suf : Toks} {form : LinForm} {usesObj : Bool}
    (h : IsBody seg form usesObj) :
    takeBody (seg ++ suf) = .ok ((form, usesObj), suf) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨cnt, body, prs, rfl, hc, hp, rfl, rfl⟩
  · simp [takeBody, takeTok, bind, Except.bind]
  · have hb : (cnt == "OBJ") = false := by
      simpa using natTok_ne hc not_allDigits_OBJ
    rw [List.cons_append, takeBody]
    simp only [takeTok, bind, Except.bind, hb, Bool.false_eq_true, ite_false,
      parseNat_eq_some_iff.mpr hc, takePairs_complete hp]

theorem takeBody_sound {ts ts' : Toks} {form : LinForm} {usesObj : Bool}
    (h : takeBody ts = .ok ((form, usesObj), ts')) :
    ∃ seg, ts = seg ++ ts' ∧ IsBody seg form usesObj := by
  rw [takeBody] at h
  obtain ⟨⟨t, ts1⟩, hA, hB⟩ := bind_eq_ok h
  obtain rfl := takeTok_sound hA
  dsimp only at hB
  by_cases hobj : t = "OBJ"
  · subst hobj
    simp only [beq_self_eq_true, ite_true, Except.ok.injEq, Prod.mk.injEq] at hB
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hB
    exact ⟨["OBJ"], by simp, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · have hb : (t == "OBJ") = false := by simpa using hobj
    rw [hb] at hB
    cases hn : natOfDigits? t.toList with
    | none => rw [hn] at hB; exact absurd hB (by simp)
    | some p =>
        rw [hn] at hB
        dsimp only at hB
        obtain ⟨⟨pairs, ts2⟩, hC, hD⟩ := bind_eq_ok hB
        obtain ⟨hlen, seg, rfl, hseg⟩ := takePairs_sound hC
        dsimp only at hD
        simp only [Except.ok.injEq, Prod.mk.injEq] at hD
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hD
        obtain ⟨hd, hv⟩ := parseNat_eq_some_iff.mp hn
        exact ⟨t :: seg, by simp, Or.inr ⟨t, seg, pairs, rfl, ⟨hd, by rw [hlen, hv]⟩,
          hseg, rfl, rfl⟩⟩

/-! ## Constraint rows -/

theorem takeCon_complete {seg suf : Toks} {c : ViprCon} (h : IsCon seg c) :
    takeCon (seg ++ suf) = .ok (c, suf) := by
  obtain ⟨st, rt, body, rfl, hs, hr, hb⟩ := h
  rw [takeCon]
  simp only [List.cons_append, bind, Except.bind, takeTok_prefix,
    takeSense_prefix hs, takeNum_prefix hr, takeBody_complete hb]

theorem takeCon_sound {ts ts' : Toks} {c : ViprCon} (h : takeCon ts = .ok (c, ts')) :
    ∃ seg, ts = seg ++ ts' ∧ IsCon seg c := by
  rw [takeCon] at h
  obtain ⟨⟨name, ts1⟩, hA, hB⟩ := bind_eq_ok h
  obtain rfl := takeTok_sound hA
  dsimp only at hB
  obtain ⟨⟨sense, ts2⟩, hC, hD⟩ := bind_eq_ok hB
  obtain ⟨st, rfl, hs⟩ := takeSense_sound hC
  dsimp only at hD
  obtain ⟨⟨rhs, ts3⟩, hE, hF⟩ := bind_eq_ok hD
  obtain ⟨rt, rfl, hr⟩ := takeNum_sound hE
  dsimp only at hF
  obtain ⟨⟨⟨form, usesObj⟩, ts4⟩, hG, hH⟩ := bind_eq_ok hF
  obtain ⟨body, rfl, hb⟩ := takeBody_sound hG
  dsimp only at hH
  simp only [Except.ok.injEq, Prod.mk.injEq] at hH
  obtain ⟨rfl, rfl⟩ := hH
  exact ⟨name :: st :: rt :: body, by simp, st, rt, body, rfl, hs, hr, hb⟩

theorem takeCons_complete {seg suf : Toks} {cs : List ViprCon}
    (h : IsSeq IsCon seg cs) : takeCons cs.length (seg ++ suf) = .ok (cs, suf) := by
  induction h with
  | nil => simp [takeCons]
  | @cons s rest c cs hc hs ih =>
      rw [List.length_cons, List.append_assoc, takeCons]
      simp only [bind, Except.bind, takeCon_complete hc, ih]

theorem takeCons_sound : ∀ {n : Nat} {ts ts' : Toks} {cs : List ViprCon},
    takeCons n ts = .ok (cs, ts') →
      cs.length = n ∧ ∃ seg, ts = seg ++ ts' ∧ IsSeq IsCon seg cs
  | 0, ts, ts', cs, h => by
      obtain ⟨rfl, rfl⟩ : cs = [] ∧ ts = ts' := by simpa [takeCons, eq_comm] using h
      exact ⟨rfl, [], rfl, IsSeq.nil⟩
  | n + 1, ts, ts', cs, h => by
      rw [takeCons] at h
      obtain ⟨⟨c, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨rest, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      dsimp only at hD
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      obtain ⟨seg, rfl, hc⟩ := takeCon_sound hA
      obtain ⟨hlen, seg2, rfl, hseg⟩ := takeCons_sound hC
      exact ⟨by simp [hlen], seg ++ seg2, by simp, IsSeq.cons hc hseg⟩

/-! ## Solutions -/

theorem takeSol_complete {seg suf : Toks} {sol : String × List (Nat × ℚ)}
    (h : IsSol seg sol) : takeSol (seg ++ suf) = .ok (sol, suf) := by
  obtain ⟨cnt, body, rfl, hc, hp⟩ := h
  rw [takeSol]
  simp only [List.cons_append, bind, Except.bind, takeTok_prefix,
    takeNat_prefix hc, takePairs_complete hp]

theorem takeSol_sound {ts ts' : Toks} {sol : String × List (Nat × ℚ)}
    (h : takeSol ts = .ok (sol, ts')) : ∃ seg, ts = seg ++ ts' ∧ IsSol seg sol := by
  rw [takeSol] at h
  obtain ⟨⟨name, ts1⟩, hA, hB⟩ := bind_eq_ok h
  obtain rfl := takeTok_sound hA
  dsimp only at hB
  obtain ⟨⟨p, ts2⟩, hC, hD⟩ := bind_eq_ok hB
  obtain ⟨cnt, rfl, hc⟩ := takeNat_sound hC
  dsimp only at hD
  obtain ⟨⟨pairs, ts3⟩, hE, hF⟩ := bind_eq_ok hD
  obtain ⟨hlen, seg, rfl, hseg⟩ := takePairs_sound hE
  dsimp only at hF
  simp only [Except.ok.injEq, Prod.mk.injEq] at hF
  obtain ⟨rfl, rfl⟩ := hF
  exact ⟨name :: cnt :: seg, by simp, cnt, seg, rfl, by rw [← hlen] at hc; exact hc, hseg⟩

theorem takeSols_complete {seg suf : Toks} {sols : List (String × List (Nat × ℚ))}
    (h : IsSeq IsSol seg sols) : takeSols sols.length (seg ++ suf) = .ok (sols, suf) := by
  induction h with
  | nil => simp [takeSols]
  | @cons s rest sol sols hsol hs ih =>
      rw [List.length_cons, List.append_assoc, takeSols]
      simp only [bind, Except.bind, takeSol_complete hsol, ih]

theorem takeSols_sound : ∀ {n : Nat} {ts ts' : Toks}
    {sols : List (String × List (Nat × ℚ))}, takeSols n ts = .ok (sols, ts') →
      sols.length = n ∧ ∃ seg, ts = seg ++ ts' ∧ IsSeq IsSol seg sols
  | 0, ts, ts', sols, h => by
      obtain ⟨rfl, rfl⟩ : sols = [] ∧ ts = ts' := by simpa [takeSols, eq_comm] using h
      exact ⟨rfl, [], rfl, IsSeq.nil⟩
  | n + 1, ts, ts', sols, h => by
      rw [takeSols] at h
      obtain ⟨⟨sol, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨rest, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      dsimp only at hD
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      obtain ⟨seg, rfl, hsol⟩ := takeSol_sound hA
      obtain ⟨hlen, seg2, rfl, hseg⟩ := takeSols_sound hC
      exact ⟨by simp [hlen], seg ++ seg2, by simp, IsSeq.cons hsol hseg⟩

/-! ## Weak-completion bounds -/

/-- The kind token denotes exactly `L` or `U`. -/
theorem weakKind?_eq_some_iff {t : String} {k : Char} :
    weakKind? t = some k ↔ (t.toList = [k] ∧ (k = 'L' ∨ k = 'U')) := by
  constructor
  · intro h
    unfold weakKind? at h
    split at h
    case _ he =>
        obtain rfl : 'L' = k := Option.some.inj h
        exact ⟨he, Or.inl rfl⟩
    case _ he =>
        obtain rfl : 'U' = k := Option.some.inj h
        exact ⟨he, Or.inr rfl⟩
    case _ => simp at h
  · rintro ⟨hl, hk⟩
    unfold weakKind?
    rcases hk with rfl | rfl <;> simp [hl]

theorem takeWeakBound_complete {seg suf : Toks} {b : ViprWeakBound}
    (h : IsWeakBound seg b) : takeWeakBound (seg ++ suf) = .ok (b, suf) := by
  obtain ⟨kt, vt, rt, nt, rfl, hl, hk, hv, hr, hn⟩ := h
  rw [takeWeakBound]
  simp only [List.cons_append, List.nil_append, bind, Except.bind, takeTok_prefix,
    weakKind?_eq_some_iff.mpr ⟨hl, hk⟩, takeNat_prefix hv, takeNat_prefix hr,
    takeNum_prefix hn]

theorem takeWeakBound_sound {ts ts' : Toks} {b : ViprWeakBound}
    (h : takeWeakBound ts = .ok (b, ts')) :
    ∃ seg, ts = seg ++ ts' ∧ IsWeakBound seg b := by
  rw [takeWeakBound] at h
  obtain ⟨⟨kt, ts1⟩, hA, hB⟩ := bind_eq_ok h
  obtain rfl := takeTok_sound hA
  dsimp only at hB
  split at hB
  case _ hkind => simp at hB
  case _ k hkind =>
      obtain ⟨hl, hk⟩ := weakKind?_eq_some_iff.mp hkind
      obtain ⟨⟨vi, ts2⟩, hD, hE⟩ := bind_eq_ok hB
      obtain ⟨vt, rfl, hv⟩ := takeNat_sound hD
      dsimp only at hE
      obtain ⟨⟨ri, ts3⟩, hF, hG⟩ := bind_eq_ok hE
      obtain ⟨rt, rfl, hr⟩ := takeNat_sound hF
      dsimp only at hG
      obtain ⟨⟨val, ts4⟩, hH, hI⟩ := bind_eq_ok hG
      obtain ⟨nt, rfl, hn⟩ := takeNum_sound hH
      dsimp only at hI
      simp only [Except.ok.injEq, Prod.mk.injEq] at hI
      obtain ⟨rfl, rfl⟩ := hI
      exact ⟨[kt, vt, rt, nt], by simp, kt, vt, rt, nt, rfl, hl, hk, hv, hr, hn⟩

theorem takeWeakBoundsN_complete {seg suf : Toks} {bs : List ViprWeakBound}
    (h : IsSeq IsWeakBound seg bs) :
    takeWeakBoundsN bs.length (seg ++ suf) = .ok (bs, suf) := by
  induction h with
  | nil => simp [takeWeakBoundsN]
  | @cons s rest b bs hb hs ih =>
      rw [List.length_cons, List.append_assoc, takeWeakBoundsN]
      simp only [bind, Except.bind, takeWeakBound_complete hb, ih]

theorem takeWeakBoundsN_sound : ∀ {n : Nat} {ts ts' : Toks} {bs : List ViprWeakBound},
    takeWeakBoundsN n ts = .ok (bs, ts') →
      bs.length = n ∧ ∃ seg, ts = seg ++ ts' ∧ IsSeq IsWeakBound seg bs
  | 0, ts, ts', bs, h => by
      obtain ⟨rfl, rfl⟩ : bs = [] ∧ ts = ts' := by
        simpa [takeWeakBoundsN, eq_comm] using h
      exact ⟨rfl, [], rfl, IsSeq.nil⟩
  | n + 1, ts, ts', bs, h => by
      rw [takeWeakBoundsN] at h
      obtain ⟨⟨b, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨rest, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      dsimp only at hD
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      obtain ⟨seg, rfl, hb⟩ := takeWeakBound_sound hA
      obtain ⟨hlen, seg2, rfl, hseg⟩ := takeWeakBoundsN_sound hC
      exact ⟨by simp [hlen], seg ++ seg2, by simp, IsSeq.cons hb hseg⟩

theorem takeWeakBounds_complete {seg suf : Toks} {wb : ViprWeakBounds}
    (h : IsWeakBoundsBlock seg wb) : takeWeakBounds (seg ++ suf) = .ok (wb, suf) := by
  obtain ⟨cnt, body, bs, rfl, hc, hbs, hw⟩ := h
  have hflat : ("{" :: cnt :: (body ++ ["}"])) ++ suf
      = "{" :: cnt :: (body ++ ("}" :: suf)) := by simp
  rw [hflat, takeWeakBounds]
  simp only [bind, Except.bind, expectTok_prefix, takeNat_prefix hc,
    takeWeakBoundsN_complete hbs, expectTok_prefix]
  rcases hw with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
  · simp
  · cases bs with
    | nil => exact absurd rfl hne
    | cons b0 brest => rfl

theorem takeWeakBounds_sound {ts ts' : Toks} {wb : ViprWeakBounds}
    (h : takeWeakBounds ts = .ok (wb, ts')) :
    ∃ seg, ts = seg ++ ts' ∧ IsWeakBoundsBlock seg wb := by
  rw [takeWeakBounds] at h
  obtain ⟨ts1, hA, hB⟩ := bind_eq_ok h
  obtain rfl := expectTok_sound hA
  obtain ⟨⟨n, ts2⟩, hC, hD⟩ := bind_eq_ok hB
  obtain ⟨cnt, rfl, hc⟩ := takeNat_sound hC
  dsimp only at hD
  obtain ⟨⟨bs, ts3⟩, hE, hF⟩ := bind_eq_ok hD
  obtain ⟨hlen, seg, rfl, hseg⟩ := takeWeakBoundsN_sound hE
  dsimp only at hF
  obtain ⟨ts4, hG, hH⟩ := bind_eq_ok hF
  obtain rfl := expectTok_sound hG
  rw [← hlen] at hc
  cases bs with
  | nil =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hH
      obtain ⟨rfl, rfl⟩ := hH
      exact ⟨"{" :: cnt :: (seg ++ ["}"]), by simp, cnt, seg, [], rfl, hc, hseg,
        Or.inl ⟨rfl, rfl⟩⟩
  | cons b0 brest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hH
      obtain ⟨rfl, rfl⟩ := hH
      exact ⟨"{" :: cnt :: (seg ++ ["}"]), by simp, cnt, seg, b0 :: brest, rfl, hc, hseg,
        Or.inr ⟨by simp, rfl⟩⟩

/-! ## Reasons -/

theorem takeReason_complete {nm : String} {seg suf : Toks} {r : ViprReason}
    (h : IsReason seg r) : takeReason nm (seg ++ suf) = .ok (r, suf) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨cnt, body, prs, rfl, hc, hp, rfl⟩
    | ⟨blk, wb, cnt, body, prs, rfl, hblk, hc, hp, rfl⟩
    | ⟨cnt, body, prs, rfl, hc, hp, rfl⟩
    | ⟨t1, t2, t3, t4, i1, l1, i2, l2, rfl, h1, h2, h3, h4, rfl⟩
  · simp [takeReason, expectTok, takeTok, bind, Except.bind]
  · simp [takeReason, expectTok, takeTok, bind, Except.bind]
  · have hw : (cnt == "weak") = false := by simpa using natTok_ne hc not_allDigits_weak
    have hflat : ("{" :: "lin" :: cnt :: (body ++ ["}"])) ++ suf
        = "{" :: "lin" :: cnt :: (body ++ ("}" :: suf)) := by simp
    rw [hflat, takeReason]
    simp only [bind, Except.bind, expectTok_prefix, takeTok_prefix]
    simp only [hw, Bool.false_eq_true, ite_false, parseNat_eq_some_iff.mpr hc,
      takePairs_complete hp, expectTok_prefix]
  · have hflat : ("{" :: "lin" :: "weak" :: (blk ++ cnt :: (body ++ ["}"]))) ++ suf
        = "{" :: "lin" :: "weak" :: (blk ++ (cnt :: (body ++ ("}" :: suf)))) := by simp
    rw [hflat, takeReason]
    simp only [bind, Except.bind, expectTok_prefix, takeTok_prefix]
    simp only [beq_self_eq_true, ite_true, takeWeakBounds_complete hblk,
      takeNat_prefix hc, takePairs_complete hp, expectTok_prefix]
  · have hflat : ("{" :: "rnd" :: cnt :: (body ++ ["}"])) ++ suf
        = "{" :: "rnd" :: cnt :: (body ++ ("}" :: suf)) := by simp
    rw [hflat, takeReason]
    simp only [bind, Except.bind, expectTok_prefix, takeTok_prefix]
    simp only [takeNat_prefix hc, takePairs_complete hp, expectTok_prefix]
  · have hflat : (["{", "uns", t1, t2, t3, t4, "}"] : Toks) ++ suf
        = "{" :: "uns" :: t1 :: t2 :: t3 :: t4 :: "}" :: suf := by simp
    rw [hflat, takeReason]
    simp only [bind, Except.bind, expectTok_prefix, takeTok_prefix]
    simp only [takeNat_prefix h1, takeNat_prefix h2, takeNat_prefix h3, takeNat_prefix h4,
      expectTok_prefix]

theorem takeReason_sound {nm : String} {ts ts' : Toks} {r : ViprReason}
    (h : takeReason nm ts = .ok (r, ts')) :
    ∃ seg, ts = seg ++ ts' ∧ IsReason seg r := by
  rw [takeReason] at h
  obtain ⟨ts1, hA, hB⟩ := bind_eq_ok h
  obtain rfl := expectTok_sound hA
  obtain ⟨⟨kw, ts2⟩, hC, hD⟩ := bind_eq_ok hB
  obtain rfl := takeTok_sound hC
  dsimp only at hD
  split at hD
  case h_1 =>
      obtain ⟨ts3, hE, hF⟩ := bind_eq_ok hD
      obtain rfl := expectTok_sound hE
      simp only [Except.ok.injEq, Prod.mk.injEq] at hF
      obtain ⟨rfl, rfl⟩ := hF
      exact ⟨["{", "asm", "}"], by simp, Or.inl ⟨rfl, rfl⟩⟩
  case h_2 =>
      obtain ⟨ts3, hE, hF⟩ := bind_eq_ok hD
      obtain rfl := expectTok_sound hE
      simp only [Except.ok.injEq, Prod.mk.injEq] at hF
      obtain ⟨rfl, rfl⟩ := hF
      exact ⟨["{", "sol", "}"], by simp, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  case h_3 =>
      obtain ⟨⟨next, ts3⟩, hE, hF⟩ := bind_eq_ok hD
      obtain rfl := takeTok_sound hE
      dsimp only at hF
      split at hF
      case isTrue hwk =>
          obtain rfl : next = "weak" := by simpa using hwk
          obtain ⟨⟨bounds, ts4⟩, hG, hH⟩ := bind_eq_ok hF
          obtain ⟨blk, rfl, hblk⟩ := takeWeakBounds_sound hG
          dsimp only at hH
          obtain ⟨⟨p, ts5⟩, hI, hJ⟩ := bind_eq_ok hH
          obtain ⟨cnt, rfl, hc⟩ := takeNat_sound hI
          dsimp only at hJ
          obtain ⟨⟨pairs, ts6⟩, hK, hL⟩ := bind_eq_ok hJ
          obtain ⟨hlen, body, rfl, hp⟩ := takePairs_sound hK
          dsimp only at hL
          obtain ⟨ts7, hM, hN⟩ := bind_eq_ok hL
          obtain rfl := expectTok_sound hM
          simp only [Except.ok.injEq, Prod.mk.injEq] at hN
          obtain ⟨rfl, rfl⟩ := hN
          exact ⟨"{" :: "lin" :: "weak" :: (blk ++ cnt :: (body ++ ["}"])), by simp,
            Or.inr (Or.inr (Or.inr (Or.inl ⟨blk, bounds, cnt, body, pairs, rfl, hblk,
              by rw [hlen]; exact hc, hp, rfl⟩)))⟩
      case isFalse hwk =>
          split at hF
          case h_1 => split at hF <;> simp at hF
          case h_2 p hsome =>
              obtain ⟨⟨pairs, ts4⟩, hG, hH⟩ := bind_eq_ok hF
              obtain ⟨hlen, body, rfl, hp⟩ := takePairs_sound hG
              dsimp only at hH
              obtain ⟨ts5, hI, hJ⟩ := bind_eq_ok hH
              obtain rfl := expectTok_sound hI
              simp only [Except.ok.injEq, Prod.mk.injEq] at hJ
              obtain ⟨rfl, rfl⟩ := hJ
              obtain ⟨hd, hv⟩ := parseNat_eq_some_iff.mp hsome
              exact ⟨"{" :: "lin" :: next :: (body ++ ["}"]), by simp,
                Or.inr (Or.inr (Or.inl ⟨next, body, pairs, rfl, ⟨hd, by rw [hlen, hv]⟩,
                  hp, rfl⟩))⟩
  case h_4 =>
      obtain ⟨⟨p, ts3⟩, hE, hF⟩ := bind_eq_ok hD
      obtain ⟨cnt, rfl, hc⟩ := takeNat_sound hE
      dsimp only at hF
      obtain ⟨⟨pairs, ts4⟩, hG, hH⟩ := bind_eq_ok hF
      obtain ⟨hlen, body, rfl, hp⟩ := takePairs_sound hG
      dsimp only at hH
      obtain ⟨ts5, hI, hJ⟩ := bind_eq_ok hH
      obtain rfl := expectTok_sound hI
      simp only [Except.ok.injEq, Prod.mk.injEq] at hJ
      obtain ⟨rfl, rfl⟩ := hJ
      exact ⟨"{" :: "rnd" :: cnt :: (body ++ ["}"]), by simp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cnt, body, pairs, rfl,
          by rw [hlen]; exact hc, hp, rfl⟩))))⟩
  case h_5 =>
      obtain ⟨⟨i1, ts3⟩, hE, hF⟩ := bind_eq_ok hD
      obtain ⟨t1, rfl, h1⟩ := takeNat_sound hE
      dsimp only at hF
      obtain ⟨⟨l1, ts4⟩, hG, hH⟩ := bind_eq_ok hF
      obtain ⟨t2, rfl, h2⟩ := takeNat_sound hG
      dsimp only at hH
      obtain ⟨⟨i2, ts5⟩, hI, hJ⟩ := bind_eq_ok hH
      obtain ⟨t3, rfl, h3⟩ := takeNat_sound hI
      dsimp only at hJ
      obtain ⟨⟨l2, ts6⟩, hK, hL⟩ := bind_eq_ok hJ
      obtain ⟨t4, rfl, h4⟩ := takeNat_sound hK
      dsimp only at hL
      obtain ⟨ts7, hM, hN⟩ := bind_eq_ok hL
      obtain rfl := expectTok_sound hM
      simp only [Except.ok.injEq, Prod.mk.injEq] at hN
      obtain ⟨rfl, rfl⟩ := hN
      exact ⟨["{", "uns", t1, t2, t3, t4, "}"], by simp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨t1, t2, t3, t4, i1, l1, i2, l2, rfl, h1, h2, h3, h4, rfl⟩))))⟩
  case h_6 => simp at hD

/-! ## Derivations

The scope keyword is matched greedily, so `takeScope` is the only lookahead in the
parser and the only place where a production depends on what follows it. Because the
`DER` section is last, `IsDers` describes the whole remaining stream and these lemmas
need no suffix. -/

private theorem head?_append_ne {a b : Toks} {s : String} (h : (a ++ b).head? ≠ some s) :
    a.head? ≠ some s := by
  cases a with
  | nil => simp
  | cons x xs => simpa using h

theorem takeScope_global (suf : Toks) : takeScope ("global" :: suf) = (true, suf) := rfl

theorem takeScope_local (suf : Toks) : takeScope ("local" :: suf) = (false, suf) := rfl

theorem takeScope_bare {ts : Toks} (h1 : ts.head? ≠ some "global")
    (h2 : ts.head? ≠ some "local") : takeScope ts = (false, ts) := by
  cases ts with
  | nil => rfl
  | cons t rest =>
      by_cases hg : t = "global"
      · exact absurd (by simp [hg]) h1
      · by_cases hl : t = "local"
        · exact absurd (by simp [hl]) h2
        · simp [takeScope, hg, hl]

theorem takeScope_cases (ts : Toks) :
    (∃ rest, ts = "global" :: rest ∧ takeScope ts = (true, rest)) ∨
    (∃ rest, ts = "local" :: rest ∧ takeScope ts = (false, rest)) ∨
    (takeScope ts = (false, ts) ∧ ts.head? ≠ some "global" ∧ ts.head? ≠ some "local") := by
  cases ts with
  | nil => exact Or.inr (Or.inr ⟨rfl, by simp, by simp⟩)
  | cons t rest =>
      by_cases hg : t = "global"
      · subst hg; exact Or.inl ⟨rest, rfl, rfl⟩
      · by_cases hl : t = "local"
        · subst hl; exact Or.inr (Or.inl ⟨rest, rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨by simp [takeScope, hg, hl], by simp [hg], by simp [hl]⟩)

/-- The parser reads a `DER` row's core off the front of the stream, then whatever the
scope lookahead says about the rest. -/
theorem takeDer_core {core suf : Toks} {d : ViprDer} (h : IsDerCore core d) :
    takeDer (core ++ suf)
      = .ok ({ d with isGlobal := (takeScope suf).1 }, (takeScope suf).2) := by
  obtain ⟨st, rt, body, rsn, it, rfl, hs, hr, hb, hrsn, hi⟩ := h
  have hflat : (d.name :: st :: rt :: (body ++ (rsn ++ [it]))) ++ suf
      = d.name :: st :: rt :: (body ++ (rsn ++ (it :: suf))) := by simp
  rw [hflat, takeDer]
  simp only [bind, Except.bind, takeTok_prefix, takeSense_prefix hs, takeNum_prefix hr,
    takeBody_complete hb, takeReason_complete hrsn, takeInt_prefix hi]

theorem takeDer_sound {ts ts' : Toks} {d : ViprDer} (h : takeDer ts = .ok (d, ts')) :
    (∃ core, ts = core ++ "global" :: ts' ∧ IsDerCore core d ∧ d.isGlobal = true) ∨
    (∃ core, ts = core ++ "local" :: ts' ∧ IsDerCore core d ∧ d.isGlobal = false) ∨
    (∃ core, ts = core ++ ts' ∧ IsDerCore core d ∧ d.isGlobal = false ∧
      ts'.head? ≠ some "global" ∧ ts'.head? ≠ some "local") := by
  rw [takeDer] at h
  obtain ⟨⟨name, ts1⟩, hA, hB⟩ := bind_eq_ok h
  obtain rfl := takeTok_sound hA
  dsimp only at hB
  obtain ⟨⟨sense, ts2⟩, hC, hD⟩ := bind_eq_ok hB
  obtain ⟨st, rfl, hs⟩ := takeSense_sound hC
  dsimp only at hD
  obtain ⟨⟨rhs, ts3⟩, hE, hF⟩ := bind_eq_ok hD
  obtain ⟨rt, rfl, hr⟩ := takeNum_sound hE
  dsimp only at hF
  obtain ⟨⟨⟨form, usesObj⟩, ts4⟩, hG, hH⟩ := bind_eq_ok hF
  obtain ⟨body, rfl, hb⟩ := takeBody_sound hG
  dsimp only at hH
  obtain ⟨⟨reason, ts5⟩, hI, hJ⟩ := bind_eq_ok hH
  obtain ⟨rsn, rfl, hrsn⟩ := takeReason_sound hI
  dsimp only at hJ
  obtain ⟨⟨idx, ts6⟩, hK, hL⟩ := bind_eq_ok hJ
  obtain ⟨it, rfl, hi⟩ := takeInt_sound hK
  dsimp only at hL
  rcases takeScope_cases ts6 with ⟨rest, hts6, hsc⟩ | ⟨rest, hts6, hsc⟩ | ⟨hsc, hgl, hlo⟩
  · rw [hsc] at hL
    simp only [Except.ok.injEq, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    subst hts6
    exact Or.inl ⟨name :: st :: rt :: (body ++ (rsn ++ [it])), by simp,
      ⟨st, rt, body, rsn, it, rfl, hs, hr, hb, hrsn, hi⟩, rfl⟩
  · rw [hsc] at hL
    simp only [Except.ok.injEq, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    subst hts6
    exact Or.inr (Or.inl ⟨name :: st :: rt :: (body ++ (rsn ++ [it])), by simp,
      ⟨st, rt, body, rsn, it, rfl, hs, hr, hb, hrsn, hi⟩, rfl⟩)
  · rw [hsc] at hL
    simp only [Except.ok.injEq, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    exact Or.inr (Or.inr ⟨name :: st :: rt :: (body ++ (rsn ++ [it])), by simp,
      ⟨st, rt, body, rsn, it, rfl, hs, hr, hb, hrsn, hi⟩, rfl, hgl, hlo⟩)

theorem takeDers_complete {seg : Toks} {ds : List ViprDer} (h : IsDers seg ds) :
    takeDers ds.length seg = .ok (ds, []) := by
  induction h with
  | nil => simp [takeDers]
  | @globalFlag core rest d ds hc hg hs ih =>
      have hd : ({ d with isGlobal := true } : ViprDer) = d := by rw [← hg]
      have hstep : takeDer (core ++ "global" :: rest) = .ok (d, rest) := by
        rw [takeDer_core hc, takeScope_global, hd]
      rw [List.length_cons, takeDers]
      simp only [bind, Except.bind, hstep, ih]
  | @localFlag core rest d ds hc hg hs ih =>
      have hd : ({ d with isGlobal := false } : ViprDer) = d := by rw [← hg]
      have hstep : takeDer (core ++ "local" :: rest) = .ok (d, rest) := by
        rw [takeDer_core hc, takeScope_local, hd]
      rw [List.length_cons, takeDers]
      simp only [bind, Except.bind, hstep, ih]
  | @bare core rest d ds hc hg hne hs ih =>
      have hd : ({ d with isGlobal := false } : ViprDer) = d := by rw [← hg]
      have hstep : takeDer (core ++ rest) = .ok (d, rest) := by
        rw [takeDer_core hc, takeScope_bare hne.1 hne.2, hd]
      rw [List.length_cons, takeDers]
      simp only [bind, Except.bind, hstep, ih]

theorem takeDers_sound : ∀ {n : Nat} {ts ts' : Toks} {ds : List ViprDer},
    takeDers n ts = .ok (ds, ts') →
      ds.length = n ∧ ∃ seg, ts = seg ++ ts' ∧ IsDers seg ds
  | 0, ts, ts', ds, h => by
      obtain ⟨rfl, rfl⟩ : ds = [] ∧ ts = ts' := by simpa [takeDers, eq_comm] using h
      exact ⟨rfl, [], rfl, IsDers.nil⟩
  | n + 1, ts, ts', ds, h => by
      rw [takeDers] at h
      obtain ⟨⟨d, ts1⟩, hA, hB⟩ := bind_eq_ok h
      obtain ⟨⟨rest, ts2⟩, hC, hD⟩ := bind_eq_ok hB
      dsimp only at hD
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      obtain ⟨hlen, seg, rfl, hseg⟩ := takeDers_sound hC
      rcases takeDer_sound hA with ⟨core, rfl, hc, hg⟩ | ⟨core, rfl, hc, hg⟩
        | ⟨core, rfl, hc, hg, h1, h2⟩
      · exact ⟨by simp [hlen], core ++ "global" :: seg, by simp,
          IsDers.globalFlag hc hg hseg⟩
      · exact ⟨by simp [hlen], core ++ "local" :: seg, by simp,
          IsDers.localFlag hc hg hseg⟩
      · exact ⟨by simp [hlen], core ++ seg, by simp,
          IsDers.bare hc hg ⟨head?_append_ne h1, head?_append_ne h2⟩ hseg⟩

/-! ## The relation to prove -/

theorem takeRtp_complete {seg suf : Toks} {rtp : ViprRtp} (h : IsRtpSection seg rtp) :
    takeRtp (seg ++ suf) = .ok (rtp, suf) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨lt, ut, lb, ub, rfl, hlb, hub, rfl⟩
  · simp [takeRtp, expectTok, takeTok, bind, Except.bind]
  · have hflat : (["RTP", "range", lt, ut] : Toks) ++ suf
        = "RTP" :: "range" :: lt :: ut :: suf := by simp
    rw [hflat, takeRtp]
    simp only [bind, Except.bind, expectTok_prefix, takeTok_prefix]
    simp only [takeBound_eq_ok_iff.mpr hlb, takeBound_eq_ok_iff.mpr hub]
    simp

theorem takeRtp_sound {ts ts' : Toks} {rtp : ViprRtp} (h : takeRtp ts = .ok (rtp, ts')) :
    ∃ seg, ts = seg ++ ts' ∧ IsRtpSection seg rtp := by
  rw [takeRtp] at h
  obtain ⟨ts1, hA, hB⟩ := bind_eq_ok h
  obtain rfl := expectTok_sound hA
  obtain ⟨⟨kind, ts2⟩, hC, hD⟩ := bind_eq_ok hB
  obtain rfl := takeTok_sound hC
  dsimp only at hD
  split at hD
  case isTrue hk =>
      obtain rfl : kind = "infeas" := eq_of_beq hk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hD
      obtain ⟨rfl, rfl⟩ := hD
      exact ⟨["RTP", "infeas"], by simp, Or.inl ⟨rfl, rfl⟩⟩
  case isFalse hk =>
      split at hD
      case isFalse hk2 => simp at hD
      case isTrue hk2 =>
          obtain rfl : kind = "range" := eq_of_beq hk2
          obtain ⟨⟨lt, tsa⟩, hE, hF⟩ := bind_eq_ok hD
          obtain rfl := takeTok_sound hE
          dsimp only at hF
          obtain ⟨⟨ut, tsb⟩, hG, hH⟩ := bind_eq_ok hF
          obtain rfl := takeTok_sound hG
          dsimp only at hH
          obtain ⟨lb, hI, hJ⟩ := bind_eq_ok hH
          obtain ⟨ub, hK, hL⟩ := bind_eq_ok hJ
          simp only [Except.ok.injEq, Prod.mk.injEq] at hL
          obtain ⟨rfl, rfl⟩ := hL
          exact ⟨["RTP", "range", lt, ut], by simp,
            Or.inr ⟨lt, ut, lb, ub, rfl, takeBound_eq_ok_iff.mp hI,
              takeBound_eq_ok_iff.mp hK, rfl⟩⟩

end LeanVIPR.Parser
