module

public import LeanVIPR.Impl.Parser.Render
public import LeanVIPR.Thm.Parser
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The round trip

Reading what the renderer writes gives back what was written. Working file; the statement
worth citing is in `LeanVIPR.Thm.Parser`.

The parse direction comes free from `parseVipr_complete`: it suffices to show the text
the renderer emits is derived by the grammar as the certificate it came from. So all the
work here is that `digitsValue` inverts the digit printer, and that each production can
be built from the rendered fields.
-/

namespace LeanVIPR.Impl

open LeanVIPR.Parser LeanVIPR.Semantics

/-! ## Digits -/

private theorem digitChar_isDigit : ∀ {r : Nat}, r < 10 → (digitChar r).isDigit
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | n + 10, h => absurd h (by omega)

private theorem digitChar_sub : ∀ {r : Nat}, r < 10 →
    (digitChar r).toNat - '0'.toNat = r
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | n + 10, h => absurd h (by omega)

/-- The accumulator invariant: what is already written contributes its own value, shifted
by however many digits still get prepended. -/
private theorem natDigitsAux_value : ∀ (n : Nat) (acc : List Char),
    digitsValue (natDigitsAux n acc) = n * 10 ^ acc.length + digitsValue acc
  | 0, acc => by simp [natDigitsAux]
  | n + 1, acc => by
      rw [natDigitsAux]
      have hr : (n + 1) % 10 < 10 := Nat.mod_lt _ (by omega)
      rw [natDigitsAux_value ((n + 1) / 10) _]
      simp only [List.length_cons, digitsValue, digitChar_sub hr]
      have hdm : (n + 1) / 10 * 10 + (n + 1) % 10 = n + 1 := by omega
      have key : ∀ K D : Nat,
          (n + 1) / 10 * (10 ^ 1 * K) + ((n + 1) % 10 * K + D) = (n + 1) * K + D := by
        intro K D
        rw [show (n + 1) / 10 * (10 ^ 1 * K) = (n + 1) / 10 * 10 * K by ring,
          ← Nat.add_assoc, ← Nat.add_mul, hdm]
      rw [show (10 : Nat) ^ (acc.length + 1) = 10 ^ 1 * 10 ^ acc.length by ring]
      exact key _ _

private theorem natDigitsAux_allDigits : ∀ (n : Nat) (acc : List Char),
    AllDigits acc → AllDigits (natDigitsAux n acc)
  | 0, acc, h => by simpa [natDigitsAux] using h
  | n + 1, acc, h => by
      rw [natDigitsAux]
      refine natDigitsAux_allDigits _ _ ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact digitChar_isDigit (Nat.mod_lt _ (by omega))
      · exact h c hc

private theorem natDigitsAux_ne_nil : ∀ (n : Nat) (acc : List Char),
    acc ≠ [] → natDigitsAux n acc ≠ []
  | 0, acc, h => by simpa [natDigitsAux] using h
  | n + 1, acc, _ => by
      rw [natDigitsAux]
      exact natDigitsAux_ne_nil _ _ (by simp)

theorem natDigits_value (n : Nat) : digitsValue (natDigits n) = n := by
  unfold natDigits
  split
  case isTrue h => subst h; simp [digitsValue]
  case isFalse h =>
      rw [natDigitsAux_value]
      simp [digitsValue]

theorem natDigits_isDigits (n : Nat) : IsDigits (natDigits n) := by
  unfold natDigits IsDigits
  split
  case isTrue h =>
      refine ⟨by simp, ?_⟩
      intro c hc
      obtain rfl : c = '0' := by simpa using hc
      decide
  case isFalse h =>
      refine ⟨?_, natDigitsAux_allDigits _ _ (by simp [AllDigits])⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [natDigitsAux]
      exact natDigitsAux_ne_nil _ _ (by simp)

/-! ## Numbers -/

theorem renderNat_isNatTok (n : Nat) : IsNatTok (renderNat n) n := by
  refine ⟨?_, ?_⟩
  · simpa [renderNat] using natDigits_isDigits n
  · simp [renderNat, natDigits_value]

private theorem renderInt_toList (z : Int) :
    (renderInt z).toList =
      (if z < 0 then ['-'] else []) ++ natDigits z.natAbs := by
  unfold renderInt
  split
  case isTrue h => simp
  case isFalse h => simp [renderNat]

theorem renderInt_isIntValue (z : Int) : IsIntValue (renderInt z).toList z := by
  refine ⟨if z < 0 then ['-'] else [], natDigits z.natAbs,
    ⟨renderInt_toList z, ?_, natDigits_isDigits _⟩, ?_⟩
  · split
    case isTrue => exact Or.inr (Or.inl rfl)
    case isFalse => exact Or.inl rfl
  · unfold intValue
    by_cases hz : z < 0
    · rw [show (if z < 0 then ['-'] else ([] : List Char)) = ['-'] from by simp [hz]]
      simp only [natDigits_value]
      split
      case isTrue => omega
      case isFalse hc => simp at hc
    · rw [show (if z < 0 then ['-'] else ([] : List Char)) = [] from by simp [hz]]
      simp only [natDigits_value]
      split
      case isTrue hc => simp at hc
      case isFalse => omega

theorem renderInt_isIntTok (z : Int) : IsIntTok (renderInt z) z := renderInt_isIntValue z

private theorem renderRat_toList (q : ℚ) :
    (renderRat q).toList =
      (if q.num < 0 then ['-'] else []) ++
        (natDigits q.num.natAbs ++ '/' :: ([] ++ natDigits q.den)) := by
  simp [renderRat, renderInt_toList]

theorem renderRat_isNumValue (q : ℚ) : IsNumValue (renderRat q).toList q := by
  refine Or.inr (Or.inr ⟨if q.num < 0 then ['-'] else [], natDigits q.num.natAbs, [],
    natDigits q.den, ⟨renderRat_toList q, ?_, natDigits_isDigits _, Or.inl rfl,
      natDigits_isDigits _, ?_⟩, ?_⟩)
  · split
    case isTrue => exact Or.inr (Or.inl rfl)
    case isFalse => exact Or.inl rfl
  · rw [natDigits_value]
    exact q.den_nz
  · unfold quotValue intValue
    have hnum : ((if (if q.num < 0 then ['-'] else []) = ['-'] then
          -(digitsValue (natDigits q.num.natAbs) : Int)
        else (digitsValue (natDigits q.num.natAbs) : Int))) = q.num := by
      rw [natDigits_value]
      by_cases hz : q.num < 0
      · rw [show (if q.num < 0 then ['-'] else ([] : List Char)) = ['-'] from by simp [hz]]
        split
        case isTrue => omega
        case isFalse hc => simp at hc
      · rw [show (if q.num < 0 then ['-'] else ([] : List Char)) = [] from by simp [hz]]
        split
        case isTrue hc => simp at hc
        case isFalse => omega
    have hden : ((if ([] : List Char) = ['-'] then
          -(digitsValue (natDigits q.den) : Int)
        else (digitsValue (natDigits q.den) : Int))) = (q.den : Int) := by
      rw [natDigits_value]
      simp
    rw [hnum, hden]
    exact (Rat.num_div_den q).symm

theorem renderRat_isNumTok (q : ℚ) : IsNumTok (renderRat q) q := renderRat_isNumValue q

/-! ## Rows

Each level has the same shape: if the value is renderable at all — which is what a
hypothesis `IsX ts x` says — then the renderer renders it. Carrying the hypothesis is
what supplies the side conditions the grammar imposes but a bare `Vipr` does not, such
as a sense being one of `E`, `L`, `G`. -/

theorem renderPair_isPair (p : Nat × ℚ) : IsPair (renderPair p) p :=
  ⟨renderNat p.1, renderRat p.2, rfl, renderNat_isNatTok p.1, renderRat_isNumTok p.2⟩

theorem renderPairs_isSeq : ∀ prs : List (Nat × ℚ), IsSeq IsPair (renderPairs prs) prs
  | [] => by simpa [renderPairs] using IsSeq.nil
  | p :: ps => by
      rw [renderPairs]
      exact IsSeq.cons (renderPair_isPair p) (renderPairs_isSeq ps)

theorem renderNats_isSeq : ∀ ns : List Nat, IsSeq IsNatItem (renderNats ns) ns
  | [] => by simpa [renderNats] using IsSeq.nil
  | n :: ns => by
      rw [renderNats]
      exact IsSeq.cons ⟨renderNat n, rfl, renderNat_isNatTok n⟩ (renderNats_isSeq ns)

theorem renderChar_isSenseTok {c : Char} (h : c = 'E' ∨ c = 'L' ∨ c = 'G') :
    IsSenseTok (renderChar c) c := ⟨by simp [renderChar], h⟩

theorem renderBody_isBody {form : LinForm} {usesObj : Bool}
    (h : usesObj = true → form = []) :
    IsBody (renderBody form usesObj) form usesObj := by
  unfold renderBody
  cases usesObj with
  | true => exact Or.inl ⟨by simp, h rfl, rfl⟩
  | false =>
      refine Or.inr ⟨renderNat form.length,
        renderPairs (form.map (fun t => (t.idx, t.coeff))),
        form.map (fun t => (t.idx, t.coeff)), by simp, ?_, renderPairs_isSeq _, ?_, rfl⟩
      · simpa using renderNat_isNatTok form.length
      · clear h
        induction form with
        | nil => rfl
        | cons t ts ih =>
            simp only [List.map_cons]
            rw [← ih]

/-- What a body production forces about the row: an `OBJ` body has no explicit form. -/
private theorem isBody_objForm {ts : Toks} {form : LinForm} {usesObj : Bool}
    (h : IsBody ts form usesObj) : usesObj = true → form = [] := by
  rcases h with ⟨-, hf, -⟩ | ⟨-, -, -, -, -, -, -, hu⟩
  · exact fun _ => hf
  · intro ht; rw [hu] at ht; exact absurd ht (by simp)

theorem renderCon_isCon {ts : Toks} {c : ViprCon} (h : IsCon ts c) :
    IsCon (renderCon c) c := by
  obtain ⟨st, rt, body, -, hs, -, hb⟩ := h
  exact ⟨renderChar c.sense, renderRat c.rhs, renderBody c.form c.usesObj, rfl,
    renderChar_isSenseTok hs.2, renderRat_isNumTok c.rhs, renderBody_isBody
      (isBody_objForm hb)⟩

theorem renderCons_isSeq : ∀ {ts : Toks} {cs : List ViprCon}, IsSeq IsCon ts cs →
    IsSeq IsCon (renderCons cs) cs
  | _, _, IsSeq.nil => by simpa [renderCons] using IsSeq.nil
  | _, _, IsSeq.cons hc hs => by
      rw [renderCons]
      exact IsSeq.cons (renderCon_isCon hc) (renderCons_isSeq hs)

theorem renderSol_isSol (s : String × List (Nat × ℚ)) : IsSol (renderSol s) s :=
  ⟨renderNat s.2.length, renderPairs s.2, rfl, renderNat_isNatTok s.2.length,
    renderPairs_isSeq s.2⟩

theorem renderSols_isSeq : ∀ ss : List (String × List (Nat × ℚ)),
    IsSeq IsSol (renderSols ss) ss
  | [] => by simpa [renderSols] using IsSeq.nil
  | s :: ss => by
      rw [renderSols]
      exact IsSeq.cons (renderSol_isSol s) (renderSols_isSeq ss)

theorem renderWeakBound_isWeakBound {ts : Toks} {b : ViprWeakBound}
    (h : IsWeakBound ts b) : IsWeakBound (renderWeakBound b) b := by
  obtain ⟨kt, vt, rt, nt, -, -, hk, -, -, -⟩ := h
  exact ⟨renderChar b.kind, renderNat b.varIdx, renderNat b.rowIdx, renderRat b.value,
    rfl, by simp [renderChar], hk, renderNat_isNatTok _, renderNat_isNatTok _,
    renderRat_isNumTok _⟩

theorem renderWeakBounds_isSeq : ∀ {ts : Toks} {bs : List ViprWeakBound},
    IsSeq IsWeakBound ts bs → IsSeq IsWeakBound (renderWeakBounds bs) bs
  | _, _, IsSeq.nil => by simpa [renderWeakBounds] using IsSeq.nil
  | _, _, IsSeq.cons hb hs => by
      rw [renderWeakBounds]
      exact IsSeq.cons (renderWeakBound_isWeakBound hb) (renderWeakBounds_isSeq hs)

/-! ## Reasons and derivations -/

theorem renderWeakBlock_isBlock {ts : Toks} {wb : ViprWeakBounds}
    (h : IsWeakBoundsBlock ts wb) : IsWeakBoundsBlock (renderWeakBlock wb) wb := by
  obtain ⟨cnt, body, bs, -, -, hseq, hcase⟩ := h
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
  · exact ⟨renderNat 0, [], [], by simp [renderWeakBlock], renderNat_isNatTok 0,
      IsSeq.nil, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨renderNat bs.length, renderWeakBounds bs, bs, by simp [renderWeakBlock],
      renderNat_isNatTok _, renderWeakBounds_isSeq hseq, Or.inr ⟨hne, rfl⟩⟩

theorem renderReason_isReason {ts : Toks} {r : ViprReason} (h : IsReason ts r) :
    IsReason (renderReason r) r := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨cnt, body, prs, -, -, hp, rfl⟩
    | ⟨blk, wb, cnt, body, prs, -, hblk, -, hp, rfl⟩
    | ⟨cnt, body, prs, -, -, hp, rfl⟩
    | ⟨t1, t2, t3, t4, i1, l1, i2, l2, -, -, -, -, -, rfl⟩
  · exact Or.inl ⟨by simp [renderReason], rfl⟩
  · exact Or.inr (Or.inl ⟨by simp [renderReason], rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨renderNat prs.length, renderPairs prs, prs,
      by simp [renderReason], renderNat_isNatTok _, renderPairs_isSeq _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨renderWeakBlock wb, wb, renderNat prs.length,
      renderPairs prs, prs, by simp [renderReason], renderWeakBlock_isBlock hblk,
      renderNat_isNatTok _, renderPairs_isSeq _, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨renderNat prs.length, renderPairs prs,
      prs, by simp [renderReason], renderNat_isNatTok _, renderPairs_isSeq _, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨renderNat i1, renderNat l1,
      renderNat i2, renderNat l2, i1, l1, i2, l2, by simp [renderReason],
      renderNat_isNatTok _, renderNat_isNatTok _, renderNat_isNatTok _,
      renderNat_isNatTok _, rfl⟩))))

theorem renderDerCore_isDerCore {ts : Toks} {d : ViprDer} (h : IsDerCore ts d) :
    IsDerCore (renderDerCore d) d := by
  obtain ⟨st, rt, body, rsn, it, -, hs, -, hb, hr, -⟩ := h
  exact ⟨renderChar d.sense, renderRat d.rhs, renderBody d.form d.usesObj,
    renderReason d.reason, renderInt d.idx, by simp [renderDerCore],
    renderChar_isSenseTok hs.2, renderRat_isNumTok _,
    renderBody_isBody (isBody_objForm hb), renderReason_isReason hr,
    renderInt_isIntTok _⟩

theorem renderDers_isDers : ∀ {ts : Toks} {ds : List ViprDer}, IsDers ts ds →
    IsDers (renderDers ds) ds
  | _, _, IsDers.nil => by simpa [renderDers] using IsDers.nil
  | _, _, IsDers.globalFlag hc hg hs => by
      rw [renderDers]
      split
      case isTrue =>
          exact IsDers.globalFlag (renderDerCore_isDerCore hc) hg (renderDers_isDers hs)
      case isFalse hbad => exact absurd hg hbad
  | _, _, IsDers.localFlag hc hg hs => by
      rw [renderDers]
      split
      case isTrue hbad => rw [hg] at hbad; simp at hbad
      case isFalse =>
          exact IsDers.localFlag (renderDerCore_isDerCore hc) hg (renderDers_isDers hs)
  | _, _, IsDers.bare hc hg _ hs => by
      rw [renderDers]
      split
      case isTrue hbad => rw [hg] at hbad; simp at hbad
      case isFalse =>
          exact IsDers.localFlag (renderDerCore_isDerCore hc) hg (renderDers_isDers hs)

/-! ## Sections -/

private theorem renderRat_mem_slash (q : ℚ) : '/' ∈ (renderRat q).toList := by
  rw [renderRat_toList]; simp

private theorem renderRat_ne {q : ℚ} {s : String} (h : '/' ∉ s.toList) :
    renderRat q ≠ s := fun he => h (he ▸ renderRat_mem_slash q)

theorem renderBound_isBoundTok {infinity : String} {b : Option ℚ}
    (h : '/' ∉ infinity.toList) : IsBoundTok infinity (renderBound infinity b) b := by
  cases b with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some q => exact Or.inr ⟨renderRat_ne h, q, renderRat_isNumTok q, rfl⟩

theorem renderRtp_isRtpSection (rtp : ViprRtp) : IsRtpSection (renderRtp rtp) rtp := by
  cases rtp with
  | infeas => exact Or.inl ⟨rfl, rfl⟩
  | range lb ub =>
      exact Or.inr ⟨renderBound "-inf" lb, renderBound "inf" ub, lb, ub, rfl,
        renderBound_isBoundTok (by decide), renderBound_isBoundTok (by decide), rfl⟩

/-- **Everything the renderer writes, the grammar derives as what it came from.** The
hypothesis is what supplies the conditions a bare `Vipr` does not carry: that senses are
`E`/`L`/`G`, that `numCon` and `numSol` agree with the arrays they count, and that a
`lin weak` block listing no bounds is the `global` spelling. -/
theorem renderVipr_isVipr {ts : Toks} {v : Vipr} (h : IsVipr ts v) :
    IsVipr (renderVipr v) v := by
  obtain ⟨sVer, sVar, sInt, sObj, sCon, sRtp, sSol, sDer, -,
    hver, hvar, hint, hobj, hcon, hrtp, hsol, hder⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, hnc, hcseq⟩ := hcon
  obtain ⟨s1, s2, s3, s4, hns, hsseq⟩ := hsol
  obtain ⟨i1, i2, i3, i4, hiseq⟩ := hint
  obtain ⟨d1, d2, d3, d4, hdseq⟩ := hder
  refine ⟨["VER", v.version],
    "VAR" :: renderNat v.varNames.toList.length :: v.varNames.toList,
    "INT" :: renderNat v.intVars.length :: renderNats v.intVars,
    "OBJ" :: v.objSense :: renderNat v.objTerms.length :: renderPairs v.objTerms,
    "CON" :: renderNat v.numCon :: renderNat v.numBounds :: renderCons v.cons.toList,
    renderRtp v.rtp,
    "SOL" :: renderNat v.numSol :: renderSols v.sols.toList,
    "DER" :: renderNat v.ders.toList.length :: renderDers v.ders.toList,
    by simp [renderVipr], rfl,
    ⟨renderNat v.varNames.toList.length, rfl, renderNat_isNatTok _⟩,
    ⟨renderNat v.intVars.length, renderNats v.intVars, rfl, renderNat_isNatTok _,
      renderNats_isSeq _⟩,
    ⟨renderNat v.objTerms.length, renderPairs v.objTerms, rfl, renderNat_isNatTok _,
      renderPairs_isSeq _⟩,
    ⟨renderNat v.numCon, renderNat v.numBounds, renderCons v.cons.toList, rfl,
      renderNat_isNatTok _, renderNat_isNatTok _, hnc, renderCons_isSeq hcseq⟩,
    renderRtp_isRtpSection _,
    ⟨renderNat v.numSol, renderSols v.sols.toList, rfl, renderNat_isNatTok _, hns,
      renderSols_isSeq _⟩,
    ⟨renderNat v.ders.toList.length, renderDers v.ders.toList, rfl,
      renderNat_isNatTok _, renderDers_isDers hdseq⟩⟩

/-! ## Joining tokens

Joining with single spaces and re-tokenizing is the identity, provided each token could
have been produced by the tokenizer in the first place. -/

theorem unwordsChars_isTokenization : ∀ {ts : Toks}, Renderable ts →
    IsTokenization (unwordsChars ts) ts
  | [], _ => by simpa [unwordsChars] using IsTokenization.nil
  | [t], h => by
      obtain ⟨hne, hnw, hpct⟩ := h t (by simp)
      have : IsTokenization (t.toList ++ []) (String.ofList t.toList :: []) :=
        IsTokenization.token hne hnw hpct (by simp [AtTokenEnd]) IsTokenization.nil
      simpa [unwordsChars] using this
  | t :: u :: ts, h => by
      obtain ⟨hne, hnw, hpct⟩ := h t (by simp)
      have ih : IsTokenization (unwordsChars (u :: ts)) (u :: ts) :=
        unwordsChars_isTokenization (fun s hs => h s (by simp [hs]))
      have hsp : IsTokenization (' ' :: unwordsChars (u :: ts)) (u :: ts) :=
        IsTokenization.space (by decide) ih
      have := IsTokenization.token (t := t.toList)
        (rest := ' ' :: unwordsChars (u :: ts)) hne hnw hpct
        (by
          intro c hc
          obtain rfl : ' ' = c := by simpa using hc
          decide)
        hsp
      simpa [unwordsChars] using this

/-! ## Every emitted token is one the tokenizer could produce -/

theorem renderable_nil : Renderable [] := by simp [Renderable]

theorem renderable_cons {t : String} {ts : Toks} (h : RenderableTok t)
    (hs : Renderable ts) : Renderable (t :: ts) := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact h
  · exact hs u hu

theorem renderable_append {a b : Toks} (ha : Renderable a) (hb : Renderable b) :
    Renderable (a ++ b) := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact ha u hu
  · exact hb u hu

private theorem digit_not_ws {c : Char} (h : c.isDigit) : ¬ c.isWhitespace := by
  unfold Char.isDigit at h
  unfold Char.isWhitespace
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (intro hc; rw [hc] at h; exact absurd h (by decide))

private theorem digit_ne_pct {c : Char} (h : c.isDigit) : c ≠ '%' := by
  unfold Char.isDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro hc
  rw [hc] at h
  exact absurd h (by decide)

/-- A nonempty run of digits is a token: digits are neither whitespace nor `%`. -/
theorem renderableTok_of_isDigits {t : String} (h : IsDigits t.toList) :
    RenderableTok t := by
  refine ⟨h.1, fun c hc => digit_not_ws (h.2 c hc), fun hh => ?_⟩
  exact absurd (h.2 '%' (List.mem_of_mem_head? (Option.mem_def.mpr hh))) (by decide)

theorem renderNat_renderableTok (n : Nat) : RenderableTok (renderNat n) :=
  renderableTok_of_isDigits
    (show IsDigits (renderNat n).toList by simpa [renderNat] using natDigits_isDigits n)

private theorem renderableTok_of_chars {t : String} (hne : t.toList ≠ [])
    (h : ∀ c ∈ t.toList, ¬ c.isWhitespace ∧ c ≠ '%') : RenderableTok t := by
  refine ⟨hne, fun c hc => (h c hc).1, fun hh => ?_⟩
  exact (h '%' (List.mem_of_mem_head? (Option.mem_def.mpr hh))).2 rfl

private theorem natDigits_chars {n : Nat} {c : Char} (hc : c ∈ natDigits n) :
    ¬ c.isWhitespace ∧ c ≠ '%' :=
  ⟨digit_not_ws ((natDigits_isDigits n).2 c hc), digit_ne_pct ((natDigits_isDigits n).2 c hc)⟩

theorem renderInt_renderableTok (z : Int) : RenderableTok (renderInt z) := by
  refine renderableTok_of_chars ?_ ?_ <;> rw [renderInt_toList]
  · split <;> simp [(natDigits_isDigits z.natAbs).1]
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · split at hc
      · obtain rfl : c = '-' := by simpa using hc
        exact ⟨by decide, by decide⟩
      · simp at hc
    · exact natDigits_chars hc

theorem renderRat_renderableTok (q : ℚ) : RenderableTok (renderRat q) := by
  refine renderableTok_of_chars ?_ ?_ <;> rw [renderRat_toList]
  · split <;> simp
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · split at hc
      · obtain rfl : c = '-' := by simpa using hc
        exact ⟨by decide, by decide⟩
      · simp at hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact natDigits_chars hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨by decide, by decide⟩
        · exact natDigits_chars (by simpa using hc)

theorem renderNat_renderable (n : Nat) : Renderable [renderNat n] :=
  renderable_cons (renderNat_renderableTok n) renderable_nil

theorem renderChar_renderableTok {c : Char} (h : ¬ c.isWhitespace ∧ c ≠ '%') :
    RenderableTok (renderChar c) :=
  renderableTok_of_chars (by simp [renderChar]) (by
    intro d hd
    obtain rfl : d = c := by simpa [renderChar] using hd
    exact h)

private theorem lit (t : String) (h : RenderableTok t) : RenderableTok t := h

theorem renderPair_renderable (p : Nat × ℚ) : Renderable (renderPair p) :=
  renderable_cons (renderNat_renderableTok _)
    (renderable_cons (renderRat_renderableTok _) renderable_nil)

theorem renderPairs_renderable : ∀ prs : List (Nat × ℚ), Renderable (renderPairs prs)
  | [] => by simpa [renderPairs] using renderable_nil
  | p :: ps => by
      rw [renderPairs]
      exact renderable_append (renderPair_renderable p) (renderPairs_renderable ps)

theorem renderNats_renderable : ∀ ns : List Nat, Renderable (renderNats ns)
  | [] => by simpa [renderNats] using renderable_nil
  | n :: ns => by
      rw [renderNats]
      exact renderable_append (renderNat_renderable n) (renderNats_renderable ns)

theorem renderBody_renderable (form : LinForm) (usesObj : Bool) :
    Renderable (renderBody form usesObj) := by
  unfold renderBody
  split
  · exact renderable_cons (by decide) renderable_nil
  · exact renderable_cons (renderNat_renderableTok _) (renderPairs_renderable _)

/-- A sense or weak-bound kind is a token, because each allowed letter is. -/
private theorem letterTok {c : Char} (h : c = 'E' ∨ c = 'L' ∨ c = 'G') :
    RenderableTok (renderChar c) :=
  renderChar_renderableTok (by rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)

private theorem kindTok {c : Char} (h : c = 'L' ∨ c = 'U') :
    RenderableTok (renderChar c) :=
  renderChar_renderableTok (by rcases h with rfl | rfl <;> exact ⟨by decide, by decide⟩)

theorem renderCon_renderable {ts : Toks} {c : ViprCon} (hg : IsCon ts c)
    (hn : RenderableTok c.name) : Renderable (renderCon c) := by
  obtain ⟨_, _, _, _, hs, _, _⟩ := hg
  exact renderable_cons hn (renderable_cons (letterTok hs.2)
    (renderable_cons (renderRat_renderableTok _) (renderBody_renderable _ _)))

theorem renderCons_renderable : ∀ {ts : Toks} {cs : List ViprCon}, IsSeq IsCon ts cs →
    (∀ c ∈ cs, RenderableTok c.name) → Renderable (renderCons cs)
  | _, _, IsSeq.nil, _ => by simpa [renderCons] using renderable_nil
  | _, c :: cs, IsSeq.cons hc hs, hn => by
      rw [renderCons]
      exact renderable_append (renderCon_renderable hc (hn c (by simp)))
        (renderCons_renderable hs (fun d hd => hn d (by simp [hd])))

theorem renderSol_renderable {s : String × List (Nat × ℚ)} (hn : RenderableTok s.1) :
    Renderable (renderSol s) :=
  renderable_cons hn (renderable_cons (renderNat_renderableTok _)
    (renderPairs_renderable _))

theorem renderSols_renderable : ∀ {ss : List (String × List (Nat × ℚ))},
    (∀ s ∈ ss, RenderableTok s.1) → Renderable (renderSols ss)
  | [], _ => by simpa [renderSols] using renderable_nil
  | s :: ss, hn => by
      rw [renderSols]
      exact renderable_append (renderSol_renderable (hn s (by simp)))
        (renderSols_renderable (fun u hu => hn u (by simp [hu])))

theorem renderWeakBound_renderable {ts : Toks} {b : ViprWeakBound}
    (h : IsWeakBound ts b) : Renderable (renderWeakBound b) := by
  obtain ⟨_, _, _, _, _, _, hk, _, _, _⟩ := h
  exact renderable_cons (kindTok hk) (renderable_cons (renderNat_renderableTok _)
    (renderable_cons (renderNat_renderableTok _)
      (renderable_cons (renderRat_renderableTok _) renderable_nil)))

theorem renderWeakBounds_renderable : ∀ {ts : Toks} {bs : List ViprWeakBound},
    IsSeq IsWeakBound ts bs → Renderable (renderWeakBounds bs)
  | _, _, IsSeq.nil => by simpa [renderWeakBounds] using renderable_nil
  | _, _, IsSeq.cons hb hs => by
      rw [renderWeakBounds]
      exact renderable_append (renderWeakBound_renderable hb)
        (renderWeakBounds_renderable hs)

theorem renderWeakBlock_renderable {ts : Toks} {wb : ViprWeakBounds}
    (h : IsWeakBoundsBlock ts wb) : Renderable (renderWeakBlock wb) := by
  obtain ⟨_, _, bs, _, _, hseq, hcase⟩ := h
  rcases hcase with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
  · exact renderable_cons (by decide) (renderable_cons (renderNat_renderableTok _)
      (renderable_cons (by decide) renderable_nil))
  · rw [renderWeakBlock]
    exact renderable_cons (by decide) (renderable_cons (renderNat_renderableTok _)
      (renderable_append (renderWeakBounds_renderable hseq)
        (renderable_cons (by decide) renderable_nil)))

theorem renderReason_renderable {ts : Toks} {r : ViprReason} (h : IsReason ts r) :
    Renderable (renderReason r) := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, prs, _, _, _, rfl⟩
    | ⟨_, wb, _, _, prs, _, hblk, _, _, rfl⟩ | ⟨_, _, prs, _, _, _, rfl⟩
    | ⟨_, _, _, _, i1, l1, i2, l2, _, _, _, _, _, rfl⟩
  · exact renderable_cons (by decide) (renderable_cons (by decide)
      (renderable_cons (by decide) renderable_nil))
  · exact renderable_cons (by decide) (renderable_cons (by decide)
      (renderable_cons (by decide) renderable_nil))
  · exact renderable_cons (by decide) (renderable_cons (by decide)
      (renderable_cons (renderNat_renderableTok _)
        (renderable_append (renderPairs_renderable _)
          (renderable_cons (by decide) renderable_nil))))
  · exact renderable_cons (by decide) (renderable_cons (by decide)
      (renderable_cons (by decide)
        (renderable_append (renderWeakBlock_renderable hblk)
          (renderable_cons (renderNat_renderableTok _)
            (renderable_append (renderPairs_renderable _)
              (renderable_cons (by decide) renderable_nil))))))
  · exact renderable_cons (by decide) (renderable_cons (by decide)
      (renderable_cons (renderNat_renderableTok _)
        (renderable_append (renderPairs_renderable _)
          (renderable_cons (by decide) renderable_nil))))
  · exact renderable_cons (by decide) (renderable_cons (by decide)
      (renderable_cons (renderNat_renderableTok _)
        (renderable_cons (renderNat_renderableTok _)
          (renderable_cons (renderNat_renderableTok _)
            (renderable_cons (renderNat_renderableTok _)
              (renderable_cons (by decide) renderable_nil))))))

theorem renderDerCore_renderable {ts : Toks} {d : ViprDer} (h : IsDerCore ts d)
    (hn : RenderableTok d.name) : Renderable (renderDerCore d) := by
  obtain ⟨_, _, _, _, _, _, hs, _, _, hr, _⟩ := h
  exact renderable_cons hn (renderable_cons (letterTok hs.2)
    (renderable_cons (renderRat_renderableTok _)
      (renderable_append (renderBody_renderable _ _)
        (renderable_append (renderReason_renderable hr)
          (renderable_cons (renderInt_renderableTok _) renderable_nil)))))

theorem renderDers_renderable : ∀ {ts : Toks} {ds : List ViprDer}, IsDers ts ds →
    (∀ d ∈ ds, RenderableTok d.name) → Renderable (renderDers ds)
  | _, _, IsDers.nil, _ => by simpa [renderDers] using renderable_nil
  | _, d :: ds, IsDers.globalFlag hc _ hs, hn => by
      rw [renderDers]
      refine renderable_append (renderDerCore_renderable hc (hn d (by simp))) ?_
      exact renderable_cons (by split <;> decide)
        (renderDers_renderable hs (fun e he => hn e (by simp [he])))
  | _, d :: ds, IsDers.localFlag hc _ hs, hn => by
      rw [renderDers]
      refine renderable_append (renderDerCore_renderable hc (hn d (by simp))) ?_
      exact renderable_cons (by split <;> decide)
        (renderDers_renderable hs (fun e he => hn e (by simp [he])))
  | _, d :: ds, IsDers.bare hc _ _ hs, hn => by
      rw [renderDers]
      refine renderable_append (renderDerCore_renderable hc (hn d (by simp))) ?_
      exact renderable_cons (by split <;> decide)
        (renderDers_renderable hs (fun e he => hn e (by simp [he])))

theorem renderRtp_renderable (rtp : ViprRtp) : Renderable (renderRtp rtp) := by
  cases rtp with
  | infeas => exact renderable_cons (by decide) (renderable_cons (by decide) renderable_nil)
  | range lb ub =>
      refine renderable_cons (by decide) (renderable_cons (by decide)
        (renderable_cons ?_ (renderable_cons ?_ renderable_nil)))
      · cases lb with
        | none => exact (by decide : RenderableTok "-inf")
        | some q => exact renderRat_renderableTok q
      · cases ub with
        | none => exact (by decide : RenderableTok "inf")
        | some q => exact renderRat_renderableTok q

theorem unwords_isTokenization {ts : Toks} (h : Renderable ts) :
    IsTokenization (unwords ts).toList ts := by
  simpa [unwords] using unwordsChars_isTokenization h

/-- Anything that came out of the tokenizer can go back in. -/
theorem IsTokenization.renderable {cs : List Char} {ts : Toks}
    (h : IsTokenization cs ts) : Renderable ts := fun t ht =>
  ⟨by simpa using h.ne_empty t ht, h.no_ws t ht, h.no_pct t ht⟩

/-! ## The round trip -/

theorem renderVipr_renderable {ts : Toks} {v : Vipr} (hg : IsVipr ts v)
    (hv : Renderable (verbatimToks v)) : Renderable (renderVipr v) := by
  obtain ⟨sVer, sVar, sInt, sObj, sCon, sRtp, sSol, sDer, _,
    _, _, _, _, hcon, _, _, hder⟩ := hg
  obtain ⟨_, _, _, _, _, _, _, hcseq⟩ := hcon
  obtain ⟨_, _, _, _, hdseq⟩ := hder
  have hver : RenderableTok v.version := hv _ (by simp [verbatimToks])
  have hobj : RenderableTok v.objSense := hv _ (by simp [verbatimToks])
  have hvars : Renderable v.varNames.toList := fun t ht =>
    hv t (by simp [verbatimToks, ht])
  have hcn : ∀ c ∈ v.cons.toList, RenderableTok c.name := by
    intro c hc
    refine hv _ ?_
    simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
  have hsn : ∀ s ∈ v.sols.toList, RenderableTok s.1 := by
    intro s hs
    refine hv _ ?_
    simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩))))
  have hdn : ∀ d ∈ v.ders.toList, RenderableTok d.name := by
    intro d hd
    refine hv _ ?_
    simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, hd, rfl⟩))))
  rw [renderVipr]
  refine renderable_append (renderable_cons (by decide) (renderable_cons hver
    renderable_nil)) ?_
  refine renderable_append (renderable_cons (by decide) (renderable_cons
    (renderNat_renderableTok _) hvars)) ?_
  refine renderable_append (renderable_cons (by decide) (renderable_cons
    (renderNat_renderableTok _) (renderNats_renderable _))) ?_
  refine renderable_append (renderable_cons (by decide) (renderable_cons hobj
    (renderable_cons (renderNat_renderableTok _) (renderPairs_renderable _)))) ?_
  refine renderable_append (renderable_cons (by decide) (renderable_cons
    (renderNat_renderableTok _) (renderable_cons (renderNat_renderableTok _)
      (renderCons_renderable hcseq hcn)))) ?_
  refine renderable_append (renderRtp_renderable _) ?_
  exact renderable_append (renderable_cons (by decide) (renderable_cons
    (renderNat_renderableTok _) (renderSols_renderable hsn)))
    (renderable_cons (by decide) (renderable_cons (renderNat_renderableTok _)
      (renderDers_renderable hdseq hdn)))

/-- The rendered text is derived by the grammar as the certificate it came from. -/
theorem render_isViprText {ts : Toks} {v : Vipr} (hg : IsVipr ts v)
    (hv : Renderable (verbatimToks v)) : IsViprText (render v).toList v :=
  ⟨renderVipr v,
    by simpa [render] using unwords_isTokenization (renderVipr_renderable hg hv),
    renderVipr_isVipr hg⟩

/-- **The round trip.** Reading back what the renderer writes gives the certificate it
was given.

The two hypotheses are not slack in the proof; no printer could drop them. A `Vipr`
value carries arbitrary `String` fields, so a variable could be named `""`, `"a b"` or
`"%x"` — none of which survives tokenization — and `IsVipr ts v` is what supplies the
rest of what the grammar demands and the datatype does not, such as a sense being one of
`E`, `L`, `G` and `numCon` agreeing with the array it counts. Both hold of any
certificate that came from a parse. -/
theorem parseVipr_render {ts : Toks} {v : Vipr} (hg : IsVipr ts v) (hvalid : IsValid v)
    (hv : Renderable (verbatimToks v)) : parseVipr (render v) = .ok v :=
  parseVipr_complete (render_isViprText hg hv) hvalid

end LeanVIPR.Impl
