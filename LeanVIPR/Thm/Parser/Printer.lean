module

public import LeanVIPR.Impl.Parser.Printer
public import LeanVIPR.Thm.Parser.Tokens
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The round trip

Reading what the printer writes gives back what was written. Working file; the statement
worth citing is in `LeanVIPR.Thm.Parser`.

The parse direction comes free from `parseVipr_complete`, which is why the round trip
itself is stated in `LeanVIPR.Thm.Parser` alongside the other results rather than here.
What is proved here is everything that feeds it: that `digitsValue` inverts the digit
printer, that each production can be built from the printed fields, and that every token
the printer emits is one the tokenizer could have produced.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Impl LeanVIPR.Semantics

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

theorem printNat_isNatTok (n : Nat) : IsNatTok (printNat n) n := by
  refine ⟨?_, ?_⟩
  · simpa [printNat] using natDigits_isDigits n
  · simp [printNat, natDigits_value]

private theorem printInt_toList (z : Int) :
    (printInt z).toList =
      (if z < 0 then ['-'] else []) ++ natDigits z.natAbs := by
  unfold printInt
  split
  case isTrue h => simp
  case isFalse h => simp [printNat]

theorem printInt_isIntValue (z : Int) : IsIntValue (printInt z).toList z := by
  refine ⟨if z < 0 then ['-'] else [], natDigits z.natAbs,
    ⟨printInt_toList z, ?_, natDigits_isDigits _⟩, ?_⟩
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

theorem printInt_isIntTok (z : Int) : IsIntTok (printInt z) z := printInt_isIntValue z

private theorem printRat_toList (q : ℚ) :
    (printRat q).toList =
      (if q.num < 0 then ['-'] else []) ++
        (natDigits q.num.natAbs ++ '/' :: ([] ++ natDigits q.den)) := by
  simp [printRat, printInt_toList]

theorem printRat_isNumValue (q : ℚ) : IsNumValue (printRat q).toList q := by
  refine Or.inr (Or.inr ⟨if q.num < 0 then ['-'] else [], natDigits q.num.natAbs, [],
    natDigits q.den, ⟨printRat_toList q, ?_, natDigits_isDigits _, Or.inl rfl,
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

theorem printRat_isNumTok (q : ℚ) : IsNumTok (printRat q) q := printRat_isNumValue q

/-! ## Rows

Each level has the same shape: if the value is printable at all — which is what a
hypothesis `IsX ts x` says — then the printer prints it. Carrying the hypothesis is
what supplies the side conditions the grammar imposes but a bare `Vipr` does not, such
as a sense being one of `E`, `L`, `G`. -/

theorem printPair_isPair (p : Nat × ℚ) : IsPair (printPair p) p :=
  ⟨printNat p.1, printRat p.2, rfl, printNat_isNatTok p.1, printRat_isNumTok p.2⟩

theorem printPairs_isSeq : ∀ prs : List (Nat × ℚ), IsSeq IsPair (printPairs prs) prs
  | [] => by simpa [printPairs] using IsSeq.nil
  | p :: ps => by
      rw [printPairs]
      exact IsSeq.cons (printPair_isPair p) (printPairs_isSeq ps)

theorem printNats_isSeq : ∀ ns : List Nat, IsSeq IsNatItem (printNats ns) ns
  | [] => by simpa [printNats] using IsSeq.nil
  | n :: ns => by
      rw [printNats]
      exact IsSeq.cons ⟨printNat n, rfl, printNat_isNatTok n⟩ (printNats_isSeq ns)

theorem printChar_isSenseTok {c : Char} (h : c = 'E' ∨ c = 'L' ∨ c = 'G') :
    IsSenseTok (printChar c) c := ⟨by simp [printChar], h⟩

theorem printBody_isBody {form : LinForm} {usesObj : Bool}
    (h : usesObj = true → form = []) :
    IsBody (printBody form usesObj) form usesObj := by
  unfold printBody
  cases usesObj with
  | true => exact Or.inl ⟨by simp, h rfl, rfl⟩
  | false =>
      refine Or.inr ⟨printNat form.length,
        printPairs (form.map (fun t => (t.idx, t.coeff))),
        form.map (fun t => (t.idx, t.coeff)), by simp, ?_, printPairs_isSeq _, ?_, rfl⟩
      · simpa using printNat_isNatTok form.length
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

theorem printCon_isCon {ts : Toks} {c : ViprCon} (h : IsCon ts c) :
    IsCon (printCon c) c := by
  obtain ⟨st, rt, body, -, hs, -, hb⟩ := h
  exact ⟨printChar c.sense, printRat c.rhs, printBody c.form c.usesObj, rfl,
    printChar_isSenseTok hs.2, printRat_isNumTok c.rhs, printBody_isBody
      (isBody_objForm hb)⟩

theorem printCons_isSeq : ∀ {ts : Toks} {cs : List ViprCon}, IsSeq IsCon ts cs →
    IsSeq IsCon (printCons cs) cs
  | _, _, IsSeq.nil => by simpa [printCons] using IsSeq.nil
  | _, _, IsSeq.cons hc hs => by
      rw [printCons]
      exact IsSeq.cons (printCon_isCon hc) (printCons_isSeq hs)

theorem printSol_isSol (s : String × List (Nat × ℚ)) : IsSol (printSol s) s :=
  ⟨printNat s.2.length, printPairs s.2, rfl, printNat_isNatTok s.2.length,
    printPairs_isSeq s.2⟩

theorem printSols_isSeq : ∀ ss : List (String × List (Nat × ℚ)),
    IsSeq IsSol (printSols ss) ss
  | [] => by simpa [printSols] using IsSeq.nil
  | s :: ss => by
      rw [printSols]
      exact IsSeq.cons (printSol_isSol s) (printSols_isSeq ss)

theorem printWeakBound_isWeakBound {ts : Toks} {b : ViprWeakBound}
    (h : IsWeakBound ts b) : IsWeakBound (printWeakBound b) b := by
  obtain ⟨kt, vt, rt, nt, -, -, hk, -, -, -⟩ := h
  exact ⟨printChar b.kind, printNat b.varIdx, printNat b.rowIdx, printRat b.value,
    rfl, by simp [printChar], hk, printNat_isNatTok _, printNat_isNatTok _,
    printRat_isNumTok _⟩

theorem printWeakBounds_isSeq : ∀ {ts : Toks} {bs : List ViprWeakBound},
    IsSeq IsWeakBound ts bs → IsSeq IsWeakBound (printWeakBounds bs) bs
  | _, _, IsSeq.nil => by simpa [printWeakBounds] using IsSeq.nil
  | _, _, IsSeq.cons hb hs => by
      rw [printWeakBounds]
      exact IsSeq.cons (printWeakBound_isWeakBound hb) (printWeakBounds_isSeq hs)

/-! ## Reasons and derivations -/

theorem printWeakBlock_isBlock {ts : Toks} {wb : ViprWeakBounds}
    (h : IsWeakBoundsBlock ts wb) : IsWeakBoundsBlock (printWeakBlock wb) wb := by
  obtain ⟨cnt, body, bs, -, -, hseq, hcase⟩ := h
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
  · exact ⟨printNat 0, [], [], by simp [printWeakBlock], printNat_isNatTok 0,
      IsSeq.nil, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨printNat bs.length, printWeakBounds bs, bs, by simp [printWeakBlock],
      printNat_isNatTok _, printWeakBounds_isSeq hseq, Or.inr ⟨hne, rfl⟩⟩

theorem printReason_isReason {ts : Toks} {r : ViprReason} (h : IsReason ts r) :
    IsReason (printReason r) r := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨cnt, body, prs, -, -, hp, rfl⟩
    | ⟨blk, wb, cnt, body, prs, -, hblk, -, hp, rfl⟩
    | ⟨cnt, body, prs, -, -, hp, rfl⟩
    | ⟨t1, t2, t3, t4, i1, l1, i2, l2, -, -, -, -, -, rfl⟩
  · exact Or.inl ⟨by simp [printReason], rfl⟩
  · exact Or.inr (Or.inl ⟨by simp [printReason], rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨printNat prs.length, printPairs prs, prs,
      by simp [printReason], printNat_isNatTok _, printPairs_isSeq _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨printWeakBlock wb, wb, printNat prs.length,
      printPairs prs, prs, by simp [printReason], printWeakBlock_isBlock hblk,
      printNat_isNatTok _, printPairs_isSeq _, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨printNat prs.length, printPairs prs,
      prs, by simp [printReason], printNat_isNatTok _, printPairs_isSeq _, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨printNat i1, printNat l1,
      printNat i2, printNat l2, i1, l1, i2, l2, by simp [printReason],
      printNat_isNatTok _, printNat_isNatTok _, printNat_isNatTok _,
      printNat_isNatTok _, rfl⟩))))

theorem printDerCore_isDerCore {ts : Toks} {d : ViprDer} (h : IsDerCore ts d) :
    IsDerCore (printDerCore d) d := by
  obtain ⟨st, rt, body, rsn, it, -, hs, -, hb, hr, -⟩ := h
  exact ⟨printChar d.sense, printRat d.rhs, printBody d.form d.usesObj,
    printReason d.reason, printInt d.idx, by simp [printDerCore],
    printChar_isSenseTok hs.2, printRat_isNumTok _,
    printBody_isBody (isBody_objForm hb), printReason_isReason hr,
    printInt_isIntTok _⟩

private theorem isDerCore_head? {core : Toks} {d : ViprDer} (h : IsDerCore core d)
    (rest : Toks) : (core ++ rest).head? = some d.name := by
  obtain ⟨st, rt, body, rsn, it, he, -⟩ := h
  rw [he]; simp

private theorem isDers_head? : ∀ {ts : Toks} {d : ViprDer} {ds : List ViprDer},
    IsDers ts (d :: ds) → ts.head? = some d.name
  | _, _, _, IsDers.globalFlag hc _ _ => isDerCore_head? hc _
  | _, _, _, IsDers.localFlag hc _ _ => isDerCore_head? hc _
  | _, _, _, IsDers.bare hc _ _ _ => isDerCore_head? hc _

private theorem printDers_head? : ∀ {ts : Toks} {ds : List ViprDer}, IsDers ts ds →
    (printDers ds).head? = ts.head?
  | _, _, IsDers.nil => by simp [printDers]
  | _, _, IsDers.globalFlag hc hg _ => by
      rw [printDers, hg, isDerCore_head? (printDerCore_isDerCore hc),
        isDerCore_head? hc]
  | _, _, IsDers.localFlag hc hg _ => by
      rw [printDers, hg, isDerCore_head? (printDerCore_isDerCore hc),
        isDerCore_head? hc]
  | _, _, IsDers.bare hc hg _ _ => by
      rw [printDers, hg, isDerCore_head? (printDerCore_isDerCore hc),
        isDerCore_head? hc]

theorem printDers_isDers : ∀ {ts : Toks} {ds : List ViprDer}, IsDers ts ds →
    IsDers (printDers ds) ds
  | _, _, IsDers.nil => by simpa [printDers] using IsDers.nil
  | _, _, IsDers.globalFlag hc hg hs => by
      rw [printDers, hg]
      exact IsDers.globalFlag (printDerCore_isDerCore hc) hg (printDers_isDers hs)
  | _, _, IsDers.localFlag hc hg hs => by
      rw [printDers, hg]
      exact IsDers.localFlag (printDerCore_isDerCore hc) hg (printDers_isDers hs)
  | _, _, IsDers.bare hc hg hne hs => by
      rw [printDers, hg]
      refine IsDers.bare (printDerCore_isDerCore hc) hg ?_ (printDers_isDers hs)
      rw [printDers_head? hs]
      exact hne

/-! ## Every verbatim string of a certificate is a token of its stream

`Printable (verbatimToks v)` is a hypothesis of the round trip, and for a certificate
that was read from text it is not an assumption at all: each string the printer copies
rather than generates was a token, and a tokenization's tokens are non-empty,
whitespace-free, and never start with `%` -- which is exactly `PrintableTok`. These
lemmas make that argument, so `toString_roundtrip_of_text` can state the round trip for
anything the parser accepts, with no side conditions. -/

/-- In a sequence, every element whose rendering begins with `f x` contributes `f x` to
the whole. -/
private theorem isSeq_mem_head {α : Type} {R : Toks → α → Prop} {f : α → String}
    (hhead : ∀ (seg : Toks) (x : α), R seg x → seg.head? = some (f x))
    {ts : Toks} {xs : List α} (h : IsSeq R ts xs) : ∀ x ∈ xs, f x ∈ ts := by
  induction h with
  | nil => simp
  | @cons seg rest y ys hR hs ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hh := hhead seg x hR
        cases seg with
        | nil => simp at hh
        | cons u ul =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            simp
      · exact List.mem_append_right _ (ih x hx)

private theorem isCon_head {seg : Toks} {c : ViprCon} (h : IsCon seg c) :
    seg.head? = some c.name := by
  obtain ⟨st, rt, body, he, -⟩ := h; rw [he]; simp

private theorem isSol_head {seg : Toks} {s : String × List (Nat × ℚ)} (h : IsSol seg s) :
    seg.head? = some s.1 := by
  obtain ⟨cnt, body, he, -⟩ := h; rw [he]; simp

private theorem isDers_mem_name : ∀ {ts : Toks} {ds : List ViprDer}, IsDers ts ds →
    ∀ d ∈ ds, d.name ∈ ts
  | _, _, IsDers.nil, _, hx => by simp at hx
  | _, _, IsDers.globalFlag hc _ hs, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_of_mem_head? (isDerCore_head? hc _)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (isDers_mem_name hs x hx))
  | _, _, IsDers.localFlag hc _ hs, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_of_mem_head? (isDerCore_head? hc _)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (isDers_mem_name hs x hx))
  | _, _, IsDers.bare hc _ _ hs, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_of_mem_head? (isDerCore_head? hc _)
      · exact List.mem_append_right _ (isDers_mem_name hs x hx)

/-- Every string a certificate carries verbatim occurs as a token of any stream that
derives it. -/
theorem verbatimToks_subset {ts : Toks} {v : Vipr} (h : IsVipr ts v) :
    ∀ t ∈ verbatimToks v, t ∈ ts := by
  obtain ⟨sVer, sVar, sInt, sObj, sCon, sRtp, sSol, sDer, rfl,
    hver, hvar, -, hobj, hcon, -, hsol, hder⟩ := h
  obtain ⟨cntV, hvarE, -⟩ := hvar
  obtain ⟨cntO, bodyO, hobjE, -⟩ := hobj
  obtain ⟨cntC, bndC, bodyC, hconE, -, -, -, hseqC⟩ := hcon
  obtain ⟨cntS, bodyS, hsolE, -, -, hseqS⟩ := hsol
  obtain ⟨cntD, bodyD, hderE, -, hders⟩ := hder
  intro t ht
  simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map] at ht
  simp only [List.mem_append]
  rcases ht with rfl | rfl | hv | hc | hs | hd
  · have : v.version ∈ sVer := by rw [hver]; simp
    tauto
  · have : v.objSense ∈ sObj := by rw [hobjE]; simp
    tauto
  · have : t ∈ sVar := by rw [hvarE]; simp [hv]
    tauto
  · obtain ⟨c, hcm, rfl⟩ := hc
    have : c.name ∈ sCon := by
      rw [hconE]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (isSeq_mem_head (f := ViprCon.name) (fun _ _ h => isCon_head h) hseqC c hcm)))
    tauto
  · obtain ⟨sl, hsm, rfl⟩ := hs
    have : sl.1 ∈ sSol := by
      rw [hsolE]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (isSeq_mem_head (f := Prod.fst) (fun _ _ h => isSol_head h) hseqS sl hsm))
    tauto
  · obtain ⟨d, hdm, rfl⟩ := hd
    have : d.name ∈ sDer := by
      rw [hderE]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (isDers_mem_name hders d hdm))
    tauto

/-- A tokenization's tokens are exactly what the printer may copy. -/
theorem printable_of_isTokenization {cs : List Char} {ts : Toks}
    (h : IsTokenization cs ts) : Printable ts := by
  intro t ht
  exact ⟨by simpa using h.ne_empty t ht, h.no_ws t ht, h.no_pct t ht⟩

/-! ## Sections -/

private theorem printRat_mem_slash (q : ℚ) : '/' ∈ (printRat q).toList := by
  rw [printRat_toList]; simp

private theorem printRat_ne {q : ℚ} {s : String} (h : '/' ∉ s.toList) :
    printRat q ≠ s := fun he => h (he ▸ printRat_mem_slash q)

theorem printBound_isBoundTok {infinity : String} {b : Option ℚ}
    (h : '/' ∉ infinity.toList) : IsBoundTok infinity (printBound infinity b) b := by
  cases b with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some q => exact Or.inr ⟨printRat_ne h, q, printRat_isNumTok q, rfl⟩

theorem printRtp_isRtpSection (rtp : ViprRtp) : IsRtpSection (printRtp rtp) rtp := by
  cases rtp with
  | infeas => exact Or.inl ⟨rfl, rfl⟩
  | range lb ub =>
      exact Or.inr ⟨printBound "-inf" lb, printBound "inf" ub, lb, ub, rfl,
        printBound_isBoundTok (by decide), printBound_isBoundTok (by decide), rfl⟩

/-- **Everything the printer writes, the grammar derives as what it came from.** The
hypothesis is what supplies the conditions a bare `Vipr` does not carry: that senses are
`E`/`L`/`G`, that `numCon` and `numSol` agree with the arrays they count, and that a
`lin weak` block listing no bounds is the `global` spelling. -/
theorem printVipr_isVipr {ts : Toks} {v : Vipr} (h : IsVipr ts v) :
    IsVipr (printVipr v) v := by
  obtain ⟨sVer, sVar, sInt, sObj, sCon, sRtp, sSol, sDer, -,
    hver, hvar, hint, hobj, hcon, hrtp, hsol, hder⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, hnc, hcseq⟩ := hcon
  obtain ⟨s1, s2, s3, s4, hns, hsseq⟩ := hsol
  obtain ⟨i1, i2, i3, i4, hiseq⟩ := hint
  obtain ⟨d1, d2, d3, d4, hdseq⟩ := hder
  refine ⟨["VER", v.version],
    "VAR" :: printNat v.varNames.toList.length :: v.varNames.toList,
    "INT" :: printNat v.intVars.length :: printNats v.intVars,
    "OBJ" :: v.objSense :: printNat v.objTerms.length :: printPairs v.objTerms,
    "CON" :: printNat v.numCon :: printNat v.numBounds :: printCons v.cons.toList,
    printRtp v.rtp,
    "SOL" :: printNat v.numSol :: printSols v.sols.toList,
    "DER" :: printNat v.ders.toList.length :: printDers v.ders.toList,
    by simp [printVipr], rfl,
    ⟨printNat v.varNames.toList.length, rfl, printNat_isNatTok _⟩,
    ⟨printNat v.intVars.length, printNats v.intVars, rfl, printNat_isNatTok _,
      printNats_isSeq _⟩,
    ⟨printNat v.objTerms.length, printPairs v.objTerms, rfl, printNat_isNatTok _,
      printPairs_isSeq _⟩,
    ⟨printNat v.numCon, printNat v.numBounds, printCons v.cons.toList, rfl,
      printNat_isNatTok _, printNat_isNatTok _, hnc, printCons_isSeq hcseq⟩,
    printRtp_isRtpSection _,
    ⟨printNat v.numSol, printSols v.sols.toList, rfl, printNat_isNatTok _, hns,
      printSols_isSeq _⟩,
    ⟨printNat v.ders.toList.length, printDers v.ders.toList, rfl,
      printNat_isNatTok _, printDers_isDers hdseq⟩⟩

/-! ## Joining tokens

Joining with single spaces and re-tokenizing is the identity, provided each token could
have been produced by the tokenizer in the first place. -/

theorem unwordsChars_isTokenization : ∀ {ts : Toks}, Printable ts →
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

theorem printable_nil : Printable [] := by simp [Printable]

theorem printable_cons {t : String} {ts : Toks} (h : PrintableTok t)
    (hs : Printable ts) : Printable (t :: ts) := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact h
  · exact hs u hu

theorem printable_append {a b : Toks} (ha : Printable a) (hb : Printable b) :
    Printable (a ++ b) := by
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
theorem printableTok_of_isDigits {t : String} (h : IsDigits t.toList) :
    PrintableTok t := by
  refine ⟨h.1, fun c hc => digit_not_ws (h.2 c hc), fun hh => ?_⟩
  exact absurd (h.2 '%' (List.mem_of_mem_head? (Option.mem_def.mpr hh))) (by decide)

theorem printNat_printableTok (n : Nat) : PrintableTok (printNat n) :=
  printableTok_of_isDigits
    (show IsDigits (printNat n).toList by simpa [printNat] using natDigits_isDigits n)

private theorem printableTok_of_chars {t : String} (hne : t.toList ≠ [])
    (h : ∀ c ∈ t.toList, ¬ c.isWhitespace ∧ c ≠ '%') : PrintableTok t := by
  refine ⟨hne, fun c hc => (h c hc).1, fun hh => ?_⟩
  exact (h '%' (List.mem_of_mem_head? (Option.mem_def.mpr hh))).2 rfl

private theorem natDigits_chars {n : Nat} {c : Char} (hc : c ∈ natDigits n) :
    ¬ c.isWhitespace ∧ c ≠ '%' :=
  ⟨digit_not_ws ((natDigits_isDigits n).2 c hc), digit_ne_pct ((natDigits_isDigits n).2 c hc)⟩

theorem printInt_printableTok (z : Int) : PrintableTok (printInt z) := by
  refine printableTok_of_chars ?_ ?_ <;> rw [printInt_toList]
  · split <;> simp [(natDigits_isDigits z.natAbs).1]
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · split at hc
      · obtain rfl : c = '-' := by simpa using hc
        exact ⟨by decide, by decide⟩
      · simp at hc
    · exact natDigits_chars hc

theorem printRat_printableTok (q : ℚ) : PrintableTok (printRat q) := by
  refine printableTok_of_chars ?_ ?_ <;> rw [printRat_toList]
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

theorem printNat_printable (n : Nat) : Printable [printNat n] :=
  printable_cons (printNat_printableTok n) printable_nil

theorem printChar_printableTok {c : Char} (h : ¬ c.isWhitespace ∧ c ≠ '%') :
    PrintableTok (printChar c) :=
  printableTok_of_chars (by simp [printChar]) (by
    intro d hd
    obtain rfl : d = c := by simpa [printChar] using hd
    exact h)

private theorem lit (t : String) (h : PrintableTok t) : PrintableTok t := h

theorem printPair_printable (p : Nat × ℚ) : Printable (printPair p) :=
  printable_cons (printNat_printableTok _)
    (printable_cons (printRat_printableTok _) printable_nil)

theorem printPairs_printable : ∀ prs : List (Nat × ℚ), Printable (printPairs prs)
  | [] => by simpa [printPairs] using printable_nil
  | p :: ps => by
      rw [printPairs]
      exact printable_append (printPair_printable p) (printPairs_printable ps)

theorem printNats_printable : ∀ ns : List Nat, Printable (printNats ns)
  | [] => by simpa [printNats] using printable_nil
  | n :: ns => by
      rw [printNats]
      exact printable_append (printNat_printable n) (printNats_printable ns)

theorem printBody_printable (form : LinForm) (usesObj : Bool) :
    Printable (printBody form usesObj) := by
  unfold printBody
  split
  · exact printable_cons (by decide) printable_nil
  · exact printable_cons (printNat_printableTok _) (printPairs_printable _)

/-- A sense or weak-bound kind is a token, because each allowed letter is. -/
private theorem letterTok {c : Char} (h : c = 'E' ∨ c = 'L' ∨ c = 'G') :
    PrintableTok (printChar c) :=
  printChar_printableTok (by rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)

private theorem kindTok {c : Char} (h : c = 'L' ∨ c = 'U') :
    PrintableTok (printChar c) :=
  printChar_printableTok (by rcases h with rfl | rfl <;> exact ⟨by decide, by decide⟩)

theorem printCon_printable {ts : Toks} {c : ViprCon} (hg : IsCon ts c)
    (hn : PrintableTok c.name) : Printable (printCon c) := by
  obtain ⟨_, _, _, _, hs, _, _⟩ := hg
  exact printable_cons hn (printable_cons (letterTok hs.2)
    (printable_cons (printRat_printableTok _) (printBody_printable _ _)))

theorem printCons_printable : ∀ {ts : Toks} {cs : List ViprCon}, IsSeq IsCon ts cs →
    (∀ c ∈ cs, PrintableTok c.name) → Printable (printCons cs)
  | _, _, IsSeq.nil, _ => by simpa [printCons] using printable_nil
  | _, c :: cs, IsSeq.cons hc hs, hn => by
      rw [printCons]
      exact printable_append (printCon_printable hc (hn c (by simp)))
        (printCons_printable hs (fun d hd => hn d (by simp [hd])))

theorem printSol_printable {s : String × List (Nat × ℚ)} (hn : PrintableTok s.1) :
    Printable (printSol s) :=
  printable_cons hn (printable_cons (printNat_printableTok _)
    (printPairs_printable _))

theorem printSols_printable : ∀ {ss : List (String × List (Nat × ℚ))},
    (∀ s ∈ ss, PrintableTok s.1) → Printable (printSols ss)
  | [], _ => by simpa [printSols] using printable_nil
  | s :: ss, hn => by
      rw [printSols]
      exact printable_append (printSol_printable (hn s (by simp)))
        (printSols_printable (fun u hu => hn u (by simp [hu])))

theorem printWeakBound_printable {ts : Toks} {b : ViprWeakBound}
    (h : IsWeakBound ts b) : Printable (printWeakBound b) := by
  obtain ⟨_, _, _, _, _, _, hk, _, _, _⟩ := h
  exact printable_cons (kindTok hk) (printable_cons (printNat_printableTok _)
    (printable_cons (printNat_printableTok _)
      (printable_cons (printRat_printableTok _) printable_nil)))

theorem printWeakBounds_printable : ∀ {ts : Toks} {bs : List ViprWeakBound},
    IsSeq IsWeakBound ts bs → Printable (printWeakBounds bs)
  | _, _, IsSeq.nil => by simpa [printWeakBounds] using printable_nil
  | _, _, IsSeq.cons hb hs => by
      rw [printWeakBounds]
      exact printable_append (printWeakBound_printable hb)
        (printWeakBounds_printable hs)

theorem printWeakBlock_printable {ts : Toks} {wb : ViprWeakBounds}
    (h : IsWeakBoundsBlock ts wb) : Printable (printWeakBlock wb) := by
  obtain ⟨_, _, bs, _, _, hseq, hcase⟩ := h
  rcases hcase with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
  · exact printable_cons (by decide) (printable_cons (printNat_printableTok _)
      (printable_cons (by decide) printable_nil))
  · rw [printWeakBlock]
    exact printable_cons (by decide) (printable_cons (printNat_printableTok _)
      (printable_append (printWeakBounds_printable hseq)
        (printable_cons (by decide) printable_nil)))

theorem printReason_printable {ts : Toks} {r : ViprReason} (h : IsReason ts r) :
    Printable (printReason r) := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, prs, _, _, _, rfl⟩
    | ⟨_, wb, _, _, prs, _, hblk, _, _, rfl⟩ | ⟨_, _, prs, _, _, _, rfl⟩
    | ⟨_, _, _, _, i1, l1, i2, l2, _, _, _, _, _, rfl⟩
  · exact printable_cons (by decide) (printable_cons (by decide)
      (printable_cons (by decide) printable_nil))
  · exact printable_cons (by decide) (printable_cons (by decide)
      (printable_cons (by decide) printable_nil))
  · exact printable_cons (by decide) (printable_cons (by decide)
      (printable_cons (printNat_printableTok _)
        (printable_append (printPairs_printable _)
          (printable_cons (by decide) printable_nil))))
  · exact printable_cons (by decide) (printable_cons (by decide)
      (printable_cons (by decide)
        (printable_append (printWeakBlock_printable hblk)
          (printable_cons (printNat_printableTok _)
            (printable_append (printPairs_printable _)
              (printable_cons (by decide) printable_nil))))))
  · exact printable_cons (by decide) (printable_cons (by decide)
      (printable_cons (printNat_printableTok _)
        (printable_append (printPairs_printable _)
          (printable_cons (by decide) printable_nil))))
  · exact printable_cons (by decide) (printable_cons (by decide)
      (printable_cons (printNat_printableTok _)
        (printable_cons (printNat_printableTok _)
          (printable_cons (printNat_printableTok _)
            (printable_cons (printNat_printableTok _)
              (printable_cons (by decide) printable_nil))))))

theorem printDerCore_printable {ts : Toks} {d : ViprDer} (h : IsDerCore ts d)
    (hn : PrintableTok d.name) : Printable (printDerCore d) := by
  obtain ⟨_, _, _, _, _, _, hs, _, _, hr, _⟩ := h
  exact printable_cons hn (printable_cons (letterTok hs.2)
    (printable_cons (printRat_printableTok _)
      (printable_append (printBody_printable _ _)
        (printable_append (printReason_printable hr)
          (printable_cons (printInt_printableTok _) printable_nil)))))

theorem printDers_printable : ∀ {ts : Toks} {ds : List ViprDer}, IsDers ts ds →
    (∀ d ∈ ds, PrintableTok d.name) → Printable (printDers ds)
  | _, _, IsDers.nil, _ => by simpa [printDers] using printable_nil
  | _, d :: ds, IsDers.globalFlag hc hg hs, hn => by
      rw [printDers, hg]
      refine printable_append (printDerCore_printable hc (hn d (by simp))) ?_
      exact printable_cons (by decide)
        (printDers_printable hs (fun e he => hn e (by simp [he])))
  | _, d :: ds, IsDers.localFlag hc hg hs, hn => by
      rw [printDers, hg]
      refine printable_append (printDerCore_printable hc (hn d (by simp))) ?_
      exact printable_cons (by decide)
        (printDers_printable hs (fun e he => hn e (by simp [he])))
  | _, d :: ds, IsDers.bare hc hg _ hs, hn => by
      rw [printDers, hg]
      exact printable_append (printDerCore_printable hc (hn d (by simp)))
        (printDers_printable hs (fun e he => hn e (by simp [he])))

theorem printRtp_printable (rtp : ViprRtp) : Printable (printRtp rtp) := by
  cases rtp with
  | infeas => exact printable_cons (by decide) (printable_cons (by decide) printable_nil)
  | range lb ub =>
      refine printable_cons (by decide) (printable_cons (by decide)
        (printable_cons ?_ (printable_cons ?_ printable_nil)))
      · cases lb with
        | none => exact (by decide : PrintableTok "-inf")
        | some q => exact printRat_printableTok q
      · cases ub with
        | none => exact (by decide : PrintableTok "inf")
        | some q => exact printRat_printableTok q

theorem unwords_isTokenization {ts : Toks} (h : Printable ts) :
    IsTokenization (unwords ts).toList ts := by
  simpa [unwords] using unwordsChars_isTokenization h

/-- Anything that came out of the tokenizer can go back in. -/
theorem IsTokenization.printable {cs : List Char} {ts : Toks}
    (h : IsTokenization cs ts) : Printable ts := fun t ht =>
  ⟨by simpa using h.ne_empty t ht, h.no_ws t ht, h.no_pct t ht⟩

/-! ## The round trip -/

theorem printVipr_printable {ts : Toks} {v : Vipr} (hg : IsVipr ts v)
    (hv : Printable (verbatimToks v)) : Printable (printVipr v) := by
  obtain ⟨sVer, sVar, sInt, sObj, sCon, sRtp, sSol, sDer, _,
    _, _, _, _, hcon, _, _, hder⟩ := hg
  obtain ⟨_, _, _, _, _, _, _, hcseq⟩ := hcon
  obtain ⟨_, _, _, _, hdseq⟩ := hder
  have hver : PrintableTok v.version := hv _ (by simp [verbatimToks])
  have hobj : PrintableTok v.objSense := hv _ (by simp [verbatimToks])
  have hvars : Printable v.varNames.toList := fun t ht =>
    hv t (by simp [verbatimToks, ht])
  have hcn : ∀ c ∈ v.cons.toList, PrintableTok c.name := by
    intro c hc
    refine hv _ ?_
    simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
  have hsn : ∀ s ∈ v.sols.toList, PrintableTok s.1 := by
    intro s hs
    refine hv _ ?_
    simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩))))
  have hdn : ∀ d ∈ v.ders.toList, PrintableTok d.name := by
    intro d hd
    refine hv _ ?_
    simp only [verbatimToks, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, hd, rfl⟩))))
  rw [printVipr]
  refine printable_append (printable_cons (by decide) (printable_cons hver
    printable_nil)) ?_
  refine printable_append (printable_cons (by decide) (printable_cons
    (printNat_printableTok _) hvars)) ?_
  refine printable_append (printable_cons (by decide) (printable_cons
    (printNat_printableTok _) (printNats_printable _))) ?_
  refine printable_append (printable_cons (by decide) (printable_cons hobj
    (printable_cons (printNat_printableTok _) (printPairs_printable _)))) ?_
  refine printable_append (printable_cons (by decide) (printable_cons
    (printNat_printableTok _) (printable_cons (printNat_printableTok _)
      (printCons_printable hcseq hcn)))) ?_
  refine printable_append (printRtp_printable _) ?_
  exact printable_append (printable_cons (by decide) (printable_cons
    (printNat_printableTok _) (printSols_printable hsn)))
    (printable_cons (by decide) (printable_cons (printNat_printableTok _)
      (printDers_printable hdseq hdn)))

/-- The printed text is derived by the grammar as the certificate it came from. -/
theorem print_isViprText {ts : Toks} {v : Vipr} (hg : IsVipr ts v)
    (hv : Printable (verbatimToks v)) : IsViprText (print v).toList v :=
  ⟨printVipr v,
    by simpa [print] using unwords_isTokenization (printVipr_printable hg hv),
    printVipr_isVipr hg⟩

end LeanVIPR.Parser
