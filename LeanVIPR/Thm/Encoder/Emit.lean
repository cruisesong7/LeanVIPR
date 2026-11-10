module

public import LeanVIPR.Spec.Syntax.Mps
public import LeanVIPR.Impl.Encoder.Mps
public import LeanVIPR.Thm.Parser.Printer

@[expose] public section

/-!
# The emitted text is the problem it came from

Towards `mpsRoundTrip : EncodableNames m objRow → IsMpsText (encodeMps m).toList m`.

## Why this is not soundness-critical

`pipeline_infeasible` does not mention `encodeMps`. If the emitter writes the wrong file,
SCIP solves a different problem, returns a certificate about *that* problem, and
`agreesWith` rejects it. So what this buys is **honesty and completeness**: that the file
we hand the solver is the problem our theorem talks about, and that the pipeline does not
fail for reasons of our own making. Worth having, and worth not confusing with soundness.

## Tokenization, generalized away from single spaces

`LeanVIPR.Thm.Parser.Printer.unwordsChars_isTokenization` proves that joining tokens with
single spaces re-tokenizes to the same tokens. That is not quite what is needed here:
`encodeMps` indents its data lines and separates them with `'\n'`, so the glue between
tokens varies.

The two lemmas below are the generalization, and they are small because `IsTokenization`
was already stated in the right way. `space` consumes any character satisfying
`Char.isWhitespace`, and `'\n'` and `' '` both do, so arbitrary whitespace glue costs one
induction rather than a new tokenizer. `wsPrefix` absorbs leading whitespace — which is
what makes indentation free — and `consTok` is `IsTokenization.token` with the
`String.ofList` round trip discharged, so emitted lines can be assembled one token at a
time.
-/

namespace LeanVIPR.Mps

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Parser LeanVIPR.Impl

/-! ## Whitespace glue -/

/-- Every character of `w` is whitespace. -/
def AllWhitespace (w : List Char) : Prop := ∀ c ∈ w, c.isWhitespace

instance (w : List Char) : Decidable (AllWhitespace w) := by
  unfold AllWhitespace; infer_instance

theorem allWhitespace_nil : AllWhitespace [] := by simp [AllWhitespace]

theorem allWhitespace_cons {c : Char} {w : List Char} (hc : c.isWhitespace)
    (hw : AllWhitespace w) : AllWhitespace (c :: w) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact hw d hd

/-! ## Every indent the emitter writes is whitespace

Nothing to prove per section: `Encoder.Indent` has three constructors and all three render
to whitespace, so the obligation is discharged once, by cases. Before `Indent` was a type
this needed a lemma for each section of the emitter, each of which could have been got
wrong; now a new section cannot introduce a bad indent in the first place. -/

/-- Every line's indentation is whitespace. True of any `List Line` at all, since
`Encoder.Indent` only has whitespace constructors — see `indentsWhitespace`. -/
def IndentsWhitespace (ls : List Encoder.Line) : Prop :=
  ∀ l ∈ ls, AllWhitespace l.1.toString.toList

theorem allWhitespace_indent (i : Encoder.Indent) :
    AllWhitespace i.toString.toList := by
  cases i <;> decide

/-- Consequently every emitted line satisfies the invariant, whatever the problem. -/
theorem indentsWhitespace (ls : List Encoder.Line) : IndentsWhitespace ls :=
  fun l _ => allWhitespace_indent l.1

/-- Leading whitespace contributes no tokens. This is what makes a data line's
indentation invisible to the grammar. -/
theorem isTokenization_wsPrefix : ∀ {w : List Char}, AllWhitespace w →
    ∀ {cs : List Char} {ts : Toks}, IsTokenization cs ts →
    IsTokenization (w ++ cs) ts
  | [], _, _, _, h => by simpa using h
  | c :: w, hw, _, _, h => by
      refine IsTokenization.space (hw c (by simp)) ?_
      exact isTokenization_wsPrefix (fun d hd => hw d (by simp [hd])) h

/-- One token, then whitespace, then the rest: the step a line is built from.

The `AtTokenEnd` side condition is discharged from the glue being whitespace, which is
exactly why the glue has to be nonempty — two tokens run together would be read as one. -/
theorem isTokenization_consTok {t : String} (ht : PrintableTok t)
    {w : List Char} (hwne : w ≠ []) (hw : AllWhitespace w)
    {cs : List Char} {ts : Toks} (h : IsTokenization cs ts) :
    IsTokenization (t.toList ++ w ++ cs) (t :: ts) := by
  obtain ⟨hne, hnw, hpct⟩ := ht
  have hrest : IsTokenization (w ++ cs) ts := isTokenization_wsPrefix hw h
  have hend : AtTokenEnd (w ++ cs) := by
    cases w with
    | nil => exact absurd rfl hwne
    | cons d w' =>
        intro c hc
        obtain rfl : d = c := by simpa using hc
        exact hw d (by simp)
  have := IsTokenization.token (t := t.toList) (rest := w ++ cs) hne hnw hpct hend hrest
  simpa [List.append_assoc] using this

/-! ## A space-joined run, followed by anything

The step from one line to a file. `unwordsChars_isTokenization` handles a token list that
is the *whole* input; this handles one that is a prefix, followed by whitespace and then
more input. That is what a line inside a file is. -/

theorem isTokenization_unwordsChars_append :
    ∀ {ts : Toks}, Printable ts → ∀ {w : List Char}, w ≠ [] → AllWhitespace w →
    ∀ {cs : List Char} {us : Toks}, IsTokenization cs us →
    IsTokenization (unwordsChars ts ++ w ++ cs) (ts ++ us)
  | [], _, _, _, hw, _, _, h => by
      simpa [unwordsChars] using isTokenization_wsPrefix hw h
  | [t], hp, w, hwne, hw, cs, us, h => by
      simpa [unwordsChars] using
        isTokenization_consTok (hp t (by simp)) hwne hw h
  | t :: u :: ts, hp, w, hwne, hw, cs, us, h => by
      have ih : IsTokenization (unwordsChars (u :: ts) ++ w ++ cs) ((u :: ts) ++ us) :=
        isTokenization_unwordsChars_append
          (fun s hs => hp s (by simp [hs])) hwne hw h
      have := isTokenization_consTok (t := t) (hp t (by simp))
        (w := [' ']) (by simp) (allWhitespace_cons (by decide) allWhitespace_nil) ih
      simpa [unwordsChars, List.append_assoc] using this

/-! ## The whole file tokenizes to the tokens it carries -/

theorem isTokenization_renderLines :
    ∀ {ls : List Encoder.Line}, Printable ((ls.map Prod.snd).flatten) →
    IsTokenization ((ls.map Encoder.renderLineChars).flatten)
      ((ls.map Prod.snd).flatten)
  | [], _ => by simpa using IsTokenization.nil
  | l :: ls, hp => by
      have hpl : Printable l.2 := fun t ht => hp t (by simp [ht])
      have hprest : Printable ((ls.map Prod.snd).flatten) := by
        intro t ht; exact hp t (by simp [ht])
      have ih := isTokenization_renderLines hprest
      have hstep := isTokenization_unwordsChars_append hpl
        (w := ['\n']) (by simp) (allWhitespace_cons (by decide) allWhitespace_nil) ih
      have hpre := isTokenization_wsPrefix (allWhitespace_indent l.1) hstep
      simpa [Encoder.renderLineChars, List.append_assoc] using hpre

/-- **The tokenization half of the round trip.** The emitted text tokenizes to exactly the
tokens the file carries, so what remains for `mpsRoundTrip` is to show those tokens derive
`m` under `IsMpsToks`. -/
theorem isTokenization_encodeMps (name : String) (m : Mip)
    (hp : Printable (Encoder.mpsToks name m)) :
    IsTokenization (Encoder.encodeMpsNamed name m).toList (Encoder.mpsToks name m) := by
  have := isTokenization_renderLines (ls := Encoder.mpsLines name m) hp
  simpa [Encoder.encodeMpsNamed, Encoder.encodeMpsChars, Encoder.mpsToks] using this

/-! ## Names the grammar accepts are names the printer can emit

`IsNameTok` and `PrintableTok` were arrived at from opposite ends — one says what the
grammar will read back as a name, the other what survives being joined and re-split — and
they agree. That they do is why `EncodableNames` is the only precondition the round trip
needs about names. -/

theorem printableTok_of_isNameTok {t : String} (h : IsNameTok t) : PrintableTok t :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## Every token the emitter writes is one the tokenizer could produce

`Printable (mpsToks name m)` is the last hypothesis on `isTokenization_encodeMps`. Unlike
the indents it cannot be made structural: the tokens include names taken from the user's
`Mip`, so it genuinely needs `EncodableNames` and the sense condition from
`Mip.WellFormed`. What it can be is compositional — one lemma per kind of token, then one
per section. -/

/-- So an all-literal token list can be checked by `decide`, which is what makes the
section headers and the fixed vocabulary (`BND`, `rhs`, `'MARKER'`, …) free. -/
instance (ts : Toks) : Decidable (Printable ts) := by
  unfold Printable; infer_instance

/-- Lines contribute their tokens, so per-line printability suffices. -/
theorem printable_flatten {ls : List Encoder.Line}
    (h : ∀ l ∈ ls, Printable l.2) : Printable ((ls.map Prod.snd).flatten) := by
  intro t ht
  obtain ⟨ts, hts, ht⟩ := List.mem_flatten.mp ht
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hts
  exact h l hl t ht

theorem printableTok_mpsRat (q : ℚ) : PrintableTok (Encoder.mpsRat q) := by
  unfold Encoder.mpsRat
  split
  · exact printInt_printableTok _
  · exact printRat_printableTok _

/-- A marker line's name, `M` followed by the marker number. -/
theorem printableTok_markerName (n : Nat) : PrintableTok ("M" ++ printNat n) := by
  obtain ⟨_, hnw, _⟩ := printNat_printableTok n
  refine ⟨by simp, ?_, by simp⟩
  intro c hc
  rcases List.mem_cons.mp (by simpa using hc) with rfl | hc
  · decide
  · exact hnw c hc

/-- A row's sense, which `Mip.WellFormed` restricts to `L`, `G` or `E`. -/
theorem printableTok_sense {c : Char} (h : c = 'L' ∨ c = 'G' ∨ c = 'E') :
    PrintableTok c.toString := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ### One lemma per section -/

theorem printable_markerLine (n : Nat) (tag : String)
    (htag : PrintableTok ("'" ++ tag ++ "'")) :
    Printable (Encoder.markerLine n tag).2 := by
  intro t ht
  simp only [Encoder.markerLine, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact printableTok_markerName n
  · decide
  · exact htag

theorem printable_colLines {name : String} (hn : PrintableTok name)
    (es : List (String × ℚ)) (hr : ∀ e ∈ es, PrintableTok e.1) :
    ∀ l ∈ Encoder.colLines name es, Printable l.2 := by
  intro l hl
  simp only [Encoder.colLines, List.mem_map] at hl
  obtain ⟨e, he, rfl⟩ := hl
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact hn
  · exact hr e he
  · exact printableTok_mpsRat e.2

theorem printable_objSenseLines (m : Mip) :
    ∀ l ∈ Encoder.objSenseLines m, Printable l.2 := by
  intro l hl
  cases hm : m.objSense <;> rw [Encoder.objSenseLines, hm] at hl
  · simp at hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> intro t ht <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht <;>
      rcases ht with rfl <;> decide

theorem printable_rhsLines (m : Mip)
    (hr : ∀ r ∈ m.rows, PrintableTok r.name) :
    ∀ l ∈ Encoder.rhsLines m, Printable l.2 := by
  intro l hl
  simp only [Encoder.rhsLines, List.mem_map] at hl
  obtain ⟨r, hrm, rfl⟩ := hl
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · decide
  · exact hr r (by simpa using hrm)
  · exact printableTok_mpsRat r.rhs

theorem printable_rowsLines (m : Mip)
    (hr : ∀ r ∈ m.rows, PrintableTok r.name ∧ (r.sense = 'L' ∨ r.sense = 'G' ∨ r.sense = 'E')) :
    ∀ l ∈ Encoder.rowsLines m, Printable l.2 := by
  intro l hl
  simp only [Encoder.rowsLines, List.mem_cons, List.mem_map] at hl
  rcases hl with rfl | ⟨r, hrm, rfl⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> decide
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    obtain ⟨hname, hsense⟩ := hr r (by simpa using hrm)
    rcases ht with rfl | rfl
    · exact printableTok_sense hsense
    · exact hname

theorem printable_boundLines (v : Mip.Var) (hv : PrintableTok v.name) :
    ∀ l ∈ Encoder.boundLines v, Printable l.2 := by
  have h3 : ∀ ty : String, PrintableTok ty → Printable [ty, "BND", v.name] := by
    intro ty hty t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact hty
    · decide
    · exact hv
  have h4 : ∀ ty : String, PrintableTok ty → ∀ q : ℚ,
      Printable [ty, "BND", v.name, Encoder.mpsRat q] := by
    intro ty hty q t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hty
    · decide
    · exact hv
    · exact printableTok_mpsRat q
  intro l hl
  rcases hlo : v.lo with _ | lo <;> rcases hhi : v.hi with _ | hi <;>
    simp only [Encoder.boundLines, hlo, hhi] at hl <;> simp_all
  · rcases hl with rfl | ⟨hb, rfl⟩
    · exact h3 "MI" (by decide)
    · exact h3 "PL" (by decide)
  · rcases hl with rfl | rfl
    · exact h3 "MI" (by decide)
    · exact h4 "UP" (by decide) hi
  · rcases hl with rfl | ⟨hb, rfl⟩
    · exact h4 "LO" (by decide) lo
    · exact h3 "PL" (by decide)
  · rcases hl with rfl | rfl
    · exact h4 "LO" (by decide) lo
    · exact h4 "UP" (by decide) hi


/-! ### The names a problem must have for its file to be readable back

`EncodableNames` plus the sense restriction from `Mip.WellFormed`, bundled so the lemmas
below do not each carry four hypotheses. -/

structure Emittable (m : Mip) (name : String) : Prop where
  probName : PrintableTok name
  varNames : ∀ v ∈ m.vars, PrintableTok v.name
  rowNames : ∀ r ∈ m.rows, PrintableTok r.name
  senses : ∀ r ∈ m.rows, r.sense = 'L' ∨ r.sense = 'G' ∨ r.sense = 'E'

/-- A column's entries are keyed by a row name or by the objective row. -/
theorem printableTok_colEntry {n : String} (m : Mip) (h : Emittable m n) (j : Nat) :
    ∀ e ∈ Encoder.colEntries m j, PrintableTok e.1 := by
  intro e he
  simp only [Encoder.colEntries, List.mem_append] at he
  rcases he with he | he
  · split at he
    · simp at he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      exact (show PrintableTok Encoder.objRowName by decide)
  · obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp he
    split at he
    · simp at he
    · simp only [Option.some.injEq] at he
      subst he
      exact h.rowNames r (by simpa using hr)

theorem printable_columnsAux {n : String} (m : Mip) (h : Emittable m n) :
    ∀ (vs : List (Nat × Mip.Var)) (inInt : Bool) (mk : Nat),
      (∀ p ∈ vs, PrintableTok p.2.name) →
      ∀ l ∈ Encoder.columnsAux m vs inInt mk, Printable l.2
  | [], inInt, mk, _ => by
      intro l hl
      simp only [Encoder.columnsAux] at hl
      split at hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        exact printable_markerLine mk "INTEND" (by decide)
      · simp at hl
  | (j, v) :: rest, inInt, mk, hvs => by
      intro l hl
      simp only [Encoder.columnsAux] at hl
      rcases List.mem_append.mp hl with hl | hl
      · rcases List.mem_append.mp hl with hl | hl
        · split at hl
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            subst hl; exact printable_markerLine _ "INTORG" (by decide)
          · split at hl
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              subst hl; exact printable_markerLine _ "INTEND" (by decide)
            · simp at hl
        · refine printable_colLines (hvs (j, v) (by simp)) _ ?_ l hl
          split
          · intro e he
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            subst he
            exact (show PrintableTok Encoder.objRowName by decide)
          · exact printableTok_colEntry m h j
      · exact printable_columnsAux m h rest v.isInt _
          (fun p hp => hvs p (by simp [hp])) l hl

theorem printable_columnsLines {n : String} (m : Mip) (h : Emittable m n) :
    ∀ l ∈ Encoder.columnsLines m, Printable l.2 :=
  printable_columnsAux m h _ _ _ (by
    intro p hp
    obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hp
    have hp2 : p.2 = m.vars.toList[i] := by rw [← he]
    rw [hp2]
    exact h.varNames _ (by simpa using List.getElem_mem hi))

/-- The constraint-row lines on their own, without the leading free objective row:
`simp` splits `rowsLines`' cons, so the tail needs its own lemma. -/
theorem printable_rowEntryLines (m : Mip)
    (hr : ∀ r ∈ m.rows,
      PrintableTok r.name ∧ (r.sense = 'L' ∨ r.sense = 'G' ∨ r.sense = 'E')) :
    ∀ l ∈ m.rows.toList.map
        (fun r => ((Encoder.Indent.one, [r.sense.toString, r.name]) : Encoder.Line)),
      Printable l.2 := by
  intro l hl
  obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hl
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  obtain ⟨hname, hsense⟩ := hr r (by simpa using hrm)
  rcases ht with rfl | rfl
  · exact printableTok_sense hsense
  · exact hname

/-- The `BOUNDS` section: every variable's lines. -/
theorem printable_boundsSection (m : Mip) (hv : ∀ v ∈ m.vars, PrintableTok v.name) :
    ∀ l ∈ (m.vars.toList.map Encoder.boundLines).flatten, Printable l.2 := by
  intro l hl
  obtain ⟨ls, hls, hl⟩ := List.mem_flatten.mp hl
  obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hls
  exact printable_boundLines v (hv v (by simpa using hvm)) l hl

/-! ### Assembly -/

/-- Every token the file carries is one the tokenizer could produce. -/
theorem printable_mpsToks {n : String} (m : Mip) (h : Emittable m n) :
    Printable (Encoder.mpsToks n m) := by
  have hname : Printable (Encoder.Indent.none, ["NAME", n]).2 := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · decide
    · exact h.probName
  have hkw : ∀ k : String, PrintableTok k →
      Printable (Encoder.Indent.none, [k]).2 := by
    intro k hk t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    exact hk
  refine printable_flatten ?_
  intro l hl
  simp only [Encoder.mpsLines, List.cons_append, List.mem_cons,
    List.mem_append] at hl
  repeat' rcases hl with hl | hl
  all_goals first
    | decide
    | exact hname
    | exact hkw _ (by decide)
    | (subst hl; exact hname)
    | (subst hl; exact hkw _ (by decide))
    | exact printable_objSenseLines m l (by assumption)
    | exact printable_rowsLines m
        (fun r hr => ⟨h.rowNames r hr, h.senses r hr⟩) l (by assumption)
    | exact printable_rowEntryLines m
        (fun r hr => ⟨h.rowNames r hr, h.senses r hr⟩) l (by assumption)
    | exact printable_columnsLines m h l (by assumption)
    | exact printable_rhsLines m h.rowNames l (by assumption)
    | exact printable_boundsSection m h.varNames l (by assumption)
    | simp_all
    | (exfalso; simp_all)

/-- **The tokenization half, with no hypotheses left but the names.** The emitted text
tokenizes to exactly the tokens the file carries. -/
theorem isTokenization_encodeMps' {n : String} (m : Mip) (h : Emittable m n) :
    IsTokenization (Encoder.encodeMpsNamed n m).toList (Encoder.mpsToks n m) :=
  isTokenization_encodeMps n m (printable_mpsToks m h)

end LeanVIPR.Mps
