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

end LeanVIPR.Mps
