module

public import LeanVIPR.Thm.Vipr.Lemmas
public import LeanVIPR.Thm.Valid

@[expose] public section

/-!
# The certificate parser implements the certificate grammar

The headline result is `parseVipr_eq_ok_iff`: the parser accepts exactly the files the
grammar derives, and returns exactly the certificate the grammar assigns to them.

```lean
parseVipr content = .ok v ↔ (IsViprText content.toList v ∧ IsValid v)
```

Neither side of that `↔` mentions a parser function. `IsViprText` composes
`LeanVIPR.Thm.Tokens.Grammar` with `LeanVIPR.Thm.Vipr.Grammar`, and `IsValid` is
`LeanVIPR.Thm.Valid.Grammar`; between them they reach down to characters without
reference to `wsTokens`, `parseViprToks` or `validateVipr`. That is what makes the
theorem worth proving: phrased in terms of `wsTokens` it would take the tokenizer's own
output as the definition of tokenization, and so could not detect a tokenizer that
dropped, merged, or truncated tokens. With `isVipr_unique` and `isTokenization_unique`,
the grammars therefore *are* the specification of what LeanVIPR reads.

Why both directions matter. `parseVipr_sound` is the one that closes a soundness gap:
`checkVipr_sound` proves a claim about the AST it is given, so a misparse would let it
establish a true claim about the wrong mixed-integer problem. `parseVipr_complete` is
what makes a rejection meaningful: without it, "LeanVIPR rejects this file" could always
be an artefact of a narrow reader rather than a statement about the file.

Supporting results, in decreasing order of interest:

**Terminals.** For each terminal, an `iff` saying the consumer reads exactly the tokens
the grammar derives, returns exactly the value the grammar assigns, and leaves exactly
the rest of the stream. Each pairs with a `_nil` lemma: an exhausted stream is always an
error, never a silent success.

**Nonterminals.** In `LeanVIPR.Thm.Vipr.Lemmas`, a `_complete`/`_sound` pair each.

One asymmetry is worth naming. `takeScope` is the parser's only lookahead, and it is
greedy, so the grammar's `IsDers` carries a side condition excluding a `DER` row *named*
`global` or `local` directly after a flagless row. Such a file is rejected rather than
misread, so this is a limit on completeness, not on soundness — and it is a property of
the VIPR format, which leaves the keyword optional and unbracketed, not of this parser.
-/

namespace LeanVIPR.Ast

/-! ## The whole certificate

`IsValid` is a separate conjunct because it is not a syntactic condition: it says
indices are in range, that sparse vectors mention each variable once, and that no
derivation is used after its own final-use index. The grammar says what the file *is*;
`IsValid` says whether what it denotes is a usable problem. Both are declarative, so
no parser or validator function appears in `parseVipr_eq_ok_iff`. -/

theorem parseViprToks_complete {ts : Toks} {v : Vipr} (hg : IsVipr ts v)
    (hvalid : IsValid v) : parseViprToks ts = .ok v := by
  have hv : validateVipr v = .ok () := validateVipr_eq_ok_iff.mpr hvalid
  obtain ⟨sVer, sVar, sInt, sObj, sCon, sRtp, sSol, sDer, hts,
    hver, ⟨cntV, hvarEq, hcntV⟩, ⟨cntI, bodyI, hintEq, hcntI, hbodyI⟩,
    ⟨cntO, bodyO, hobjEq, hcntO, hbodyO⟩,
    ⟨cntC, bndC, bodyC, hconEq, hcntC, hbndC, hnumCon, hbodyC⟩, hrtp,
    ⟨cntS, bodyS, hsolEq, hcntS, hnumSol, hbodyS⟩,
    ⟨cntD, bodyD, hderEq, hcntD, hbodyD⟩⟩ := hg
  subst hver
  subst hvarEq
  subst hintEq
  subst hobjEq
  subst hconEq
  subst hsolEq
  subst hderEq
  subst hts
  have hC : ∀ suf, takeCons v.numCon (bodyC ++ suf) = .ok (v.cons.toList, suf) :=
    fun suf => by rw [hnumCon]; exact takeCons_complete hbodyC
  have hS : ∀ suf, takeSols v.numSol (bodyS ++ suf) = .ok (v.sols.toList, suf) :=
    fun suf => by rw [hnumSol]; exact takeSols_complete hbodyS
  rw [parseViprToks]
  simp only [List.cons_append, List.nil_append, List.append_assoc, bind, Except.bind,
    expectTok_prefix, takeTok_prefix, takeNat_prefix hcntV, takeStrings_complete,
    takeNat_prefix hcntI, takeNats_complete hbodyI, takeNat_prefix hcntO,
    takePairs_complete hbodyO, takeNat_prefix hcntC, takeNat_prefix hbndC, hC, takeRtp_complete hrtp, takeNat_prefix hcntS,
    hS, takeNat_prefix hcntD, takeDers_complete hbodyD, hv]

theorem parseViprToks_sound {ts : Toks} {v : Vipr} (h : parseViprToks ts = .ok v) :
    IsVipr ts v ∧ IsValid v := by
  rw [parseViprToks] at h
  obtain ⟨ts1, e1, h1⟩ := bind_eq_ok h
  obtain rfl := expectTok_sound e1
  obtain ⟨⟨ver, ts2⟩, e2, h2⟩ := bind_eq_ok h1
  obtain rfl := takeTok_sound e2
  dsimp only at h2
  obtain ⟨ts3, e3, h3⟩ := bind_eq_ok h2
  obtain rfl := expectTok_sound e3
  obtain ⟨⟨nvar, ts4⟩, e4, h4⟩ := bind_eq_ok h3
  obtain ⟨cntV, rfl, hcntV⟩ := takeNat_sound e4
  dsimp only at h4
  obtain ⟨⟨names, ts5⟩, e5, h5⟩ := bind_eq_ok h4
  obtain ⟨hlenN, rfl⟩ := takeStrings_sound e5
  dsimp only at h5
  obtain ⟨ts6, e6, h6⟩ := bind_eq_ok h5
  obtain rfl := expectTok_sound e6
  obtain ⟨⟨nint, ts7⟩, e7, h7⟩ := bind_eq_ok h6
  obtain ⟨cntI, rfl, hcntI⟩ := takeNat_sound e7
  dsimp only at h7
  obtain ⟨⟨ints, ts8⟩, e8, h8⟩ := bind_eq_ok h7
  obtain ⟨hlenI, bodyI, rfl, hbodyI⟩ := takeNats_sound e8
  dsimp only at h8
  obtain ⟨ts9, e9, h9⟩ := bind_eq_ok h8
  obtain rfl := expectTok_sound e9
  obtain ⟨⟨objsense, ts10⟩, e10, h10⟩ := bind_eq_ok h9
  obtain rfl := takeTok_sound e10
  dsimp only at h10
  obtain ⟨⟨nobj, ts11⟩, e11, h11⟩ := bind_eq_ok h10
  obtain ⟨cntO, rfl, hcntO⟩ := takeNat_sound e11
  dsimp only at h11
  obtain ⟨⟨objterms, ts12⟩, e12, h12⟩ := bind_eq_ok h11
  obtain ⟨hlenO, bodyO, rfl, hbodyO⟩ := takePairs_sound e12
  dsimp only at h12
  obtain ⟨ts13, e13, h13⟩ := bind_eq_ok h12
  obtain rfl := expectTok_sound e13
  obtain ⟨⟨ncon, ts14⟩, e14, h14⟩ := bind_eq_ok h13
  obtain ⟨cntC, rfl, hcntC⟩ := takeNat_sound e14
  dsimp only at h14
  obtain ⟨⟨nbound, ts15⟩, e15, h15⟩ := bind_eq_ok h14
  obtain ⟨bndC, rfl, hbndC⟩ := takeNat_sound e15
  dsimp only at h15
  obtain ⟨⟨cons, ts16⟩, e16, h16⟩ := bind_eq_ok h15
  obtain ⟨hlenC, bodyC, rfl, hbodyC⟩ := takeCons_sound e16
  dsimp only at h16
  obtain ⟨⟨rtp, ts19⟩, e19, h19⟩ := bind_eq_ok h16
  obtain ⟨sRtp, rfl, hrtp⟩ := takeRtp_sound e19
  dsimp only at h19
  obtain ⟨ts20, e20, h20⟩ := bind_eq_ok h19
  obtain rfl := expectTok_sound e20
  obtain ⟨⟨nsol, ts21⟩, e21, h21⟩ := bind_eq_ok h20
  obtain ⟨cntS, rfl, hcntS⟩ := takeNat_sound e21
  dsimp only at h21
  obtain ⟨⟨sols, ts22⟩, e22, h22⟩ := bind_eq_ok h21
  obtain ⟨hlenS, bodyS, rfl, hbodyS⟩ := takeSols_sound e22
  dsimp only at h22
  obtain ⟨ts23, e23, h23⟩ := bind_eq_ok h22
  obtain rfl := expectTok_sound e23
  obtain ⟨⟨nder, ts24⟩, e24, h24⟩ := bind_eq_ok h23
  obtain ⟨cntD, rfl, hcntD⟩ := takeNat_sound e24
  dsimp only at h24
  obtain ⟨⟨ders, ts25⟩, e25, h25⟩ := bind_eq_ok h24
  obtain ⟨hlenD, bodyD, rfl, hbodyD⟩ := takeDers_sound e25
  dsimp only at h25
  cases ts25 with
  | cons t rest => simp at h25
  | nil =>
      obtain ⟨u, e26, h26⟩ := bind_eq_ok h25
      obtain rfl : u = () := rfl
      simp only [Except.ok.injEq] at h26
      subst h26
      refine ⟨⟨["VER", ver], "VAR" :: cntV :: names, "INT" :: cntI :: bodyI,
        "OBJ" :: objsense :: cntO :: bodyO, "CON" :: cntC :: bndC :: bodyC, sRtp,
        "SOL" :: cntS :: bodyS, "DER" :: cntD :: bodyD, by simp, rfl,
        ⟨cntV, by simp, by simpa [hlenN] using hcntV⟩,
        ⟨cntI, bodyI, rfl, by simpa [hlenI] using hcntI, hbodyI⟩,
        ⟨cntO, bodyO, rfl, by simpa [hlenO] using hcntO, hbodyO⟩,
        ⟨cntC, bndC, bodyC, rfl, by simpa using hcntC, hbndC, by simp [hlenC], hbodyC⟩,
        hrtp, ⟨cntS, bodyS, rfl, by simpa using hcntS, by simp [hlenS], hbodyS⟩,
        ⟨cntD, bodyD, rfl, by simpa [hlenD] using hcntD, hbodyD⟩⟩,
        validateVipr_eq_ok_iff.mp e26⟩

/-- **Soundness.** A certificate the parser accepts is derived by the grammar from the
characters of the file, and the value returned is the one the grammar assigns to them. -/
theorem parseVipr_sound {content : String} {v : Vipr} (h : parseVipr content = .ok v) :
    IsViprText content.toList v ∧ IsValid v := by
  obtain ⟨hg, hv⟩ := parseViprToks_sound h
  exact ⟨⟨_, wsTokens_isTokenization _, hg⟩, hv⟩

/-- **Completeness.** The parser accepts every certificate the grammar derives whose
indices validate, and returns the value the grammar assigns. -/
theorem parseVipr_complete {content : String} {v : Vipr}
    (hg : IsViprText content.toList v) (hv : IsValid v) :
    parseVipr content = .ok v := by
  obtain ⟨ts, ht, hg⟩ := hg
  rw [isTokenization_eq ht] at hg
  exact parseViprToks_complete hg hv

theorem parseVipr_eq_ok_iff {content : String} {v : Vipr} :
    parseVipr content = .ok v ↔ (IsViprText content.toList v ∧ IsValid v) :=
  ⟨parseVipr_sound, fun h => parseVipr_complete h.1 h.2⟩

/-- The grammar is unambiguous: a token list derives at most one certificate. -/
theorem isVipr_unique {ts : Toks} {v v' : Vipr} (hv : IsValid v) (hv' : IsValid v')
    (h : IsVipr ts v) (h' : IsVipr ts v') : v = v' := by
  have h1 := parseViprToks_complete h hv
  rw [parseViprToks_complete h' hv'] at h1
  exact (Except.ok.inj h1).symm

end LeanVIPR.Ast
