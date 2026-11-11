module

public import LeanVIPR.Thm.Parser.Tokens
public import LeanVIPR.Thm.Parser.Number
public import LeanVIPR.Thm.Parser.Valid
public import LeanVIPR.Thm.Parser.Certificate
public import LeanVIPR.Thm.Parser.Printer

@[expose] public section

/-!
# What is proved about the reader

**This file is the result.** Every theorem a reader of the development should need is
here or named here; the files in `LeanVIPR.Thm.Parser.*` are how they are proved and are
not meant to be read.

```lean
parseVipr content = .ok v ↔ (IsViprText content.toList v ∧ IsValid v)   -- reading
parseVipr (toString v) = .ok v                                          -- and writing
```

Neither side mentions a reader. `IsViprText` and `IsValid` come from
`LeanVIPR.Thm.Parser.Grammar`, which is the whole specification of the format and the
one file to read to know what LeanVIPR accepts. That independence is the point: a
statement phrased in terms of `wsTokens` would take the tokenizer's own output as the
definition of tokenization, and so could not detect a tokenizer that dropped, merged, or
truncated tokens.

The two directions do different jobs. **Soundness** closes a gap replay cannot:
`checkVipr_sound` proves a claim about the AST it is handed, so a token read as the wrong
rational would let it establish a true claim about a *different* mixed-integer problem.
**Completeness** is what makes a rejection a statement about the file rather than
possibly an artefact of a narrow reader.

| result | where it is proved |
|---|---|
| `parseVipr_sound`, `parseVipr_complete`, `parseVipr_eq_ok_iff` | below |
| `isVipr_unique` — the grammar derives at most one certificate | below |
| `isTokenization_iff`, `isTokenization_unique` — tokenization is exactly `wsTokens` | `Thm.Parser.Tokens` |
| `parseNum_eq_some_iff`, `isNumValue_unique` — numeric tokens | `Thm.Parser.Number` |
| `validateVipr_eq_ok_iff` — validation decides exactly `IsValid` | `Thm.Parser.Valid` |
| `toString_roundtrip` — reading back what the printer writes returns what was written | below |
| `toString_roundtrip_of_parse` — the same with no side conditions, for anything the parser accepts | below |
| `printVipr_isVipr` — the grammar derives everything the printer writes | `Thm.Parser.Printer` |
| `unwords_isTokenization` — joining tokens and re-tokenizing is the identity | `Thm.Parser.Printer` |

`validateVipr_eq_ok_iff` is proved where it is rather than restated here because
`parseVipr_complete` consumes it; declaring it here would make `Thm.Parser.Certificate`
depend on this file and close a cycle.

**What the round trip does not say.** It is `parseVipr (toString v) = .ok v`: printing
then reading returns the certificate. The other direction, `toString (parseVipr s) = s`,
is not proved and is not true in general -- the printer normalizes whitespace between
tokens and writes each rational in one canonical form, so text that differs only in
layout prints back differently. Scope keywords *are* reproduced exactly, since
`ViprScope` records whether one was present. Byte-level fidelity would be needed to bind
a kernel-checked theorem to source bytes rather than to the AST; it is not claimed here.

**Round trip.** `LeanVIPR.Impl.Parser.Printer` writes a certificate back to text and
`LeanVIPR.Thm.Parser.Printer` proves reading it back returns what was written. It is
stated in this namespace alongside the reading results, since it is a theorem about the
parser; only the printer itself lives in `LeanVIPR.Impl`.

```lean
toString_roundtrip : IsVipr ts v → IsValid v → Printable (verbatimToks v) →
                       parseVipr (toString v) = .ok v
```

The three hypotheses are not slack in the proof — no printer could drop them. A `Vipr`
value carries arbitrary `String` fields, so a variable could be named `""`, `"a b"` or
`"%x"`, none of which survives tokenization; `Printable (verbatimToks v)` says the
strings it copies verbatim are themselves tokens. `IsVipr ts v` supplies what the
grammar demands and the datatype does not — a sense being one of `E`, `L`, `G`,
`numCon` agreeing with the array it counts, a `lin weak` block listing no bounds being
the `global` spelling. All three hold of any certificate that came from a parse.

Deriving them from `parseVipr content = .ok v`, to get a hypothesis-free
`parseVipr content = .ok v → parseVipr (toString v) = .ok v`, needs one further lemma:
that the verbatim strings occur as tokens of the stream they were read from.

Two printer choices are forced by the grammar rather than by taste: rationals are
written `num/den`, since every rational has that form while only some have a finite
decimal one; and a derivation with no scope flag is written with an explicit `local`,
because the flag is matched greedily and omitting it would make the next row's name
ambiguous when that name is `global` or `local`.
-/

namespace LeanVIPR.Parser

open LeanVIPR.Impl

/-- **Soundness.** A certificate the parser accepts is derived by the grammar from the
characters of the file, and the value returned is the one the grammar assigns to them. -/
theorem parseVipr_sound {content : String} {v : Vipr} (h : parseVipr content = .ok v) :
    IsViprText content.toList v ∧ IsValid v := by
  rw [parseVipr, wsTokensOf_eq] at h
  obtain ⟨hg, hv⟩ := parseViprToks_sound h
  exact ⟨⟨_, wsTokens_isTokenization _, hg⟩, hv⟩

/-- **Completeness.** The parser accepts every certificate the grammar derives whose
indices validate, and returns the value the grammar assigns. -/
theorem parseVipr_complete {content : String} {v : Vipr}
    (hg : IsViprText content.toList v) (hv : IsValid v) :
    parseVipr content = .ok v := by
  obtain ⟨ts, ht, hg⟩ := hg
  rw [isTokenization_eq ht] at hg
  rw [parseVipr, wsTokensOf_eq]
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

/-- **The round trip.** Reading back what the printer writes gives the certificate it
was given.

The two hypotheses are not slack in the proof; no printer could drop them. A `Vipr`
value carries arbitrary `String` fields, so a variable could be named `""`, `"a b"` or
`"%x"` — none of which survives tokenization — and `IsVipr ts v` is what supplies the
rest of what the grammar demands and the datatype does not, such as a sense being one of
`E`, `L`, `G` and `numCon` agreeing with the array it counts. Both hold of any
certificate that came from a parse. -/
theorem toString_roundtrip {ts : Toks} {v : Vipr} (hg : IsVipr ts v)
    (hvalid : IsValid v) (hv : Printable (verbatimToks v)) :
    parseVipr (toString v) = .ok v :=
  parseVipr_complete (print_isViprText hg hv) hvalid

/-- **The round trip, with nothing assumed.** Whatever the parser accepts, printing and
reading back returns it.

The three hypotheses of `toString_roundtrip` are all discharged by the acceptance itself.
`parseVipr_eq_ok_iff` supplies the grammar derivation and `IsValid`; the printability of
the strings the certificate carries verbatim follows because they were tokens of the
stream it was read from — `verbatimToks_subset` — and a tokenization's tokens are
non-empty, whitespace-free, and never begin with `%`, which is exactly `PrintableTok`
(`printable_of_isTokenization`). So the side conditions are not slack that a caller has
to supply: they hold of every certificate there is to print. -/
theorem toString_roundtrip_of_parse {content : String} {v : Vipr}
    (h : parseVipr content = .ok v) : parseVipr (toString v) = .ok v := by
  obtain ⟨⟨ts, htok, hg⟩, hvalid⟩ := parseVipr_eq_ok_iff.mp h
  exact toString_roundtrip hg hvalid
    (fun t ht => printable_of_isTokenization htok t (verbatimToks_subset hg t ht))

end LeanVIPR.Parser
