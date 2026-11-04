module

public import LeanVIPR.Thm.Parser.Tokens
public import LeanVIPR.Thm.Parser.Number
public import LeanVIPR.Thm.Parser.Valid
public import LeanVIPR.Thm.Parser.Certificate

@[expose] public section

/-!
# What is proved about the reader

**This file is the result.** Every theorem a reader of the development should need is
here or named here; the files in `LeanVIPR.Thm.Parser.*` are how they are proved and are
not meant to be read.

```lean
parseVipr content = .ok v ↔ (IsViprText content.toList v ∧ IsValid v)
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

`validateVipr_eq_ok_iff` is proved where it is rather than restated here because
`parseVipr_complete` consumes it; declaring it here would make `Thm.Parser.Certificate`
depend on this file and close a cycle.

Not proved: a printer and a round-trip `parseVipr (render v) = .ok v`. There is no
printer yet, so there is no round-trip theorem to state. `parseVipr_complete` is the
half of it that does not need one.
-/

namespace LeanVIPR.Parser

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

end LeanVIPR.Parser
