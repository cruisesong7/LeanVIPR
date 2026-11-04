module

public import LeanVIPR.Ast.Types

@[expose] public section

/-!
# What a certificate's characters tokenize to

**This file is the review surface for tokenization.** It says which token lists a
character list may be read as, and nothing else: no proofs, and no reference to how the
tokenizer works. `LeanVIPR.Thm.Tokens` proves the tokenizer agrees with it in both
directions, so a reader who accepts this definition need not read the tokenizer.

Without this, the parser's correctness theorem would quantify over
`wsTokens content.toList` — an implementation function in its own specification — and
would say nothing about how characters become tokens. A tokenizer that silently dropped
or merged tokens would still satisfy it.

Three rules, in the order the first character decides between them: whitespace
separates, a `%` *beginning* a token runs a comment to the end of the line, and anything
else begins a token that extends to the next whitespace. A `%` inside a token is an
ordinary character, so `x%y` is one token.
-/

namespace LeanVIPR.Ast

/-- No character of a token is whitespace. -/
def NoWhitespace (t : List Char) : Prop := ∀ c ∈ t, ¬ c.isWhitespace

/-- A token ending here cannot be extended: the input is exhausted, or what follows is
whitespace. This is what makes tokens maximal, and so the tokenization unique. -/
def AtTokenEnd (cs : List Char) : Prop := ∀ c ∈ cs.head?, c.isWhitespace

/-- `IsTokenization cs ts`: the characters `cs` tokenize to exactly `ts`. -/
inductive IsTokenization : List Char → Toks → Prop
  /-- The empty input has no tokens. -/
  | nil : IsTokenization [] []
  /-- Whitespace separates tokens and contributes none. -/
  | space {c : Char} {cs : List Char} {ts : Toks} (hw : c.isWhitespace)
      (h : IsTokenization cs ts) : IsTokenization (c :: cs) ts
  /-- A `%` beginning a token comments out the rest of its line. -/
  | commentLine {body rest : List Char} {ts : Toks} (hn : '\n' ∉ body)
      (h : IsTokenization rest ts) : IsTokenization ('%' :: (body ++ '\n' :: rest)) ts
  /-- A comment on the last line, with no terminating newline, ends the input. -/
  | commentEnd {body : List Char} (hn : '\n' ∉ body) : IsTokenization ('%' :: body) []
  /-- Any other maximal run of non-whitespace characters is one token. -/
  | token {t rest : List Char} {ts : Toks} (hne : t ≠ []) (hnw : NoWhitespace t)
      (hpct : t.head? ≠ some '%') (hend : AtTokenEnd rest)
      (h : IsTokenization rest ts) :
      IsTokenization (t ++ rest) (String.ofList t :: ts)

end LeanVIPR.Ast
