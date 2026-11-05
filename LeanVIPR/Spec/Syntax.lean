module

public import LeanVIPR.Spec.Syntax.Ast
public import LeanVIPR.Spec.Syntax.Grammar

@[expose] public section

/-!
# Syntax: which files are certificates

`Grammar` says which character sequences are VIPR certificates and which certificate
each one denotes — tokenization, numeric tokens, the eight sections, and the index
conditions a usable certificate must satisfy. `Ast` is the shape it denotes into, plus
the handful of functions that say what the AST's index fields *mean*.

Nothing here mentions a reader. `LeanVIPR.Thm.Parser` proves the reader of
`LeanVIPR.Impl.Parser` accepts exactly what `Grammar` derives and returns exactly what
it assigns — which is only a claim worth making because this file does not refer to that
reader.
-/
