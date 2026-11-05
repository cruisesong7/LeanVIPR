module

public import LeanVIPR.Impl.Parser
public import LeanVIPR.Impl.Checker

@[expose] public section

/-!
# The implementation

The executable artifacts, and the only things in the development whose correctness is in
question. Each is proved against `LeanVIPR.Spec` in `LeanVIPR.Thm`; none of it needs to
be read to know what LeanVIPR accepts.

| file | does |
|---|---|
| `Impl.Parser` | read a file into the AST, and validate its indices |
| `Impl.Checker` | replay a certificate with an array-backed pool, deciding each rule's side conditions |

`Impl.Parser` is the tokenizer, the parser and the validator, with
`Impl.Parser.Utils` holding the character-level helpers it uses: list splitting, and the
exact readers for naturals, integers, decimals and `p/q` rationals. `Impl.Checker` is the replay
loop, with `Impl.Checker.Form`, `.Rules` and `.Solution` holding the `Bool`-valued
decisions it calls.

The `B` suffix on a definition here means it is the `Bool`-valued decision procedure for
a declarative notion of the same name in `LeanVIPR.Spec` — `absurdB` for `Absurd`,
`stepValidB` for `StepValid`. Where there is no such pair the suffix is not used.
-/
