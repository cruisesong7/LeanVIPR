module

public import LeanVIPR.Impl.Number
public import LeanVIPR.Impl.Parser
public import LeanVIPR.Impl.Form
public import LeanVIPR.Impl.Rules
public import LeanVIPR.Impl.Solution
public import LeanVIPR.Impl.Checker

@[expose] public section

/-!
# The implementation

The executable artifacts, and the only things in the development whose correctness is in
question. Each is proved against `LeanVIPR.Spec` in `LeanVIPR.Thm`; none of it needs to
be read to know what LeanVIPR accepts.

| file | does |
|---|---|
| `Impl.Number`, `Impl.Parser` | read a file into the AST, and validate its indices |
| `Impl.Form`, `Impl.Rules` | decide the side conditions of each VIPR rule |
| `Impl.Solution` | decide the `SOL` section and `{ sol }` justifications |
| `Impl.Checker` | replay a certificate with an array-backed pool |

The `B` suffix on a definition here means it is the `Bool`-valued decision procedure for
a declarative notion of the same name in `LeanVIPR.Spec` — `absurdB` for `Absurd`,
`stepValidB` for `StepValid`. Where there is no such pair the suffix is not used.
-/
