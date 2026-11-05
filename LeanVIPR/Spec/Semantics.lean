module

public import LeanVIPR.Spec.Semantics.LinCon
public import LeanVIPR.Spec.Semantics.LinForm
public import LeanVIPR.Spec.Semantics.Row
public import LeanVIPR.Spec.Semantics.Lower
public import LeanVIPR.Spec.Semantics.System
public import LeanVIPR.Spec.Semantics.Claim
public import LeanVIPR.Spec.Semantics.Completeness

@[expose] public section

/-!
# Semantics: what a certificate means

Read in this order:

| file | says |
|---|---|
| `LinCon`, `LinForm`, `Row` | the sparse-row vocabulary everything else is written in |
| `Lower` | which rows and steps a parsed certificate denotes |
| `System` | which derivations over those rows the VIPR proof system admits |
| `Claim` | what a valid certificate therefore asserts about the problem |
| `Completeness` | what completeness of the system *would* mean — open, and not assumed |

`System` is stated over real-valued valuations, not the rationals a certificate is
written in. That is deliberate: a certificate with rational coefficients has to refute
the problem over the reals, because that is the problem a solver claims to have solved.
Rational arithmetic is an implementation concern.

`Claim` is the statement `viprcheck` prints `ACCEPT` for.
-/
