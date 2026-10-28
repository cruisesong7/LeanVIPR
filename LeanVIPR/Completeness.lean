module

public import LeanVIPR.Completeness.FourierMotzkin
public import LeanVIPR.Completeness.FarkasCompleteness
public import LeanVIPR.Completeness.ViprCompleteness
public import LeanVIPR.Completeness.ViprRuleComplete
public import LeanVIPR.Completeness.BoundedCompleteness
public import LeanVIPR.Completeness.RefTreeCompile
public import LeanVIPR.Completeness.NormalizationCompile
public import LeanVIPR.Completeness.IntegerProjection
public import LeanVIPR.Completeness.ProjectionCompile
public import LeanVIPR.Completeness.GeneralCompleteness
public import LeanVIPR.Completeness.OneDimensionalCompleteness
public import LeanVIPR.Completeness.ChvatalGomory
public import LeanVIPR.Completeness.FiniteRankCriterion
public import LeanVIPR.Completeness.ValidInequalityCompleteness
public import LeanVIPR.Completeness.FinitePolyhedron
public import LeanVIPR.Completeness.RecessionMonoid
public import LeanVIPR.Completeness.AffineMonoid
public import LeanVIPR.Completeness.IntegerHull
public import LeanVIPR.Completeness.PolyhedralProjection
public import LeanVIPR.Completeness.IntegerHullTargets
public import LeanVIPR.Completeness.AffineHyperplaneRank
public import LeanVIPR.Completeness.RankTransport
public import LeanVIPR.Completeness.RankAssembly
public import LeanVIPR.Completeness.RankBaseCases
public import LeanVIPR.Completeness.RecessionObjective
public import LeanVIPR.Completeness.IntegerObjective
public import LeanVIPR.Completeness.IntegerSupportFace
public import LeanVIPR.Completeness.IntegerHullSupport
public import LeanVIPR.Completeness.SupportDimension
public import LeanVIPR.Completeness.RankInvariance

@[expose] public section

/-!
# Completeness development

This umbrella module collects the mathematical completeness construction and
its compilation into concrete VIPR certificates. The executable checker,
soundness, termination, and complexity developments remain under
`LeanVIPR.Cert`.
-/
