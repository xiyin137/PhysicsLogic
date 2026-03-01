# Appendix A: Frequently used formulae and conventions

- Status: initial extraction complete
- Source page start: 651
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/Conventions.lean`

## Reading Summary
- Appendix A is a conventions index tying together normalization and parameter
  dictionaries used throughout string perturbation theory, D-brane physics, and
  M-theory/AdS-CFT duality formulas.
- Bosonic normalization package includes
  `N_{h,n} = g_s^(n+2h-2)` and sphere normalization `K_{S^2} = 8π/κ^2`.
- Cross-theory coupling conversions include:
  - bosonic `κ = 2π g_s`
  - type-II `κ = (π/2) g_s`
  - heterotic `κ = π g_s`
  - heterotic `g_YM = 2π g_s/sqrt(α') = 2κ/sqrt(α')`
- D-brane conventions include bosonic open/closed map `g_s = g_o^2` and Dp
  tensions in open-string and `κ` normalizations; type-II Dp tensions use
  `T_p = (sqrt(π)/κ)(4π^2 α')^((3-p)/2)`.
- Type-II dimensionless couplings are indexed by D1/D0 tensions and mapped to
  `κ` and `g_s` normalizations.
- M-theory dictionary includes `κ_11^2` relations to `α'`, `g_A`, and `M_11`,
  plus membrane/fivebrane tensions
  `T_M2 = M_11^3/(2π)^2`, `T_M5 = M_11^6/(2π)^5`.
- Appendix formulas cross-feed the QFT and holography lanes through shared
  coupling/normalization conventions.

## Candidate Formalization Units
- `BosonicNormalizationConventionPackage`
- `GravitationalCouplingConventionPackage`
- `BosonicDbraneTensionConventionPackage`
- `TypeIIDbraneTensionConventionPackage`
- `TypeIIDimensionlessCouplingConventionPackage`
- `MTheoryScaleTensionConventionPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringConventionsBosonicNormalizationPackage`.
- Candidate new `AssumptionId`: `stringConventionsGravitationalCouplingRelations`.
- Candidate new `AssumptionId`: `stringConventionsBosonicDpTensionRelations`.
- Candidate new `AssumptionId`: `stringConventionsTypeIIDpTensionRelation`.
- Candidate new `AssumptionId`: `stringConventionsTypeIIDimensionlessCouplings`.
- Candidate new `AssumptionId`: `stringConventionsMTheoryScaleTensionRelations`.

## Subsections
- (none listed in TOC)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
