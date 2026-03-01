# Section 04: Bosonic string interactions

- Status: initial extraction complete
- Source page start: 63
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/PerturbativeScattering.lean`

## Reading Summary
- Builds the gauge-fixed perturbative closed-string amplitude on punctured
  Riemann surfaces as a moduli-space integral
  `A_h = N_{h,n} ∫_{M_{h,n}} Ω_{6h-6+2n}` with
  `dim_R(M_{h,n}) = 6h - 6 + 2n`.
- Rewrites the `b`-ghost moduli insertion from Beltrami form to contour form
  using holomorphic transition data and introduces puncture-position moduli that
  strip `c \tilde c` to integrated matter primaries.
- Gives the ghost-number anomaly relation `∇·j_gh = -(3/4)R` and genus-dependent
  ghost-number selection rules.
- Shows BRST variation of the moduli integrand is a total derivative up to
  boundary terms; boundaries correspond to degeneration loci in moduli space.
- Uses plumbing-fixture sewing `z' = q/z` (`|q|<1`) to derive factorization and
  one-particle poles with propagator denominator `(P^2 + M^2 - iε)^{-1}`.
- Fixes perturbative normalization conventions through factorization recursion,
  including `K_{S^2} = 8π/α'`, `N_{h,n}=i^(3h-3+n)`, tachyon normalization, and
  bosonic coupling map `κ = 2π g_s`.
- Extracts tree-level tachyon formulas including Virasoro-Shapiro kernel and
  one-loop torus measure/fundamental-domain structure; includes `c=1` thermal
  one-loop duality check under `R -> α'/R`.

## Candidate Formalization Units
- `ModuliGaugeFixedAmplitudePackage`
- `BeltramiGhostInsertionPackage`
- `GhostNumberAnomalyPackage`
- `BrstBoundaryVariationPackage`
- `PlumbingFixtureDegenerationPackage`
- `TreeUnitarityFactorizationPackage`
- `PerturbativeNormalizationRecursionPackage`
- `VirasoroShapiroAmplitudePackage`
- `OneLoopTorusMeasurePackage`
- `COneThermalDualityPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringPerturbativeGaugeFixedModuliAmplitude`.
- Candidate new `AssumptionId`: `stringPerturbativeBeltramiBInsertion`.
- Candidate new `AssumptionId`: `stringPerturbativeGhostNumberAnomaly`.
- Candidate new `AssumptionId`: `stringPerturbativeBrstBoundaryVariation`.
- Candidate new `AssumptionId`: `stringPerturbativePlumbingFixtureDegeneration`.
- Candidate new `AssumptionId`: `stringPerturbativeTreeUnitarityFactorization`.
- Candidate new `AssumptionId`: `stringPerturbativeNormalizationRecursion`.
- Candidate new `AssumptionId`: `stringPerturbativeVirasoroShapiroKernel`.
- Candidate new `AssumptionId`: `stringPerturbativeOneLoopTorusMeasure`.
- Candidate new `AssumptionId`: `stringPerturbativeCOneThermalDuality`.

## Subsections
- [x] 4.1 Conformal gauge with moduli (p.63)
- [x] 4.2 Reformulation in terms of holomorphic data (p.65)
- [x] 4.3 The ghost number anomaly (p.69)
- [x] 4.4 Boundaries of the moduli space (p.70)
- [x] 4.5 The string S-matrix (p.73)
- [x] 4.6 Consistency with unitarity (p.75)
- [x] 4.7 Tree-level amplitudes in critical bosonic string theory (p.80)
- [x] 4.8 One-loop amplitudes (p.82)
- [x] 4.9 Higher loops (p.85)
- [x] 4.10 Scattering amplitudes in $c=1$ string theory (p.88)

## Subsubsections
- [x] 4.6.1 The plumbing fixture (p.76)
- [x] 4.6.2 Factorization of the string amplitude (p.78)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
