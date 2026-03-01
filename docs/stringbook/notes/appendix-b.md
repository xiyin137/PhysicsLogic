# Appendix B: The path integral

- Status: initial extraction complete
- Source page start: 654
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/PathIntegral/*`, `PhysicsLogic/QFT/BV/*`

## Reading Summary
- Derives canonical discretized phase-space path integral for quantum mechanics and its Lagrangian form after Gaussian momentum integration.
- Gives the Grassmann/Berezin path integral with second-class constraints, Dirac brackets, and anti-periodic thermal boundary conditions for fermionic variables.
- Develops Euclidean instanton saddle analysis using Morse functions, including steepest-descent equations, one-loop determinants, and zero-mode treatment.
- Uses supersymmetric quantum mechanics to connect Witten index, localization to critical points, and Morse complex/homology interpretation.
- Presents Borel resummation and its limits in the presence of additional saddles, then resolves non-perturbative sectors via contour decomposition into Lefschetz thimbles.

## Candidate Formalization Units
- `DiscretizedPhaseSpacePathIntegral`: finite-step discretization data and continuum limit interface.
- `GrassmannPathIntegralData`: Berezin integration and fermionic boundary-condition structure.
- `InstantonSaddleData`: Euclidean saddles, action suppression, and zero-mode counting interfaces.
- `WittenIndexTopologicalInvariance`: Q-exact deformation invariance of supersymmetric index.
- `BorelResummationData`: Borel transform/reconstruction interface with analyticity conditions.
- `LefschetzThimbleDecomposition`: decomposition of integration cycles into thimbles with integer intersection numbers.

## Assumption Candidates
- Candidate new `AssumptionId`: `pathIntegralDiscretizedContinuumLimit`.
- Candidate new `AssumptionId`: `pathIntegralInstantonSemiclassicalWeight`.
- Candidate new `AssumptionId`: `pathIntegralWittenIndexMorseComplex`.
- Candidate new `AssumptionId`: `pathIntegralBorelSokalWatsonCriterion`.
- Candidate new `AssumptionId`: `pathIntegralLefschetzThimbleExpansion`.

## Subsections
- [x] B.1 Path integral formulation of quantum mechanics (p.654)
- [x] B.2 Path integral with Grassmann-odd field variables (p.655)
- [x] B.3 Tunneling and instantons (p.658)
- [x] B.4 A supersymmetric model (p.659)
- [x] B.5 Borel resummation (p.668)
- [x] B.6 Lefschetz thimbles (p.670)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
