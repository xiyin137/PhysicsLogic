# Appendix F: Riemann surfaces and modular invariance

- Status: initial extraction complete
- Source page start: 704
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/ModularInvariance.lean`, `PhysicsLogic/QFT/TQFT/*`

## Reading Summary
- Reviews conformal Killing structures on sphere and torus, including `PSL(2,C)` on genus 0 and modular identifications on genus 1.
- Identifies torus moduli as upper half-plane quotient by `PSL(2,Z)` and states the associated large-diffeomorphism equivalence.
- Summarizes genus `h ≥ 2` moduli counting, plumbing-fixture construction, and Schottky/period-matrix parameterizations.
- Describes symplectic basis changes of cycles and period-matrix transformation under `Sp(2h,Z)`.
- Frames modular/crossing consistency of higher-genus correlators via pair-of-pants decompositions and elementary moves.

## Candidate Formalization Units
- `SphereConformalKillingGroup`: `PSL(2,C)` action on genus-0 worldsheet.
- `TorusModularParameterization`: torus modulus with `PSL(2,Z)` equivalence.
- `HigherGenusPlumbingData`: sewing/plumbing interface for genus increase.
- `PeriodMatrixSymplecticTransform`: period-matrix action under `Sp(2h,Z)`.
- `ModularCrossingConsistency`: higher-genus consistency from sphere crossing + torus modular covariance.

## Assumption Candidates
- Candidate new `AssumptionId`: `riemannSurfaceModuliPlumbingCoordinates`.
- Candidate new `AssumptionId`: `cftTorusOnePointModularCovariance`.
- Candidate new `AssumptionId`: `cftHigherGenusPantsDecompositionConsistency`.

## Subsections
- [x] F.1 The sphere (p.704)
- [x] F.2 The torus (p.705)
- [x] F.3 Genus $h\geq 2$ (p.706)
- [x] F.4 Modular invariance of 2D CFT (p.708)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
