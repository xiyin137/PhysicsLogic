# Appendix D: Local quantum field theories

- Status: initial extraction complete
- Source page start: 676
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/Wightman/*`, `PhysicsLogic/QFT/AQFT/*`, `PhysicsLogic/QFT/CFT/*`

## Reading Summary
- Sets local QFT kinematics through Poincare-covariant local operators, microcausality, and stress-tensor conservation/current charges.
- Defines Wightman correlators and explains Lorentzian/Euclidean analytic continuation with operator-order sensitivity across branch cuts.
- Introduces conformal invariance via traceless stress tensor and corresponding conserved conformal currents.
- Builds OPE using radial-quantization Hilbert-space decomposition on spheres and state/operator correspondence.
- Emphasizes analyticity and convergence conditions needed for inserting OPEs inside correlators.

## Candidate Formalization Units
- `LocalFieldPoincareCovariance`: operator transformation law under Poincare action.
- `MicrocausalityCommutator`: spacelike commutation interface.
- `WightmanToEuclideanContinuation`: analytic continuation interface with ordering constraints.
- `StressTensorConformalCurrents`: tracelessness-to-conformal-current map.
- `RadialQuantizationOPEDecomposition`: Hilbert-space expansion yielding local OPE coefficients.

## Assumption Candidates
- Reuse existing: `wightmanTemperedness`, `wightmanSpinStatistics`, `wightmanPctTheorem`.
- Reuse existing: `aqftGnsExistence`, `aqftReehSchlieder`.
- Candidate new `AssumptionId`: `wightmanEuclideanAnalyticContinuationDomain`.
- Candidate new `AssumptionId`: `cftRadialQuantizationOpeConvergence`.

## Subsections
- [x] D.1 Field operators (p.676)
- [x] D.2 Correlation functions (p.677)
- [x] D.3 Conformal symmetry (p.679)
- [x] D.4 Operator product expansion (p.679)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
