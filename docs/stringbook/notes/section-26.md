# Section 26: Matrix Theory

- Status: initial extraction complete
- Source page start: 636
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/MatrixTheory.lean`

## Reading Summary
- Section 26 develops Matrix Theory in two connected tracks: BFSS matrix quantum
  mechanics as a candidate nonperturbative definition of M-theory (in the
  infinite-momentum/DLCQ framing), and matrix string theory from 2D
  `N=(8,8)` SYM.
- BFSS side:
  - D0 uplift to compactified pp-wave geometry with harmonic profile
    `f0(r)=1+c0 N/r^7` and near-horizon form `~ c0 N/r^7`.
  - Near-extremal black-hole thermodynamics gives explicit Hawking temperature
    and entropy scaling laws in canonical and microcanonical ensembles.
  - Asymptotic D0-bound-state kinematics map to supergraviton momenta, and the
    BFSS conjecture equates reduced M-theory amplitudes with large-`N` MQM
    reduced amplitudes.
- Matrix-string side:
  - Via S/T duality chain, type IIA compactified pp-wave is related to 2D
    `N=(8,8)` SYM with coupling relation `g_A = 1/(sqrt(2π) g_YM R)`.
  - IR fixed point is the symmetric-product orbifold
    `Sym^N(R^8)` with twisted sectors labeled by cycle partitions.
  - Leading irrelevant deformation is the DVV twist field (dimension `(3/2,3/2)`),
    preserving `(8,8)` supersymmetry.
  - Conformal perturbation theory reproduces leading string joining/splitting
    amplitude structure, including covering-map anomaly factor and
    `k_i^+ = N_i` identification; this motivates the full matrix-string
    large-`N` amplitude conjecture.

## Candidate Formalization Units
- `BFSSUpliftParameterPackage`
- `BFSSNearHorizonPackage`
- `BFSSBlackHoleThermalPackage`
- `BFSSMicrocanonicalEntropyPackage`
- `BFSSMomentumMapPackage`
- `BFSSSmatrixConjecturePackage`
- `MatrixStringGaugeCouplingPackage`
- `MatrixStringSymmetricOrbifoldPackage`
- `DVVTwistDeformationPackage`
- `DVVCoefficientNormalizationPackage`
- `MatrixStringTreeAmplitudePackage`
- `MatrixStringLargeNConjecturePackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringMatrixBfssUpliftParameters`.
- Candidate new `AssumptionId`: `stringMatrixBfssNearHorizonDuality`.
- Candidate new `AssumptionId`: `stringMatrixBfssBlackHoleThermodynamics`.
- Candidate new `AssumptionId`: `stringMatrixBfssMicrocanonicalEntropyScaling`.
- Candidate new `AssumptionId`: `stringMatrixBfssMomentumMap`.
- Candidate new `AssumptionId`: `stringMatrixBfssSmatrixConjecture`.
- Candidate new `AssumptionId`: `stringMatrixGaugeCouplingDuality`.
- Candidate new `AssumptionId`: `stringMatrixSymmetricOrbifoldIrLimit`.
- Candidate new `AssumptionId`: `stringMatrixDvvTwistDeformation`.
- Candidate new `AssumptionId`: `stringMatrixDvvCoefficientNormalization`.
- Candidate new `AssumptionId`: `stringMatrixTreeAmplitudeMatching`.
- Candidate new `AssumptionId`: `stringMatrixStringConjectureLargeN`.

## Subsections
- [x] 26.1 M-theory and the D0-brane quantum mechanics (p.636)
- [x] 26.2 Thermodynamics of the D0-brane quantum mechanics (p.637)
- [x] 26.3 The M-theory S-matrix: a conjecture (p.638)
- [x] 26.4 Matrix string theory (p.640)

## Subsubsections
- [x] 26.4.1 The symmetric product orbifold (p.641)
- [x] 26.4.2 The DVV twist field (p.643)
- [x] 26.4.3 String interaction from conformal perturbation theory (p.645)
- [x] 26.4.4 The matrix string theory conjecture (p.649)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
