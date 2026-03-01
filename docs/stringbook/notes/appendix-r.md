# Appendix R: Kinematics of holographic correlators

- Status: initial extraction complete
- Source page start: 816
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/Holography.lean`

## Reading Summary
- Sets up the scalar EAdS/CFT source map with boundary condition `lim_{z->0} z^(Delta-d) phi = phi_0`, using `Delta = d/2 + sqrt((mR)^2 + d^2/4)`.
- Derives the scalar two-point normalization from a cutoff-regulated on-shell action with boundary counterterm, giving coefficient `(2 Delta - d) C_Delta`.
- Extracts the bulk `U(1)` gauge-field dictionary to a conserved boundary current with dimension `Delta_J = d-1`.
- Extracts the bulk graviton dictionary to the CFT stress tensor with dimension `Delta_T = d`, including regularized Einstein-Hilbert + Gibbons-Hawking + local counterterm action package.
- Records tree-level cubic scalar Witten-diagram three-point kinematics with coefficient `-g_3 a_Delta`.
- Introduces Mellin-amplitude representation with constraints `sum_{j != i} delta_ij = Delta_i`, contact-diagram `M = 1`, exchange poles at `Delta + 2k`, and the large-radius Mellin/flat-space transform relation.

## Candidate Formalization Units
- `ScalarStandardBoundaryCondition`
- `ScalarTwoPointFunction`
- `GaugeCurrentDictionary`
- `GravityStressTensorDictionary`
- `RegulatedAdSGravityAction`
- `ScalarCubicWittenThreePoint`
- `MellinConstraintSystem`
- `ContactMellinAmplitudeIsUnity`
- `MellinExchangePoleSeries`
- `MellinFlatSpaceLimitRelation`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringHolographyScalarBoundaryCondition`.
- Candidate new `AssumptionId`: `stringHolographyScalarTwoPointFunction`.
- Candidate new `AssumptionId`: `stringHolographyGaugeCurrentDictionary`.
- Candidate new `AssumptionId`: `stringHolographyGravityStressTensorDictionary`.
- Candidate new `AssumptionId`: `stringHolographyRegulatedGravityAction`.
- Candidate new `AssumptionId`: `stringHolographyWittenCubicThreePoint`.
- Candidate new `AssumptionId`: `stringHolographyMellinConstraints`.
- Candidate new `AssumptionId`: `stringHolographyMellinContactAmplitudeUnity`.
- Candidate new `AssumptionId`: `stringHolographyMellinExchangePoleSeries`.
- Candidate new `AssumptionId`: `stringHolographyMellinFlatSpaceLimit`.

## Subsections
- [x] R.1 The boundary condition on a bulk scalar field (p.816)
- [x] R.2 The two-point function (p.817)
- [x] R.3 Gauge field in AdS (p.818)
- [x] R.4 Gravity in AdS (p.819)
- [x] R.5 Witten diagrams (p.820)
- [x] R.6 Mellin amplitudes (p.821)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
