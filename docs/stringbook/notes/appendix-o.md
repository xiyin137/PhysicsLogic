# Appendix O: Anomalies

- Status: initial extraction complete
- Source page start: 789
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/PathIntegral/Anomalies.lean`, `PhysicsLogic/StringTheory/Anomalies.lean`

## Reading Summary
- Derives the 2D axial anomaly for a massless Dirac fermion in a background `U(1)` field, including the contact-term origin and coefficient `∂_μ j_A^μ = (1/2π) ε^{μν} F_{μν}`.
- Derives the 4D axial anomaly and the chiral gauge anomaly from triangle diagrams with dimensional regularization and chirality-projector structure.
- Analyzes multi-`U(1)` chiral anomalies, local-counterterm ambiguity in `d'_{abc}`, and the ambiguity-free anomaly polynomial `I_6`.
- States the general even-dimensional gauge-anomaly descent relations and the chiral-fermion anomaly-polynomial normalization.
- Develops gravitational anomalies in `d = 4k+2`, including descent-form packaging and the A-hat-genus polynomial form.
- Provides explicit 10D Majorana-Weyl gravitational-anomaly coefficients and applies them to type-IIB and type-I/heterotic anomaly-cancellation structures.

## Candidate Formalization Units
- `TwoDAxialCurrentAnomaly`, `FourDAxialCurrentAnomaly`: coefficient-level axial-current divergence relations.
- `U1ChiralGaugeVariationAnomaly`: 4D chiral `U(1)` effective-action variation relation.
- `MultiU1CubicAnomalyCoefficients`, `MultiU1CountertermShift`: cubic charge coefficients and local-counterterm shift interface.
- `GaugeDescentRelations`, `ChiralFermionGaugeAnomalyPolynomial`: general gauge-descent and anomaly-polynomial interfaces.
- `GravitationalDescentRelations`, `GravitationalAnomalyPolynomial`, `D10MajoranaWeylAnomalyPolynomial`: gravitational anomaly interfaces including explicit 10D MW coefficients.
- `TypeIIBAnomalyCancellation`, `TypeIHeteroticFactorizedAnomaly`, `GreenSchwarzCancellation`: superstring anomaly-cancellation interfaces.

## Assumption Candidates
- Candidate new `AssumptionId`: `qftAnomalyAxial2dCurrentDivergence`.
- Candidate new `AssumptionId`: `qftAnomalyAxial4dCurrentDivergence`.
- Candidate new `AssumptionId`: `qftAnomalyGaugeU1ChiralVariation`.
- Candidate new `AssumptionId`: `qftAnomalyGaugeU1CubicCoefficient`.
- Candidate new `AssumptionId`: `qftAnomalyGaugeU1CountertermShift`.
- Candidate new `AssumptionId`: `qftAnomalyGaugeDescentRelations`.
- Candidate new `AssumptionId`: `qftAnomalyGaugeChiralFermionPolynomial`.
- Candidate new `AssumptionId`: `qftAnomalyGravitationalDescent4kPlus2`.
- Candidate new `AssumptionId`: `qftAnomalyGravitationalAhatPolynomial`.
- Candidate new `AssumptionId`: `qftAnomalyGravitationalD10MwPolynomial`.
- Candidate new `AssumptionId`: `stringAnomalyTypeIibCancellation`.
- Candidate new `AssumptionId`: `stringAnomalyTypeIHeteroticFactorization`.
- Candidate new `AssumptionId`: `stringAnomalyGreenSchwarzCancellation`.

## Subsections
- [x] O.1 Axial anomaly (p.789)
- [x] O.2 Gauge anomaly (p.792)
- [x] O.3 Gravitational anomaly (p.794)
- [x] O.4 Anomaly cancellation in superstring theories (p.799)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
