# Appendix I: Lagrangian description of 2D CFTs

- Status: initial extraction complete
- Source page start: 733
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/SigmaModels.lean`, `PhysicsLogic/StringTheory/Backgrounds.lean`

## Reading Summary
- Derives nonlinear-sigma-model Weyl anomaly in dimensional regularization/minimal subtraction, with hatted beta-coefficient combinations controlling trace anomaly terms.
- Presents conformal sigma-model examples including WZW backgrounds and cigar/bell geometries from one-loop Weyl-invariance conditions.
- Derives Buscher T-duality rules by introducing an auxiliary 1-form, enforcing closure/period quantization, integrating out fields, and tracking functional-determinant-induced dilaton shift.
- Connects gauged WZW constructions to coset-model sigma-model limits via integrating out gauge fields and induced dilaton profiles.
- Develops Liouville CFT as a marginal deformation (`Q=b+1/b`), with degenerate-field bootstrap recursion and DOZZ-type structure-constant solution constraints.

## Candidate Formalization Units
- `NlsmWeylAnomalyVanishing`: hatted beta-coefficient vanishing interface at conformal points.
- `BuscherRules`: metric/B-field/dilaton transformation interface for circle isometry dualization.
- `GaugedWzwCosetFlow`: IR flow relation from gauged WZW to coset CFT interfaces.
- `LiouvilleMarginalityData`: relation between `Q,b` and central charge.
- `LiouvilleDozzRecursion`: degenerate-insertion recursion constraints for Liouville structure constants.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dNlsmWeylAnomalyVanishing`.
- Candidate new `AssumptionId`: `cft2dBuscherRules`.
- Candidate new `AssumptionId`: `cft2dGaugedWzwCosetFlow`.
- Candidate new `AssumptionId`: `cft2dLiouvilleMarginality`.
- Candidate new `AssumptionId`: `cft2dLiouvilleDozzRecursion`.

## Subsections
- [x] I.1 Weyl anomaly in the nonlinear sigma model (p.733)
- [x] I.2 Some conformal nonlinear sigma models (p.735)
- [x] I.3 Buscher rules of T-duality (p.736)
- [x] I.4 Gauged WZW and coset models (p.738)
- [x] I.5 Liouville CFT (p.739)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
