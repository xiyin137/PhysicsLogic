# Appendix E: General properties of 2D CFTs

- Status: initial extraction complete
- Source page start: 682
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/*`

## Reading Summary
- Fixes 2D coordinate conventions and explains holomorphic/anti-holomorphic factorization of conserved stress-tensor components.
- Derives primary transformation laws, stress-tensor OPE with primaries, and finite conformal transformation behavior.
- Builds Virasoro algebra from the `T(z)T(0)` OPE, including central extension, mode expansion, and cylinder energy/momentum shifts.
- Develops Weyl-anomaly logic on curved worldsheets and its relation to contact terms and Polyakov anomaly structure.
- Organizes correlators through conformal Ward identities, Virasoro blocks, crossing, and Zamolodchikov recurrence/analytic continuation.

## Candidate Formalization Units
- `TwoDConformalCoordinateData`: `(z,\bar z)` conventions and chiral decomposition.
- `StressTensorPrimaryOPEData`: primary weights from `T·O` singular terms.
- `VirasoroFromStressTensorOPE`: central extension and mode-commutator interface.
- `CylinderCasimirShift`: relation of `L_0,\tilde L_0` to cylinder energy/momentum with central-charge shift.
- `WeylAnomalyFunctional`: curved-worldsheet Weyl response data.
- `VirasoroBlockRecurrence`: recursion/analytic-continuation interface for conformal blocks.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dStressTensorOPEDefinesVirasoro`.
- Candidate new `AssumptionId`: `cft2dWeylAnomalyPolyakovFunctional`.
- Candidate new `AssumptionId`: `cft2dCrossingAssociativity`.
- Candidate new `AssumptionId`: `cft2dZamolodchikovRecurrenceValidity`.

## Subsections
- [x] E.1 2D conventions (p.682)
- [x] E.2 2D conformal symmetry (p.682)
- [x] E.3 The Virasoro algebra (p.686)
- [x] E.4 Weyl anomaly (p.689)
- [x] E.5 Representations of Virasoro algebra (p.691)
- [x] E.6 Conformal correlators and conformal blocks (p.693)
- [x] E.7 Recurrence formulae and analytic property of conformal blocks (p.698)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
