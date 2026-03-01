# Appendix C: Path integral quantization of gauge theories

- Status: initial extraction complete
- Source page start: 672
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/BV/*`, `PhysicsLogic/QFT/PathIntegral/*`

## Reading Summary
- Derives Faddeev-Popov gauge fixing by inserting a gauge-slice delta functional and determinant, with explicit gauge-group Haar-measure treatment.
- Clarifies the gauge-orbit volume factor and the normalization by `vol(G)` in gauge-invariant path integrals.
- Develops BV quantization for general gauge algebras, including open/on-shell closure and field-dependent structure functions.
- Expands the BV master equation order-by-order in ghost number and identifies the corresponding gauge invariance/Jacobi closure conditions.
- Shows BRST recovery as a special off-shell-closed case and discusses preservation of the quantum BV master equation under Wilsonian mode splitting.

## Candidate Formalization Units
- `GaugeOrbitQuotientPathIntegral`: path-integral quotient by gauge-group volume.
- `FaddeevPopovGaugeSliceData`: gauge condition, FP determinant, and Haar measure interfaces.
- `BVMasterEquationExpansion`: hierarchy of closure/Jacobi constraints from BV master equation.
- `BVGaugeFixingFromFermion`: derivation of gauge-fixed action from gauge-fixing fermion data.
- `WilsonianBVMasterPreservation`: stability of BV master equation under integrating out high modes.

## Assumption Candidates
- Candidate new `AssumptionId`: `bvFaddeevPopovGaugeSliceRegular`.
- Candidate new `AssumptionId`: `bvMasterEquationClosureHierarchy`.
- Candidate new `AssumptionId`: `bvGaugeFixingFermionRecoversBrst`.
- Candidate new `AssumptionId`: `bvWilsonianMasterEquationPreserved`.

## Subsections
- [x] C.1 The Faddeev-Popov ansatz (p.672)
- [x] C.2 Batalin-Vilkovisky quantization of gauge theory (p.673)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
