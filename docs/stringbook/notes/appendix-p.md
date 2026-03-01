# Appendix P: Boundary conformal field theory

- Status: initial extraction complete
- Source page start: 801
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/BoundaryCFT.lean`

## Reading Summary
- Establishes conformal boundary conditions in 2D CFT via stress-tensor gluing on the boundary and equality of left/right central charges.
- Organizes boundary operators in strip Hilbert spaces `${\cal H}_{BB'}` with boundary Virasoro generators and fixed two-/three-point function kinematics on UHP/disc.
- Introduces boundary states `|B\rangle`, Ishibashi decomposition, and the bulk one-point / bulk-boundary coefficient relation `R_{i0}=D_{ij}U_B^j`.
- States the cylinder modular-crossing relation between closed-channel propagation of boundary states and open-channel thermal trace.
- Describes direct-sum boundary conditions and Chan-Paton enhancement `${\cal H}_{B^{\oplus n}B^{\oplus m}}\simeq {\cal H}_{BB}\otimes Mat(n,m)` with matrix-unit OPE composition.
- Works out free-boson Neumann/Dirichlet boundary states and normalizations, then free-fermion (Ising, diagonal GSO) Neumann/Dirichlet boundary states and sector content.

## Candidate Formalization Units
- `BoundaryConformalInvariance`: stress-tensor gluing and central-charge matching.
- `BoundaryCorrelatorKinematics`: boundary two-/three-point kinematic constraints and coefficient symmetries.
- `BoundaryStateGluing`, `BulkBoundaryOnePointRelation`: Ishibashi/gluing and `R_{i0}=D_{ij}U_B^j` interfaces.
- `BoundaryCylinderModularDuality`: closed/open channel cylinder duality.
- `ChanPatonFactorization`: Chan-Paton enhancement and matrix-unit multiplication law.
- `FreeBosonNDBoundaryConditions`, `FreeBosonBoundaryStateNormalization`: free-boson N/D boundary packages.
- `FreeFermionNDBoundaryConditions`, `FreeFermionBoundaryStateCoefficients`, `FreeFermionBoundarySectorIdentification`: Ising free-fermion boundary packages.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dBoundaryConformalInvariance`.
- Candidate new `AssumptionId`: `cft2dBoundaryCorrelatorKinematics`.
- Candidate new `AssumptionId`: `cft2dBoundaryStateIshibashiGluing`.
- Candidate new `AssumptionId`: `cft2dBoundaryBulkBoundaryOnePoint`.
- Candidate new `AssumptionId`: `cft2dBoundaryCylinderModularDuality`.
- Candidate new `AssumptionId`: `cft2dBoundaryChanPatonFactorization`.
- Candidate new `AssumptionId`: `cft2dBoundaryFreeBosonNdConditions`.
- Candidate new `AssumptionId`: `cft2dBoundaryFreeBosonNormalization`.
- Candidate new `AssumptionId`: `cft2dBoundaryFreeFermionNdConditions`.
- Candidate new `AssumptionId`: `cft2dBoundaryFreeFermionCoefficients`.
- Candidate new `AssumptionId`: `cft2dBoundaryFreeFermionSectorIdentification`.

## Subsections
- [x] P.1 Conformal boundary conditions (p.801)
- [x] P.2 The boundary state (p.803)
- [x] P.3 Neumann and Dirichlet boundary conditions in the free boson CFT (p.804)
- [x] P.4 Neumann and Dirichlet boundary conditions in a free fermion CFT with diagonal GSO projection (p.807)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
