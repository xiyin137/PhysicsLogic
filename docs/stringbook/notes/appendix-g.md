# Appendix G: 2D free field theories

- Status: initial extraction complete
- Source page start: 712
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/Examples.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional/Virasoro.lean`

## Reading Summary
- Builds the 2D free-boson CFT from canonical mode expansion, normal ordering/OPE regularization, and state-operator map to vertex operators.
- Derives stress-tensor realization for the free boson and confirms Virasoro central charge `c=1`.
- Extends free-boson correlators to torus and higher genus via Green functions, prime forms, period matrices, and momentum-conservation constraints.
- Develops free-fermion quantization with NS/R sector structure, spin fields, and OPE characterization of half-integer spin operators.
- Introduces genus-dependent fermion propagators through Szego kernels for even/odd spin structures; confirms free-fermion central charge `c=1/2`.

## Candidate Formalization Units
- `FreeBosonModeAlgebra2D`: oscillator commutation relations and Fock-state interfaces.
- `NormalOrderedVertexOperators2D`: local-operator construction and OPE singular-part bookkeeping.
- `FreeBosonGenusHCorrelatorData`: correlator interfaces using Green function + period-matrix data.
- `FreeFermionSectorData2D`: NS/R sector decomposition and spin-field interfaces.
- `SzegoKernelSpinStructureData`: fermion propagator interfaces parameterized by spin structure.
- `FreeFieldCentralChargeAssignments`: canonical `c=1` boson and `c=1/2` fermion consistency interfaces.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dFreeBosonVertexOperatorStateMap`.
- Candidate new `AssumptionId`: `cft2dFreeBosonHigherGenusCorrelatorFormula`.
- Candidate new `AssumptionId`: `cft2dFreeFermionNsRSectorConsistency`.
- Candidate new `AssumptionId`: `cft2dSzegoKernelSpinStructurePropagator`.
- Candidate new `AssumptionId`: `cft2dFreeFieldCentralCharges`.

## Subsections
- [x] G.1 Free bosons (p.712)
- [x] G.2 Free boson on a Riemann surface (p.715)
- [x] G.3 Free fermions (p.717)
- [x] G.4 Free fermion on a Riemann surface (p.721)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
