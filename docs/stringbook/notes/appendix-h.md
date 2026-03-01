# Appendix H: Symmetries, defects, and orbifolds

- Status: initial extraction complete
- Source page start: 723
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/DefectsOrbifolds.lean`, `PhysicsLogic/QFT/TQFT/*`

## Reading Summary
- Uses the Ising minimal model (`c=1/2`) to show explicit crossing constraints from null-vector differential equations, fixing `C_{σσϵ} = 1/2`.
- Develops topological defect lines, fusion rules, junction spaces, and H-junction crossing kernels with pentagon consistency.
- Describes symmetry lines as invertible defects and classifies crossing phases modulo rephasings by `H^3(G,U(1))` ('t Hooft anomaly data).
- Constructs orbifold CFT Hilbert space as the `G`-invariant subspace of defect sectors and emphasizes modular consistency of twisted partition data.
- Presents Narain lattice conditions (integral/even/self-dual) for modular-invariant torus partition functions and cocycle constraints for vertex-operator OPE associativity.

## Candidate Formalization Units
- `IsingSigmaFourPointCrossing`: crossing-constrained Ising spin-field 4-point decomposition.
- `TopologicalDefectFusionData`: simple-line fusion multiplicities and junction consistency interfaces.
- `DefectFusionPentagonConsistency`: H-junction crossing-kernel pentagon relation abstraction.
- `OrbifoldSectorData`: symmetry-line sector decomposition and conjugation action on twisted sectors.
- `NarainLatticeData`: even/self-dual modular invariance interface for Narain-lattice CFT.
- `NarainCocycleAssociative`: associativity condition for lattice cocycle phases in vertex-operator OPE.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dIsingSigmaFourPointCrossing`.
- Candidate new `AssumptionId`: `cft2dDefectFusionPentagon`.
- Candidate new `AssumptionId`: `cft2dOrbifoldConstructionModularInvariant`.
- Candidate new `AssumptionId`: `cft2dNarainEvenSelfDualModularInvariant`.
- Candidate new `AssumptionId`: `cft2dNarainCocycleAssociative`.

## Subsections
- [x] H.1 The Ising CFT (p.723)
- [x] H.2 Topological defect lines (p.725)
- [x] H.3 Orbifolds (p.728)
- [x] H.4 Narain lattice (p.731)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
