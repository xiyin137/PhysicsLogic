# Appendix M: Super-Poincar\'e symmetry

- Status: initial extraction complete
- Source page start: 769
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/Symmetries/SuperPoincare.lean`, `PhysicsLogic/Symmetries/Poincare.lean`

## Reading Summary
- Defines `d`-dimensional extended super-Poincare algebra with central charges, analyzes massless one-particle multiplets, and states state-count/spin-range constraints from supercharge Clifford generators.
- States central-charge BPS bound (`M >= |Z|`) and preserved-supercharge consequence for saturated states.
- Builds 4D `${\cal N}=1` superspace with supercharges/superderivatives, their algebra, and superspace-integral construction of manifestly supersymmetric actions.
- Gives chiral-superfield and vector-superfield constraints/expansions, Wess-Zumino gauge, gauge-covariant field-strength superfields, and superspace actions for Abelian/non-Abelian gauge theories.
- Describes Wilsonian `(non-)renormalization` structure in 4D `${\cal N}=1` gauge theories (holomorphy constraints, one-loop structure, NSVZ relation in canonical normalization).
- Summarizes 4D `${\cal N}=2` gauge-theory organization via `${\cal N}=1` superfields, prepotential constraints, and 3D supersymmetric Chern-Simons-matter constructions including `${\cal N}=3` quartic superpotential relation.

## Candidate Formalization Units
- `NExtendedSuperPoincareRelation`: anticommutator relation for supercharges, momentum, and central charge.
- `MasslessSupermultipletDimension`: massless multiplet state-count relation.
- `BpsBoundSaturation`: BPS bound and saturation-preserved supercharge interface.
- `N1SuperspaceAlgebra`: 4D `${\cal N}=1` superspace `Q/D` anticommutator package.
- `N1ChiralConstraints`: chiral/anti-chiral superfield constraint package.
- `N1VectorGaugeFieldStrengthPackage`: vector-superfield gauge transformation and field-strength invariance interface.
- `N1HolomorphicOneLoopBeta`, `NsvzBetaRelation`: 4D `${\cal N}=1` RG relation interfaces.
- `N2PrepotentialConstraints`: `${\cal N}=2` prepotential-determined `K`/`tau` interface.
- `ThreeDN2SigmaDtermRelation`, `ThreeDN3QuarticSuperpotential`: 3D supersymmetric Chern-Simons-matter reduction interfaces.

## Assumption Candidates
- Candidate new `AssumptionId`: `symSuperPoincareAlgebra`.
- Candidate new `AssumptionId`: `symSuperPoincareMasslessMultipletDimension`.
- Candidate new `AssumptionId`: `symSuperPoincareBpsBound`.
- Candidate new `AssumptionId`: `symSuperspaceN1Algebra4d`.
- Candidate new `AssumptionId`: `symSuperspaceN1ChiralConstraint`.
- Candidate new `AssumptionId`: `symSuperspaceN1VectorFieldStrengthGaugeInvariant`.
- Candidate new `AssumptionId`: `qftSusyN1HolomorphicOneLoopBeta`.
- Candidate new `AssumptionId`: `qftSusyN1NsvzBetaRelation`.
- Candidate new `AssumptionId`: `qftSusyN2PrepotentialConstraints`.
- Candidate new `AssumptionId`: `qftSusy3dN2SigmaDtermRelation`.
- Candidate new `AssumptionId`: `qftSusy3dN3QuarticSuperpotential`.

## Subsections
- [x] M.1 1-particle representations of supersymmetry (p.769)
- [x] M.2 4D ${\cal N}=1$ superspace (p.770)
- [x] M.3 (Non-)renormalization in 4D ${\cal N}=1$ gauge theories (p.774)
- [x] M.4 4D ${\cal N}=2$ gauge theories (p.776)
- [x] M.5 3D supersymmetric gauge theories (p.777)

## Subsubsections
- [x] M.2.1 Chiral superfield (p.771)
- [x] M.2.2 Vector superfield (p.772)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
