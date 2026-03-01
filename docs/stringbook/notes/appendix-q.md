# Appendix Q: Double-scaled matrix quantum mechanics

- Status: initial extraction complete
- Source page start: 809
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/Euclidean/MatrixQuantumMechanics.lean`

## Reading Summary
- Formulates one-matrix quantum mechanics with canonical matrix-coordinate/momentum commutators and a `U(N)`-invariant Hamiltonian.
- Rewrites the model in eigenvalue/angular variables with Vandermonde redefinition and identifies gauged-singlet reduction to non-interacting identical fermions.
- Specializes to the `c=1` matrix model with inverted harmonic potential and semiclassical Fermi-sea background.
- Introduces collective-field description of Fermi-surface fluctuations, including `λ = sqrt(2μ) cosh τ` and asymptotic massless scalar behavior.
- Records perturbative `1 -> 2` collective-field amplitude and non-perturbative particle-hole reflection formalism.
- Captures leading instanton corrections to `1 -> n` amplitudes and the non-singlet long-string renormalized-energy/integral-equation structure.

## Candidate Formalization Units
- `MatrixCanonicalCommutationRelation`: one-matrix canonical commutator package.
- `MatrixModelSingletReduction`: gauged-singlet/Vandermonde reduction to free-fermion sector.
- `COneInvertedHarmonicPotential`: `c=1` potential relation.
- `COneFermiSeaProfile`: semiclassical Fermi-surface/eigenvalue-density package.
- `CollectiveFieldTauPackage`: `λ-τ` map and interaction-prefactor structure.
- `CollectiveBornOneToTwoAmplitude`: tree-level collective-field amplitude relation.
- `ReflectionHoleRelation`: particle/hole reflection inverse relation.
- `COneInstantonOneToNCorrection`: leading instanton correction package.
- `LongStringRenormalizedEnergyRelation`, `LongStringIntegralEquationRelation`: non-singlet long-string interfaces.

## Assumption Candidates
- Candidate new `AssumptionId`: `qftEuclideanMqmCanonicalCommutation`.
- Candidate new `AssumptionId`: `qftEuclideanMqmSingletReduction`.
- Candidate new `AssumptionId`: `qftEuclideanMqmCOneInvertedPotential`.
- Candidate new `AssumptionId`: `qftEuclideanMqmFermiSeaProfile`.
- Candidate new `AssumptionId`: `qftEuclideanMqmCollectiveTauHamiltonian`.
- Candidate new `AssumptionId`: `qftEuclideanMqmCollectiveBornOneToTwo`.
- Candidate new `AssumptionId`: `qftEuclideanMqmReflectionHoleRelation`.
- Candidate new `AssumptionId`: `qftEuclideanMqmInstantonOneToN`.
- Candidate new `AssumptionId`: `qftEuclideanMqmLongStringRenormalizedEnergy`.
- Candidate new `AssumptionId`: `qftEuclideanMqmLongStringIntegralEquation`.

## Subsections
- [x] Q.1 One-matrix quantum mechanics (p.809)
- [x] Q.2 The $c=1$ MQM (p.810)
- [x] Q.3 Particle-hole scattering and non-perturbative effects in the $c=1$ MQM (p.813)
- [x] Q.4 Non-singlet sector and long string states (p.814)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
