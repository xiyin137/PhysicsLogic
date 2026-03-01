# Appendix L: Spinor conventions in general dimensions

- Status: initial extraction complete
- Source page start: 763
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/Symmetries/Spinors.lean`, `PhysicsLogic/QFT/BV/*`

## Reading Summary
- Constructs Lorentz spinor representations from Clifford generators and fermionic creation/annihilation combinations in even dimensions, with recursive gamma-matrix realization and chirality decomposition.
- States Lorentz-generator realization `Sigma^{mu nu} = -(i/2) Gamma^{mu nu}` and its algebra, then analyzes reality constraints via `B_1, B_2` matrices and mod-8 conditions for Majorana and Majorana-Weyl spinors.
- Introduces charge conjugation matrix relation `C Gamma^mu C^{-1} = -(Gamma^mu)^T` and Lorentz-covariant conjugate bilinears.
- Records explicit 10D Majorana-Weyl conventions (antisymmetric `C`, symmetric lowered/raised gamma blocks, cyclic/Fierz-type identity).
- Records explicit 4D Weyl/Majorana conventions (gamma basis, chirality matrix, index raising/lowering, Majorana-from-Weyl reconstruction, bilinear decomposition) and 3D real-gamma conventions.
- Gives Euclidean spinor conventions including recursive gamma construction, 8D triality-index identities, and 6D `su(4) ~= so(6)` gamma-index relations.

## Candidate Formalization Units
- `CliffordAlgebraRelation`: operator anticommutator interface for gamma matrices.
- `EvenCliffordFockRelation`: even-dimensional oscillator-style spinor construction package.
- `ChiralityEigenspaceDimensions`: chiral/anti-chiral dimension split interface.
- `MajoranaConditionAdmissibleEven` and `MajoranaWeylAdmissible`: mod-8 admissibility interfaces.
- `ChargeConjugationRelation`: `C Gamma C^{-1} = -Gamma^T` interface.
- `So19ConventionPackage`: 10D index and cyclic gamma-identity package.
- `So13ConventionPackage`: 4D gamma-contraction and Majorana/Weyl bilinear relation package.
- `So12ConventionPackage`: 3D real-gamma/symmetric-index convention package.
- `D8TrialityRelations` and `D6Su4GammaIdentity`: Euclidean 8D/6D convention packages.

## Assumption Candidates
- Candidate new `AssumptionId`: `symSpinorCliffordAlgebraRelation`.
- Candidate new `AssumptionId`: `symSpinorEvenCliffordFockRelation`.
- Candidate new `AssumptionId`: `symSpinorChiralityEigenspaceDimensions`.
- Candidate new `AssumptionId`: `symSpinorMajoranaAdmissibleEven`.
- Candidate new `AssumptionId`: `symSpinorMajoranaWeylAdmissible`.
- Candidate new `AssumptionId`: `symSpinorChargeConjugationRelation`.
- Candidate new `AssumptionId`: `symSpinorSo19ConventionPackage`.
- Candidate new `AssumptionId`: `symSpinorSo13ConventionPackage`.
- Candidate new `AssumptionId`: `symSpinorSo12ConventionPackage`.
- Candidate new `AssumptionId`: `symSpinorEuclideanD8TrialityRelations`.
- Candidate new `AssumptionId`: `symSpinorEuclideanD6Su4GammaIdentity`.

## Subsections
- [x] L.1 Spinor representations from the Clifford algebra (p.763)
- [x] L.2 Majorana condition and conjugation (p.764)
- [x] L.3 $so(1,9)$ spinor conventions (p.765)
- [x] L.4 $so(1,3)$ spinor conventions (p.766)
- [x] L.5 $so(1,2)$ spinor conventions (p.767)
- [x] L.6 Euclidean spinors (p.767)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
