# Section 23: Strings from ${\cal N}=4$ SYM I: planar integrability and the asymptotic Bethe ansatz

- Status: initial extraction complete
- Source page start: 539
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/AdS5Integrability.lean`

## Reading Summary
- Establishes the one-loop planar `SU(2)` spin-chain map for single-trace operators,
  with Heisenberg Hamiltonian `H_1 = (1/(8 pi^2)) sum_l (1-P_{l,l+1})`, one-magnon
  dispersion, and Bethe-root equations including cyclicity.
- Derives BMN/pp-wave kinematics from AdS charges with
  `P_+ = -mu(Delta-J)`, `P_- = -(Delta+J)/(2 mu R^2)`, and reviews lightcone
  GS quantization yielding massive free worldsheet oscillators plus level matching.
- Uses centrally extended `su(2|2)` symmetry to obtain the exact magnon
  dispersion `E = sqrt(1 + 16 h(lambda)^2 sin^2(p/2))`, with weak-coupling
  matching `h(lambda)=sqrt(lambda)/(4 pi)`.
- Organizes the magnon S-matrix in Zhukovsky variables, highlighting analytic
  unitarity and crossing constraints, and the role of the dressing factor on a
  nontrivial Riemann sheet.
- Summarizes ABA/BES machinery for the cusp anomalous dimension, including
  all-order relation and strong-coupling asymptotics.
- Develops nested Bethe ansatz, Bethe-Yang equations for
  `su(2|2) x su(2|2)`, and bound-state (`Q`-particle) dispersion.

## Candidate Formalization Units
- `OneLoopSpinChainPackage`
- `SingleMagnonDispersionPackage`
- `HeisenbergBetheRootsPackage`
- `BmnPpWaveMapPackage`
- `PpWaveSpectrumPackage`
- `CentrallyExtendedMagnonDispersion`
- `WeakCouplingInterpolatingMapPackage`
- `ZhukovskyVariablesPackage`
- `MagnonSMatrixConsistencyPackage`
- `CuspAnomalousDimensionPackage`
- `CuspStrongCouplingPackage`
- `BetheYangSystemPackage`
- `BoundStateDispersionPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityOneLoopSpinChain`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilitySingleMagnonDispersion`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityHeisenbergBetheRoots`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityBmnPpWaveMap`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityPpWaveSpectrum`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityMagnonDispersion`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityWeakCouplingMap`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityZhukovskyVariables`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilitySMatrixConsistency`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityCuspBesEquation`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityCuspStrongCoupling`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityBetheYangSystem`.
- Candidate new `AssumptionId`: `stringAdS5IntegrabilityBoundStateDispersion`.

## Subsections
- [x] 23.1 Single-trace operators as spin chains (p.539)
- [x] 23.2 The BMN/pp-wave limit (p.543)
- [x] 23.3 The all-order magnon dispersion relation (p.549)
- [x] 23.4 The magnon S-matrix: $su(2|2)$ invariance, analyticity, and crossing (p.553)
- [x] 23.5 The crossing-symmetric dressing factor (p.557)
- [x] 23.6 Asymptotic Bethe ansatz and the cusp anomalous dimension (p.559)
- [x] 23.7 Nested Bethe ansatz (p.564)
- [x] 23.8 Bethe-Yang equations (p.569)
- [x] 23.9 Bound states (p.571)

## Subsubsections
- [x] 23.2.1 GS action in AdS$_5\times S^5$ (p.544)
- [x] 23.2.2 GS action in pp-wave (p.546)
- [x] 23.2.3 Lightcone gauge and the string spectrum in pp-wave (p.548)
- [x] 23.6.1 The $SL(2)$ sector at 1-loop (p.559)
- [x] 23.6.2 The cusp anomalous dimension to all orders (p.561)
- [x] 23.7.1 Level II excitations (p.566)
- [x] 23.7.2 Level II scattering (p.567)
- [x] 23.7.3 Level III (p.568)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
