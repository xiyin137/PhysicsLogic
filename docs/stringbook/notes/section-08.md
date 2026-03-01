# Section 08: Superstring perturbation theory: explicit computations

- Status: initial extraction complete
- Source page start: 164
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/SuperstringExplicitComputations.lean`

## Reading Summary
- Extracted tree-level PCO contour formulas for superstring amplitudes
  (`superstringtree`) including NS/R-dependent odd-moduli counting in each
  chirality and normalization `i^(n-3)` for genus-zero amplitudes.
- Extracted NSNS picture-raising and integrated-vertex conversion relations
  (`raisedfixedvop`, `ccgunfix`), including safe PCO-collision limits and
  conversion to integrated matter superdescendants.
- Extracted tree-level massless NSNS and RR 4-point structures:
  NSNS (`nsampexft`, `knstens`, `teightdef`, `gammalowp`) and RR
  (`rrampsg`, `krtens`), with common gamma-ratio momentum dependence.
- Extracted low-energy matching to type-II supergravity and effective couplings:
  `kappa=(pi/2) g_s` (`typeiigskap`), supergravity pole
  (`sugrafouramp`), and `alpha'^3 R^4`-type correction (`typeiieffbos`).
- Extracted genus-one NSNS setup and spin-structure handling
  (`aonegsuperns`, `oneloopzeropic`, `oddscont`, `oddscontbb`,
  `freefertoru`, `zepstaus`, `fermionzmspl`, `oddcora`, `zeromodcalc`),
  including vanishing identities for low multiplicity (`jacidoneloo`,
  `thetasids`) and explicit nonzero 4-point result (`fournsoneloop`,
  `onelooprfou`).
- Extracted genus-one amplitudes with Ramond states
  (`termsineta`, `onelooprr`, `ramondcorrtor`, `ramthetaid`,
  `onelooprrsimp`), including theta-function spurious-singularity loci and
  spin-structure simplifications.
- Extracted higher-genus ghost correlator technology (`sigmeeeage`,
  `bclambdform`, `bcbasic`, `xietacorr`, plus Abel-Jacobi/theta/prime-form
  definitions) and higher-loop vacuum/coupling-function constraints
  (`vacuumgenustwo`, `omegacorrvac`, `insertjj`, `omomfina`,
  `nsnsfgen`, `fstalpha`).

## Candidate Formalization Units
- `TreeLevelSuperstringPcoPackage`
- `NsnsPictureRaisingPackage`
- `NsnsThreePointSupergravityPackage`
- `NsnsFourPointTreePackage`
- `FourPointLowEnergyExpansionPackage`
- `RrFourPointTreePackage`
- `OneLoopNsnsSpinStructurePackage`
- `OneLoopNsnsLowMultiplicityVanishingPackage`
- `OneLoopNsnsFourPointPackage`
- `OneLoopRrFourPointPackage`
- `HigherGenusGhostCorrelatorPackage`
- `HigherLoopVacuumVanishingPackage`
- `FourGravitonCouplingFunctionPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringSuperExplicitTreeLevelPcoAmplitude`.
- Candidate new `AssumptionId`: `stringSuperExplicitNsnsPictureRaising`.
- Candidate new `AssumptionId`: `stringSuperExplicitNsnsThreePointSupergravity`.
- Candidate new `AssumptionId`: `stringSuperExplicitNsnsFourPointTreeKernel`.
- Candidate new `AssumptionId`: `stringSuperExplicitFourPointLowEnergyExpansion`.
- Candidate new `AssumptionId`: `stringSuperExplicitRrFourPointTreeKernel`.
- Candidate new `AssumptionId`: `stringSuperExplicitOneLoopNsnsSpinStructure`.
- Candidate new `AssumptionId`: `stringSuperExplicitOneLoopNsnsVanishingLowMultiplicity`.
- Candidate new `AssumptionId`: `stringSuperExplicitOneLoopNsnsFourPointLeading`.
- Candidate new `AssumptionId`: `stringSuperExplicitOneLoopRrFourPoint`.
- Candidate new `AssumptionId`: `stringSuperExplicitHigherGenusGhostCorrelators`.
- Candidate new `AssumptionId`: `stringSuperExplicitHigherLoopVacuumVanishing`.
- Candidate new `AssumptionId`: `stringSuperExplicitFourGravitonCouplingFunction`.

## Subsections
- [x] 8.1 Tree-level superstring amplitudes (p.164)
- [x] 8.2 One-loop amplitudes of (NS,NS) states (p.169)
- [x] 8.3 One-loop amplitudes involving Ramond states (p.174)
- [x] 8.4 Ghost correlators on a higher genus surface (p.176)
- [x] 8.5 Higher loop superstring amplitudes (p.180)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
