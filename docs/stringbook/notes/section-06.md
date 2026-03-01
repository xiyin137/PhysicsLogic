# Section 06: Quantization of superstrings

- Status: initial extraction complete
- Source page start: 117
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/SuperstringQuantization.lean`

## Reading Summary
- Extracted the super-Polyakov worldsheet action and local gauge symmetries:
  local worldsheet supersymmetry (`superp`, `localsusyws`) and super-Weyl
  invariance (`supweyl`), plus conformal-gauge reduction to the free
  `(X, psi)` CFT (`freezpsiact`, `stresstensorfreexpsi`).
- Extracted the superconformal ghost system construction:
  `beta-gamma` action in flat gauge and OPE/current data
  (`sbetagamflat`, `bgamsingope`, `ghostsupercurr`), with
  `c_bc=-26`, `c_beta_gamma=11`, and total ghost central charge `-15`.
- Extracted picture-number structure and bosonization dictionary
  (`bcdict`, `hprimapl`) including NS canonical picture `-1`,
  Ramond canonical picture `-1/2`, and genus-dependent anomaly in `beta-gamma`
  charge.
- Extracted chiral GSO projection and type-II choices (`iiaiibgso`) and
  their role in modular-invariant worldsheet sectors.
- Extracted BRST superfield/current formulas and mode relations
  (`qbsuperfields`, `brstcurpp`, `jbrstbetgams`, `jbrstetaxis`,
  `qblsuper`, `qabbetag`), including the critical-dimension nilpotency
  condition.
- Extracted physical-state conditions as BRST cohomology with Siegel/`beta_0`
  constraints (`siegelsupq`, `betasiegel`) and OCQ representatives
  (`calvsuper`, `vrsuperocq`).
- Extracted mass-shell and massless-spectrum formulas
  (`supersmash`, `emunusuper`, `fthethe`, `kgammaspaeom`, `falphaind`,
  `gauginovert`, `sustertrans`, `uzetagauge`) for `(NS,NS)`, `(R,R)`,
  and mixed fermionic sectors.
- Extracted spacetime-supersymmetry-current and algebra relations
  (`stsusycurrents`, `qalphaminsh`, `susyope`, `susyalgaa`, `susyalgab`)
  up to picture-raising.

## Candidate Formalization Units
- `SuperPolyakovGaugePackage`
- `SuperconformalGhostPackage`
- `PictureNumberPackage`
- `TypeIIGsoProjectionPackage`
- `SuperBRSTCurrentPackage`
- `SuperBRSTNilpotentInCriticalDimension`
- `SuperstringSiegelConstraintPackage`
- `SuperstringPhysicalCohomologyPackage`
- `SuperstringOcqRepresentativePackage`
- `SuperstringMassSpectrumPackage`
- `SuperstringMasslessSectorPackage`
- `SpacetimeSupersymmetryAlgebraPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringSuperstringPolyakovGaugePackage`.
- Candidate new `AssumptionId`: `stringSuperstringGhostSystemPackage`.
- Candidate new `AssumptionId`: `stringSuperstringPictureNumberPackage`.
- Candidate new `AssumptionId`: `stringSuperstringTypeIIGsoProjection`.
- Candidate new `AssumptionId`: `stringSuperstringBrstCurrentPackage`.
- Candidate new `AssumptionId`: `stringSuperstringBrstNilpotencyCritical`.
- Candidate new `AssumptionId`: `stringSuperstringSiegelConstraintPackage`.
- Candidate new `AssumptionId`: `stringSuperstringPhysicalCohomologyPackage`.
- Candidate new `AssumptionId`: `stringSuperstringOcqRepresentativePackage`.
- Candidate new `AssumptionId`: `stringSuperstringMassSpectrumPackage`.
- Candidate new `AssumptionId`: `stringSuperstringMasslessSectorPackage`.
- Candidate new `AssumptionId`: `stringSuperstringSpacetimeSusyAlgebra`.

## Subsections
- [x] 6.1 Supersymmetric extension of Polyakov's action (p.117)
- [x] 6.2 The superconformal ghost system (p.119)
- [x] 6.3 The space of ghost states and picture number (p.121)
- [x] 6.4 The Gliozzi-Scherk-Olive projection (p.124)
- [x] 6.5 BRST symmetry (p.129)
- [x] 6.6 The physical superstring states (p.131)

## Subsubsections
- [x] 6.4.1 Neveu-Schwarz and Ramond sectors of the matter CFT (p.124)
- [x] 6.4.2 Chiral GSO projection (p.126)
- [x] 6.4.3 Modular invariance on the torus (p.127)
- [x] 6.4.4 Type IIA and IIB GSO projection (p.129)
- [x] 6.6.1 Light cone and OCQ representation (p.132)
- [x] 6.6.2 The superstring spectrum (p.133)
- [x] 6.6.3 Spacetime supersymmetry (p.135)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
