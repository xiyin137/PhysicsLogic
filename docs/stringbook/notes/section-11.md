# Section 11: Heterotic string theory

- Status: initial extraction complete
- Source page start: 209
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/HeteroticStringTheory.lean`

## Reading Summary
- Extracted heterotic worldsheet construction with chiral local supersymmetry,
  `(0,1)` gauge-fixed SCFT, 32 left-moving fermions, and the two chiral-GSO
  realizations of the `c=16` chiral sector (`SO(32)` / `E_8 x E_8`) including
  Narain-lattice descriptions (`hetcovaction`, `sothirtyt`, `sosixtsixt`,
  `allstateshet`).
- Extracted heterotic physical-state package: BRST/Siegel construction, level
  matching and right-moving GSO tachyon removal, 10D `N=1` supersymmetry
  current, and massless supergravity plus gauge multiplets.
- Extracted perturbative amplitude structure where supermoduli and PCO contour
  data apply to the anti-holomorphic sector only (`hetamppres`), with explicit
  tree/loop effective-coupling consequences:
  `kappa = pi g_s`, `g_YM = 2 pi g_s / sqrt(alpha')`, tree-level `R^2` but no
  independent `R^3`, and one-loop parity-odd `B_2 wedge X_8`/`BF^4`
  Green-Schwarz terms (`nsgravthreehet`, `kappahetconvs`, `hetcouprel`,
  `gsmech`, `xeightanom`, `amphetbff`, `gshetcoupbf`).
- Extracted non-BPS `SO(32)` spinor mass-renormalization setup:
  stable `128+128` multiplet, off-shell 1PI framework in heterotic field space,
  and one-loop torus two-point mass shift extraction (`sec:hetmassrenorm`,
  `hzerosuper`, `torusmassrenorm`, `deltamsq`).
- Extracted heterotic background-field `(0,1)` sigma-model with gauge/lorentz
  anomaly compensation via `B`-transformations, gauge-invariant
  `H-hat` and modified Bianchi identity, plus one- and two-loop beta-function
  constraints (`hetsigmasup`, `sacthetcurv`, `banomalfa`, `banomlore`,
  `hwidehath`, `modbianchi`, `bamueq`, `hetbetatwol`).
- Extracted Calabi-Yau-with-gauge-bundle and standard-embedding logic:
  `(0,2)` enhancement, `H-hat` simplification under embedding, 4D `N=1`
  vacua with expected unbroken gauge groups, and torsional Strominger-system /
  Hermitian-Yang-Mills constraints (`hermitianf`, `atomst`, `uonersymhethflux`,
  `hermitcond`, `hthstrom`, `dhthrchern`, `domtor`, `gfhermitym`).
- Extracted quantum-corrected heterotic vacuum analysis:
  4D `N=1` FI/D-term potential from anomalous `U(1)` and dilaton multiplet,
  one-loop FI mass term formula matching worldsheet computation, two-loop
  vacuum energy from genus-two boundary factorization, and shifted-vacuum SUSY
  restoration mechanism (`deltgaugchir`, `vscasupggg`, `deltabanomuone`,
  `luonecompkv`, `tauexpfactsix`, `mvaaf`, `delmaexans`, `massintreshh`,
  `sec:twolooptadpole`, `calatwoff`).

## Candidate Formalization Units
- `HeteroticWorldsheetPackage`
- `HeteroticLambdaGsoPackage`
- `HeteroticSpectrumPackage`
- `HeteroticAmplitudePrescriptionPackage`
- `HeteroticTreeEffectiveCouplingPackage`
- `HeteroticGreenSchwarzPackage`
- `HeteroticNonBpsSpinorMassRenormalizationPackage`
- `HeteroticBackgroundNlsmPackage`
- `HeteroticCalabiYauGaugeBundlePackage`
- `HeteroticStromingerSystemPackage`
- `HeteroticFourDEffectiveTheoryPackage`
- `HeteroticOneLoopFiMassTermPackage`
- `HeteroticTwoLoopVacuumEnergyPackage`
- `HeteroticShiftedVacuumPackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringHeteroticWorldsheetChiralSupersymmetry`.
- Mapped `AssumptionId`: `stringHeteroticLambdaGsoCurrentAlgebras`.
- Mapped `AssumptionId`: `stringHeteroticPhysicalSpectrumCohomology`.
- Mapped `AssumptionId`: `stringHeteroticPerturbativeAmplitudePrescription`.
- Mapped `AssumptionId`: `stringHeteroticTreeLevelEffectiveCouplings`.
- Mapped `AssumptionId`: `stringHeteroticGreenSchwarzAnomalyCoupling`.
- Mapped `AssumptionId`: `stringHeteroticNonBpsSpinorMassRenormalization`.
- Mapped `AssumptionId`: `stringHeteroticBackgroundNlsmGaugeLorentzAnomaly`.
- Mapped `AssumptionId`: `stringHeteroticCalabiYauStandardEmbedding`.
- Mapped `AssumptionId`: `stringHeteroticStromingerSystem`.
- Mapped `AssumptionId`: `stringHeteroticFourDEffectiveFiPotential`.
- Mapped `AssumptionId`: `stringHeteroticOneLoopFiMassTerm`.
- Mapped `AssumptionId`: `stringHeteroticTwoLoopVacuumEnergyFromBoundary`.
- Mapped `AssumptionId`: `stringHeteroticShiftedVacuumSupersymmetryRestoration`.

## Subsections
- [x] 11.1 The worldsheet theory and string spectrum (p.209)
- [x] 11.2 Perturbation theory and spacetime effective theory (p.211)
- [x] 11.3 Mass renormalization (p.218)
- [x] 11.4 Heterotic string in background fields (p.220)
- [x] 11.5 Calabi-Yau compactification with gauge bundle (p.224)
- [x] 11.6 A quantum-corrected heterotic vacuum (p.227)

## Subsubsections
- [x] 11.6.1 The 4D effective theory (p.228)
- [x] 11.6.2 The 1-loop Fayet-Iliopoulos mass term (p.231)
- [x] 11.6.3 The 2-loop vacuum energy (p.236)
- [x] 11.6.4 Shifted vacuum and restoration of supersymmetry (p.240)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
