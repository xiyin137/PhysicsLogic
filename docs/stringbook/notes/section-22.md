# Section 22: D1-D5 system and AdS$_3$/CFT$_2$

- Status: initial extraction complete
- Source page start: 507
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/AdS3CFT2.lean`
- QFT target: `PhysicsLogic/QFT/CFT/TwoDimensional/ConformalManifolds.lean`
- QFT target: `PhysicsLogic/QFT/CFT/TwoDimensional/CurrentAlgebras.lean`
- Cross-lane bridge target: `PhysicsLogic/StringTheory/AdS3CFTBridge.lean`

## Reading Summary
- Derives the low-energy D1-D5 gauge-theory description, emphasizing Coulomb vs
  Higgs branches, FI-induced lifting of the Coulomb branch, and the ADHM
  relation to instanton moduli.
- Connects D1/D5 charges to instanton number (`n=Q1` on `T^4`,
  `n=Q1+Q5` on K3), and records moduli-space dimensions and central-charge
  matching `c=6Q1Q5`.
- Develops the near-horizon decoupling geometry `AdS_3 x S^3 x M_4`,
  conformal-manifold/U-duality structure, and attractor relation for axion-dilaton
  data.
- Identifies the role of the symmetric-product orbifold CFT locus and its
  relation to FI/B-field/RR deformations.
- Formalizes bosonic AdS3 WZW/current-algebra/spectral-flow data, including
  representation ranges and mass-shell relations.
- Extends to superstrings in purely `(NS,NS)` flux with
  `hatSL(2)_k x hatSU(2)_k x M_4`, then tracks mixed `(NS,NS)`/`(R,R)` flux
  deformation, RR-deformation SFT recursion, and semiclassical/quantum
  mass-shift relations.

## Candidate Formalization Units
- `D1D5InstantonChargeMap`
- `D1D5BranchStructurePackage`
- `D1D5InstantonModuliDimensionPackage`
- `D1D5NearHorizonPackage`
- `D1D5CentralChargePackage`
- `D1D5ConformalManifoldPackage`
- `D1D5SymmetricOrbifoldPackage`
- `AdS3BosonicWZWLevelRadiusRelation`
- `AdS3BosonicSpectralFlowPackage`
- `AdS3BosonicPhysicalSpectrumPackage`
- `AdS3BosonicMassShellPackage`
- `AdS3NSNSSuperstringBackgroundPackage`
- `AdS3NSNSSuperstringMassShellPackage`
- `AdS3MixedFluxPackage`
- `AdS3MixedFluxLongStringTransitionPackage`
- `AdS3MixedFluxPulsatingPackage`
- `AdS3MixedFluxPulsatingThresholdPackage`
- `AdS3MixedFluxSftRrDeformationPackage`
- `AdS3MixedFluxMassShiftFromFourPointPackage`
- `AdS3MixedFluxFiniteKWzwFourPointReductionPackage`
- `AdS3MixedFluxWzwOpeStructureConstantPackage`
- `AdS3MixedFluxRrTwoStringBracketPackage`
- `D1D5ConformalManifoldGeometryPackage` (QFT lane)
- `D1D5AttractorTauGamma0Package` (QFT lane)
- `D1D5SymmetricProductOrbifoldLocusPackage` (QFT lane)
- `D1D5ConformalGeometryBridgePackage`
- `D1D5AttractorBridgePackage`
- `D1D5SymmetricOrbifoldBridgePackage`
- `AdS3Sl2BosonicWzwLevelRadiusRelation` (QFT lane)
- `AdS3Sl2SpectralFlowAutomorphism` (QFT lane)
- `AdS3Sl2RepresentationSpectrumPackage` (QFT lane)
- `AdS3Sl2MassShellEnergyRelation` (QFT lane)
- `AdS3NsnsWorldsheetMatterScftPackage` (QFT lane)
- `AdS3NsnsAffineLevelShiftPackage` (QFT lane)
- `AdS3NsnsSpinFieldGsoConstraintPackage` (QFT lane)
- `AdS3NsnsSl2SpectralFlowAutomorphism` (QFT lane)
- `AdS3NsnsSuperstringMassShellBpsPackage` (QFT lane)
- `AdS3MixedFluxWorldsheetDeformationPackage` (QFT lane)
- `AdS3MixedFluxPulsatingSpectrumPackage` (QFT lane)
- `AdS3MixedFluxPulsatingThresholdCftPackage` (QFT lane)
- `AdS3MixedFluxSftRrDeformationCftPackage` (QFT lane)
- `AdS3MixedFluxMassShiftFromFourPointCftPackage` (QFT lane)
- `AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage` (QFT lane)
- `AdS3MixedFluxWzwOpeStructureConstantCftPackage` (QFT lane)
- `AdS3MixedFluxRrTwoStringBracketCftPackage` (QFT lane)
- `AdS3BosonicWzwBridgePackage`
- `AdS3SpectralMassShellBridgePackage`
- `AdS3NsnsWorldsheetBridgePackage`
- `AdS3NsnsGsoBridgePackage`
- `AdS3NsnsMassShellBridgePackage`
- `AdS3MixedFluxBridgePackage`
- `AdS3MixedFluxPulsatingThresholdBridgePackage`
- `AdS3MixedFluxLongStringTransitionBridgePackage`
- `AdS3MixedFluxSftMassShiftBridgePackage`
- `AdS3MixedFluxFiniteKWzwReductionBridgePackage`
- `AdS3MixedFluxWzwOpeConstantBridgePackage`
- `AdS3MixedFluxRrTwoStringBracketBridgePackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringAdS3D1D5InstantonChargeMap`.
- Candidate new `AssumptionId`: `stringAdS3D1D5BranchStructure`.
- Candidate new `AssumptionId`: `stringAdS3D1D5InstantonModuliDimension`.
- Candidate new `AssumptionId`: `stringAdS3D1D5NearHorizonGeometry`.
- Candidate new `AssumptionId`: `stringAdS3D1D5CentralCharge`.
- Candidate new `AssumptionId`: `stringAdS3D1D5ConformalManifoldUduality`.
- Candidate new `AssumptionId`: `stringAdS3D1D5SymmetricOrbifoldLocus`.
- Candidate new `AssumptionId`: `stringAdS3BosonicWzwLevelRadius`.
- Candidate new `AssumptionId`: `stringAdS3BosonicSpectralFlow`.
- Candidate new `AssumptionId`: `stringAdS3BosonicPhysicalSpectrum`.
- Candidate new `AssumptionId`: `stringAdS3BosonicMassShell`.
- Candidate new `AssumptionId`: `stringAdS3NsnsSuperstringWorldsheet`.
- Candidate new `AssumptionId`: `stringAdS3NsnsSuperstringMassShell`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxParameterization`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxLongStringSpectrumTransition`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxPulsatingShift`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxPulsatingThresholdPole`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxSftRrDeformation`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxMassShiftFromFourPoint`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxFiniteKWzwFourPointReduction`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxWzwOpeStructureConstants`.
- Candidate new `AssumptionId`: `stringAdS3MixedFluxRrTwoStringBracketStructure`.
- Candidate new `AssumptionId`: `cft2dD1D5ConformalManifoldQuaternionicQuotient`.
- Candidate new `AssumptionId`: `cft2dD1D5AttractorTauGamma0Level`.
- Candidate new `AssumptionId`: `cft2dD1D5SymmetricProductOrbifoldLocus`.
- Candidate new `AssumptionId`: `cft2dAds3BosonicWzwLevelRadius`.
- Candidate new `AssumptionId`: `cft2dAds3Sl2SpectralFlowAutomorphism`.
- Candidate new `AssumptionId`: `cft2dAds3Sl2RepresentationSpectrum`.
- Candidate new `AssumptionId`: `cft2dAds3Sl2MassShellEnergyRelation`.
- Candidate new `AssumptionId`: `cft2dAds3NsnsWorldsheetMatterScft`.
- Candidate new `AssumptionId`: `cft2dAds3NsnsAffineLevelShift`.
- Candidate new `AssumptionId`: `cft2dAds3NsnsSpinFieldGsoConstraints`.
- Candidate new `AssumptionId`: `cft2dAds3NsnsSl2SpectralFlowAutomorphism`.
- Candidate new `AssumptionId`: `cft2dAds3NsnsSuperstringMassShellBps`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxWorldsheetDeformation`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxPulsatingSpectrumShift`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxPulsatingThresholdPole`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxSftRrDeformation`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxMassShiftFromFourPoint`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxFiniteKWzwFourPointReduction`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxWzwOpeStructureConstants`.
- Candidate new `AssumptionId`: `cft2dAds3MixedFluxRrTwoStringBracketStructure`.

## Subsections
- [x] 22.1 The D1-D5 system and its low energy effective theory (p.507)
- [x] 22.2 Supergravity description and the decoupling limit (p.512)
- [x] 22.3 The conformal manifold and U-duality (p.514)
- [x] 22.4 The role of the symmetric product orbifold CFT (p.517)
- [x] 22.5 Bosonic strings in AdS$_3$ (p.520)
- [x] 22.6 Superstrings in purely (NS,NS) AdS$_3\times S^3\times M_4$ (p.527)
- [x] 22.7 The effect of RR flux (p.532)

## Subsubsections
- [x] 22.5.1 Current algebra and spectral flow (p.521)
- [x] 22.5.2 Short and long strings (p.523)
- [x] 22.5.3 Physical string spectrum (p.525)
- [x] 22.6.1 The worldsheet SCFT and GSO projection (p.527)
- [x] 22.6.2 Spectral flow of the supersymmetric $\setbox \z@ \hbox {\mathsurround \z@ $\textstyle {SL}(2)_k$}\mathaccent "0362{{SL}(2)_k}$ (p.530)
- [x] 22.6.3 Superstring spectrum (p.530)
- [x] 22.7.1 Semi-classical limit (p.533)
- [x] 22.7.2 String field theory description of the RR flux deformation (p.534)
- [x] 22.7.3 RR flux correction to superstring spectrum (p.537)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
