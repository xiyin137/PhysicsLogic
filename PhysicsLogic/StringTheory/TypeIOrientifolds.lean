import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev TypeIOrientifoldClaim := Prop

/-- Unoriented-string worldsheet parity and spectrum-projection data. -/
structure UnorientedWorldsheetParityData where
  orientationReversingDiffeomorphismsGauged : TypeIOrientifoldClaim
  worldsheetParityOmegaDefinedOnCylinderAndPlane : TypeIOrientifoldClaim
  physicalStatesProjectedToOmegaInvariantSubspace : TypeIOrientifoldClaim
  nsnsBFieldProjectedOutByParity : TypeIOrientifoldClaim
  eulerCharacteristicWithCrosscapsUsed : TypeIOrientifoldClaim
  unorientedSurfaceDescribedByOrientedDoubleCover : TypeIOrientifoldClaim

/-- Section 17.1 package:
unoriented-string construction via gauged orientation reversal and
`Omega`-projected spectrum. -/
def UnorientedWorldsheetParityPackage
    (data : UnorientedWorldsheetParityData) : Prop :=
  data.orientationReversingDiffeomorphismsGauged /\
  data.worldsheetParityOmegaDefinedOnCylinderAndPlane /\
  data.physicalStatesProjectedToOmegaInvariantSubspace /\
  data.nsnsBFieldProjectedOutByParity /\
  data.eulerCharacteristicWithCrosscapsUsed /\
  data.unorientedSurfaceDescribedByOrientedDoubleCover

/-- Assumed Section 17.1 unoriented-worldsheet parity package. -/
theorem unoriented_worldsheet_parity_package
    (data : UnorientedWorldsheetParityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeIUnorientedWorldsheetParityProjection
      (UnorientedWorldsheetParityPackage data)) :
    UnorientedWorldsheetParityPackage data := by
  exact h_phys

/-- Bosonic crosscap-state and Klein-bottle modular-crossing data. -/
structure CrosscapStateBosonicData where
  alphaPrime : StringSlope
  crosscapBoundaryIdentificationImposed : TypeIOrientifoldClaim
  oscillatorGluingConditionsSolved : TypeIOrientifoldClaim
  explicitCrosscapStateExponentialFormUsed : TypeIOrientifoldClaim
  kleinBottleCrossChannelRelationUsed : TypeIOrientifoldClaim
  crosscapNormalizationMagnitudeDetermined : TypeIOrientifoldClaim
  mobiusComparisonFixesSignChoice : TypeIOrientifoldClaim
  crosscapSourcesMasslessTadpoleWithoutBraneCancellation : TypeIOrientifoldClaim

/-- Section 17.2 package:
crosscap-state construction, modular crossing, and normalization/sign data. -/
def CrosscapStateBosonicPackage (data : CrosscapStateBosonicData) : Prop :=
  data.alphaPrime > 0 /\
  data.crosscapBoundaryIdentificationImposed /\
  data.oscillatorGluingConditionsSolved /\
  data.explicitCrosscapStateExponentialFormUsed /\
  data.kleinBottleCrossChannelRelationUsed /\
  data.crosscapNormalizationMagnitudeDetermined /\
  data.mobiusComparisonFixesSignChoice /\
  data.crosscapSourcesMasslessTadpoleWithoutBraneCancellation

/-- Assumed Section 17.2 crosscap-state package. -/
theorem crosscap_state_bosonic_package
    (data : CrosscapStateBosonicData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeICrosscapStateAndKleinBottleDuality
      (CrosscapStateBosonicPackage data)) :
    CrosscapStateBosonicPackage data := by
  exact h_phys

/-- Type-I open/closed `Omega`-projection data from type-IIB parent theory. -/
structure TypeIClosedOpenProjectionData where
  startedFromTypeIIBWithParityInvariantGso : TypeIOrientifoldClaim
  omegaActionOnMatterGhostSuperghostSpecified : TypeIOrientifoldClaim
  omegaSquaredMatchesFParityInClosedSector : TypeIOrientifoldClaim
  rrProjectionRetainsOnlyTwoFormPotential : TypeIOrientifoldClaim
  openStripOmegaActionAndDoublingTrickUsed : TypeIOrientifoldClaim
  chanPatonOmegaActionUsesCMatrixConstraint : TypeIOrientifoldClaim
  openMasslessGaugeBosonsFormSoOrSpAlgebra : TypeIOrientifoldClaim
  typeIConsistencySelectsSo32Candidate : TypeIOrientifoldClaim

/-- Section 17.3 package:
type-I projection from type-IIB with `Omega` action in open/closed sectors and
Chan-Paton algebra reduction. -/
def TypeIClosedOpenProjectionPackage
    (data : TypeIClosedOpenProjectionData) : Prop :=
  data.startedFromTypeIIBWithParityInvariantGso /\
  data.omegaActionOnMatterGhostSuperghostSpecified /\
  data.omegaSquaredMatchesFParityInClosedSector /\
  data.rrProjectionRetainsOnlyTwoFormPotential /\
  data.openStripOmegaActionAndDoublingTrickUsed /\
  data.chanPatonOmegaActionUsesCMatrixConstraint /\
  data.openMasslessGaugeBosonsFormSoOrSpAlgebra /\
  data.typeIConsistencySelectsSo32Candidate

/-- Assumed Section 17.3 type-I open/closed projection package. -/
theorem type_i_closed_open_projection_package
    (data : TypeIClosedOpenProjectionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeIClosedOpenOmegaProjectionSpectrum
      (TypeIClosedOpenProjectionPackage data)) :
    TypeIClosedOpenProjectionPackage data := by
  exact h_phys

/-- Type-I tadpole-cancellation data with crosscap and D9 boundary states. -/
structure TypeITadpoleCancellationData where
  d9BraneCount : Nat
  crosscapStateBuiltInNsnsAndRrSectors : TypeIOrientifoldClaim
  kleinBottleCrossChannelNormalizationsComputed : TypeIOrientifoldClaim
  mobiusComparisonWithD9BoundaryStatePerformed : TypeIOrientifoldClaim
  nsnsTadpoleCancellationVerified : TypeIOrientifoldClaim
  rrTadpoleCancellationVerified : TypeIOrientifoldClaim
  soTypeChanPatonSelectionRequired : TypeIOrientifoldClaim
  orientifoldInterpretedAsClosedStringSource : TypeIOrientifoldClaim

/-- Section 17.4 package:
massless tadpole cancellation in type-I requires the `SO(32)` D9 system. -/
def TypeITadpoleCancellationPackage
    (data : TypeITadpoleCancellationData) : Prop :=
  data.d9BraneCount = 32 /\
  data.crosscapStateBuiltInNsnsAndRrSectors /\
  data.kleinBottleCrossChannelNormalizationsComputed /\
  data.mobiusComparisonWithD9BoundaryStatePerformed /\
  data.nsnsTadpoleCancellationVerified /\
  data.rrTadpoleCancellationVerified /\
  data.soTypeChanPatonSelectionRequired /\
  data.orientifoldInterpretedAsClosedStringSource

/-- Assumed Section 17.4 type-I tadpole-cancellation package. -/
theorem type_i_tadpole_cancellation_package
    (data : TypeITadpoleCancellationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeITadpoleCancellationSO32
      (TypeITadpoleCancellationPackage data)) :
    TypeITadpoleCancellationPackage data := by
  exact h_phys

/-- Type-I amplitude normalization data on oriented+unoriented open+closed supermoduli. -/
structure TypeIAmplitudeNormalizationData where
  orientedAndUnorientedWorldsheetClassesIncluded : TypeIOrientifoldClaim
  pcoAndSpinStructureFiberBundleIntegrationUsed : TypeIOrientifoldClaim
  unitarityFixesEulerCharacteristicNormalization : TypeIOrientifoldClaim
  omegaInvariantIntermediateStateFactorizationUsed : TypeIOrientifoldClaim
  openPropagatorNormalizationConstraintApplied : TypeIOrientifoldClaim
  omegaInvariantOpenClosedSftExtensionWithCrosscapsAvailable : TypeIOrientifoldClaim

/-- Section 17.5 package:
type-I open+closed amplitude normalization on oriented/unoriented moduli space. -/
def TypeIAmplitudeNormalizationPackage
    (data : TypeIAmplitudeNormalizationData) : Prop :=
  data.orientedAndUnorientedWorldsheetClassesIncluded /\
  data.pcoAndSpinStructureFiberBundleIntegrationUsed /\
  data.unitarityFixesEulerCharacteristicNormalization /\
  data.omegaInvariantIntermediateStateFactorizationUsed /\
  data.openPropagatorNormalizationConstraintApplied /\
  data.omegaInvariantOpenClosedSftExtensionWithCrosscapsAvailable

/-- Assumed Section 17.5 type-I amplitude normalization package. -/
theorem type_i_amplitude_normalization_package
    (data : TypeIAmplitudeNormalizationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeIAmplitudeNormalizationUnorientedOpenClosed
      (TypeIAmplitudeNormalizationPackage data)) :
    TypeIAmplitudeNormalizationPackage data := by
  exact h_phys

/-- Type-I one-loop vacuum-topology and cancellation data. -/
structure TypeIVacuumAmplitudeData where
  torusKleinBottleCylinderMobiusTopologiesIncluded : TypeIOrientifoldClaim
  closedOneLoopOmegaInvariantInterpretationUsed : TypeIOrientifoldClaim
  openOneLoopOmegaInvariantInterpretationUsed : TypeIOrientifoldClaim
  uvDivergenceAsMasslessClosedExchangeIdentified : TypeIOrientifoldClaim
  tadpoleCancellationRemovesMasslessExchangeDivergences : TypeIOrientifoldClaim
  supersymmetryImpliesTotalVacuumAmplitudeVanishing : TypeIOrientifoldClaim

/-- Section 17.5.1 package:
vacuum amplitude from the four one-loop topologies and tadpole-controlled
consistency. -/
def TypeIVacuumAmplitudePackage (data : TypeIVacuumAmplitudeData) : Prop :=
  data.torusKleinBottleCylinderMobiusTopologiesIncluded /\
  data.closedOneLoopOmegaInvariantInterpretationUsed /\
  data.openOneLoopOmegaInvariantInterpretationUsed /\
  data.uvDivergenceAsMasslessClosedExchangeIdentified /\
  data.tadpoleCancellationRemovesMasslessExchangeDivergences /\
  data.supersymmetryImpliesTotalVacuumAmplitudeVanishing

/-- Assumed Section 17.5.1 type-I vacuum amplitude package. -/
theorem type_i_vacuum_amplitude_package
    (data : TypeIVacuumAmplitudeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeIVacuumAmplitudeTopologyAndCancellation
      (TypeIVacuumAmplitudePackage data)) :
    TypeIVacuumAmplitudePackage data := by
  exact h_phys

/-- Type-I spacetime effective-action data with gauge/gravity couplings. -/
structure TypeIEffectiveActionData (FieldConfig : Type*) where
  stringCoupling : DimensionlessCoupling
  alphaPrime : StringSlope
  gravitationalCoupling : CouplingScale
  yangMillsCouplingSq : CouplingScale
  effectiveActionFunctional : FieldConfig → ComplexActionValue
  sphereAndDiscDilatonWeightsIncluded : TypeIOrientifoldClaim
  gravityAndGaugeCouplingsMatchedToThreePointAmplitudes : TypeIOrientifoldClaim
  rrChernSimonsCouplingsToGaugeFieldsIncluded : TypeIOrientifoldClaim
  greenSchwarzAnomalyCouplingsPresent : TypeIOrientifoldClaim
  actionInterpretedAsFunctionalNotScalarObservable : TypeIOrientifoldClaim

/-- Section 17.5.2 package:
type-I massless effective action with gauge/gravity coupling dictionary and
RR Chern-Simons/Green-Schwarz couplings. -/
def TypeIEffectiveActionPackage
    {FieldConfig : Type*} (data : TypeIEffectiveActionData FieldConfig) : Prop :=
  data.stringCoupling > 0 /\
  data.alphaPrime > 0 /\
  data.gravitationalCoupling > 0 /\
  data.yangMillsCouplingSq > 0 /\
  data.sphereAndDiscDilatonWeightsIncluded /\
  data.gravityAndGaugeCouplingsMatchedToThreePointAmplitudes /\
  data.rrChernSimonsCouplingsToGaugeFieldsIncluded /\
  data.greenSchwarzAnomalyCouplingsPresent /\
  data.actionInterpretedAsFunctionalNotScalarObservable

/-- Assumed Section 17.5.2 type-I effective-action package. -/
theorem type_i_effective_action_package
    {FieldConfig : Type*}
    (data : TypeIEffectiveActionData FieldConfig)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeIEffectiveActionGaugeGravityCouplings
      (TypeIEffectiveActionPackage data)) :
    TypeIEffectiveActionPackage data := by
  exact h_phys

/-- Type-I BPS D1/D5 brane-spectrum and Chan-Paton-projection data. -/
structure TypeIBpsD1D5Data where
  d1AndD5AllowedByOmegaConsistencyCondition : TypeIOrientifoldClaim
  d1ChanPatonProjectionUsesSymmetricMatrix : TypeIOrientifoldClaim
  d5ChanPatonProjectionUsesAntisymmetricMatrix : TypeIOrientifoldClaim
  d1MasslessWorldvolumeModesAndChiralRamondSpectrumIdentified : TypeIOrientifoldClaim
  d1d9SectorHasChiralMasslessFermionsInSo32Vector : TypeIOrientifoldClaim
  d5d5SectorCarriesSpGaugeMultipletData : TypeIOrientifoldClaim
  d5d9SectorCarriesSixDimensionalHypermultipletData : TypeIOrientifoldClaim

/-- Section 17.6.1 package:
BPS D1/D5 branes in type-I from `Omega` projections of type-IIB D-brane sectors. -/
def TypeIBpsD1D5Package (data : TypeIBpsD1D5Data) : Prop :=
  data.d1AndD5AllowedByOmegaConsistencyCondition /\
  data.d1ChanPatonProjectionUsesSymmetricMatrix /\
  data.d5ChanPatonProjectionUsesAntisymmetricMatrix /\
  data.d1MasslessWorldvolumeModesAndChiralRamondSpectrumIdentified /\
  data.d1d9SectorHasChiralMasslessFermionsInSo32Vector /\
  data.d5d5SectorCarriesSpGaugeMultipletData /\
  data.d5d9SectorCarriesSixDimensionalHypermultipletData

/-- Assumed Section 17.6.1 type-I BPS D1/D5 package. -/
theorem type_i_bps_d1_d5_package
    (data : TypeIBpsD1D5Data)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeIBpsD1D5BraneSpectrum
      (TypeIBpsD1D5Package data)) :
    TypeIBpsD1D5Package data := by
  exact h_phys

/-- Type-I non-BPS D0-brane projection/stability data. -/
structure TypeINonBpsD0Data where
  constructedFromTypeIibNonBpsBoundaryCondition : TypeIOrientifoldClaim
  omegaProjectionRemovesOpenStringTachyon : TypeIOrientifoldClaim
  bosonicCollectiveCoordinateModesRetained : TypeIOrientifoldClaim
  ramondGoldstinoModesPartiallyRetained : TypeIOrientifoldClaim
  d0d9MasslessFermionCount : Nat
  residualZTwoGaugeSymmetryRetained : TypeIOrientifoldClaim
  classicallyStableAfterProjection : TypeIOrientifoldClaim

/-- Section 17.6.2 package:
type-I non-BPS D0-brane with tachyon projection and `SO(32)` spinor-state
quantization data from D0-D9 fermionic modes. -/
def TypeINonBpsD0Package (data : TypeINonBpsD0Data) : Prop :=
  data.constructedFromTypeIibNonBpsBoundaryCondition /\
  data.omegaProjectionRemovesOpenStringTachyon /\
  data.bosonicCollectiveCoordinateModesRetained /\
  data.ramondGoldstinoModesPartiallyRetained /\
  data.d0d9MasslessFermionCount = 32 /\
  data.residualZTwoGaugeSymmetryRetained /\
  data.classicallyStableAfterProjection

/-- Assumed Section 17.6.2 type-I non-BPS D0 package. -/
theorem type_i_non_bps_d0_package
    (data : TypeINonBpsD0Data)
    (h_phys : PhysicsAssumption
      AssumptionId.stringTypeINonBpsD0StabilityAndFermions
      (TypeINonBpsD0Package data)) :
    TypeINonBpsD0Package data := by
  exact h_phys

/-- Orientifold-plane crosscap/charge dictionary data. -/
structure OrientifoldPlaneData where
  p : Nat
  omegaTimesInvolutionQuotientDefined : TypeIOrientifoldClaim
  typeIIBEvenPAndTypeIIAOddPCompatibilityUsed : TypeIOrientifoldClaim
  opCrosscapStatesDefinedInNsnsAndRrSectors : TypeIOrientifoldClaim
  opNormalizationFixedByKleinBottleAndMobiusMatching : TypeIOrientifoldClaim
  opPlusMinusFamiliesFromSoSpChoiceIdentified : TypeIOrientifoldClaim
  opTensionAndRrChargeRelativeToDpDetermined : TypeIOrientifoldClaim
  tDualityMapFromO9ToTwoO8PlanesUsed : TypeIOrientifoldClaim

/-- Section 17.7 package:
orientifold-plane construction from `Omega * I`, crosscap normalization, and
`O p^+ / O p^-` charge-tension dictionary. -/
def OrientifoldPlanePackage (data : OrientifoldPlaneData) : Prop :=
  data.p ≤ 9 /\
  data.omegaTimesInvolutionQuotientDefined /\
  data.typeIIBEvenPAndTypeIIAOddPCompatibilityUsed /\
  data.opCrosscapStatesDefinedInNsnsAndRrSectors /\
  data.opNormalizationFixedByKleinBottleAndMobiusMatching /\
  data.opPlusMinusFamiliesFromSoSpChoiceIdentified /\
  data.opTensionAndRrChargeRelativeToDpDetermined /\
  data.tDualityMapFromO9ToTwoO8PlanesUsed

/-- Assumed Section 17.7 orientifold-plane package. -/
theorem orientifold_plane_package
    (data : OrientifoldPlaneData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringOrientifoldPlaneCrosscapChargeDictionary
      (OrientifoldPlanePackage data)) :
    OrientifoldPlanePackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
