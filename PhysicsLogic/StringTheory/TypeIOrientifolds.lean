import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Unoriented-string worldsheet parity and spectrum-projection data. -/
structure UnorientedWorldsheetParityData where
  orientationReversingDiffeomorphismsGauged : Bool
  worldsheetParityOmegaDefinedOnCylinderAndPlane : Bool
  physicalStatesProjectedToOmegaInvariantSubspace : Bool
  nsnsBFieldProjectedOutByParity : Bool
  eulerCharacteristicWithCrosscapsUsed : Bool
  unorientedSurfaceDescribedByOrientedDoubleCover : Bool

/-- Section 17.1 package:
unoriented-string construction via gauged orientation reversal and
`Omega`-projected spectrum. -/
def UnorientedWorldsheetParityPackage
    (data : UnorientedWorldsheetParityData) : Prop :=
  data.orientationReversingDiffeomorphismsGauged = true /\
  data.worldsheetParityOmegaDefinedOnCylinderAndPlane = true /\
  data.physicalStatesProjectedToOmegaInvariantSubspace = true /\
  data.nsnsBFieldProjectedOutByParity = true /\
  data.eulerCharacteristicWithCrosscapsUsed = true /\
  data.unorientedSurfaceDescribedByOrientedDoubleCover = true

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
  alphaPrime : Real
  crosscapBoundaryIdentificationImposed : Bool
  oscillatorGluingConditionsSolved : Bool
  explicitCrosscapStateExponentialFormUsed : Bool
  kleinBottleCrossChannelRelationUsed : Bool
  crosscapNormalizationMagnitudeDetermined : Bool
  mobiusComparisonFixesSignChoice : Bool
  crosscapSourcesMasslessTadpoleWithoutBraneCancellation : Bool

/-- Section 17.2 package:
crosscap-state construction, modular crossing, and normalization/sign data. -/
def CrosscapStateBosonicPackage (data : CrosscapStateBosonicData) : Prop :=
  data.alphaPrime > 0 /\
  data.crosscapBoundaryIdentificationImposed = true /\
  data.oscillatorGluingConditionsSolved = true /\
  data.explicitCrosscapStateExponentialFormUsed = true /\
  data.kleinBottleCrossChannelRelationUsed = true /\
  data.crosscapNormalizationMagnitudeDetermined = true /\
  data.mobiusComparisonFixesSignChoice = true /\
  data.crosscapSourcesMasslessTadpoleWithoutBraneCancellation = true

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
  startedFromTypeIIBWithParityInvariantGso : Bool
  omegaActionOnMatterGhostSuperghostSpecified : Bool
  omegaSquaredMatchesFParityInClosedSector : Bool
  rrProjectionRetainsOnlyTwoFormPotential : Bool
  openStripOmegaActionAndDoublingTrickUsed : Bool
  chanPatonOmegaActionUsesCMatrixConstraint : Bool
  openMasslessGaugeBosonsFormSoOrSpAlgebra : Bool
  typeIConsistencySelectsSo32Candidate : Bool

/-- Section 17.3 package:
type-I projection from type-IIB with `Omega` action in open/closed sectors and
Chan-Paton algebra reduction. -/
def TypeIClosedOpenProjectionPackage
    (data : TypeIClosedOpenProjectionData) : Prop :=
  data.startedFromTypeIIBWithParityInvariantGso = true /\
  data.omegaActionOnMatterGhostSuperghostSpecified = true /\
  data.omegaSquaredMatchesFParityInClosedSector = true /\
  data.rrProjectionRetainsOnlyTwoFormPotential = true /\
  data.openStripOmegaActionAndDoublingTrickUsed = true /\
  data.chanPatonOmegaActionUsesCMatrixConstraint = true /\
  data.openMasslessGaugeBosonsFormSoOrSpAlgebra = true /\
  data.typeIConsistencySelectsSo32Candidate = true

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
  crosscapStateBuiltInNsnsAndRrSectors : Bool
  kleinBottleCrossChannelNormalizationsComputed : Bool
  mobiusComparisonWithD9BoundaryStatePerformed : Bool
  nsnsTadpoleCancellationVerified : Bool
  rrTadpoleCancellationVerified : Bool
  soTypeChanPatonSelectionRequired : Bool
  orientifoldInterpretedAsClosedStringSource : Bool

/-- Section 17.4 package:
massless tadpole cancellation in type-I requires the `SO(32)` D9 system. -/
def TypeITadpoleCancellationPackage
    (data : TypeITadpoleCancellationData) : Prop :=
  data.d9BraneCount = 32 /\
  data.crosscapStateBuiltInNsnsAndRrSectors = true /\
  data.kleinBottleCrossChannelNormalizationsComputed = true /\
  data.mobiusComparisonWithD9BoundaryStatePerformed = true /\
  data.nsnsTadpoleCancellationVerified = true /\
  data.rrTadpoleCancellationVerified = true /\
  data.soTypeChanPatonSelectionRequired = true /\
  data.orientifoldInterpretedAsClosedStringSource = true

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
  orientedAndUnorientedWorldsheetClassesIncluded : Bool
  pcoAndSpinStructureFiberBundleIntegrationUsed : Bool
  unitarityFixesEulerCharacteristicNormalization : Bool
  omegaInvariantIntermediateStateFactorizationUsed : Bool
  openPropagatorNormalizationConstraintApplied : Bool
  omegaInvariantOpenClosedSftExtensionWithCrosscapsAvailable : Bool

/-- Section 17.5 package:
type-I open+closed amplitude normalization on oriented/unoriented moduli space. -/
def TypeIAmplitudeNormalizationPackage
    (data : TypeIAmplitudeNormalizationData) : Prop :=
  data.orientedAndUnorientedWorldsheetClassesIncluded = true /\
  data.pcoAndSpinStructureFiberBundleIntegrationUsed = true /\
  data.unitarityFixesEulerCharacteristicNormalization = true /\
  data.omegaInvariantIntermediateStateFactorizationUsed = true /\
  data.openPropagatorNormalizationConstraintApplied = true /\
  data.omegaInvariantOpenClosedSftExtensionWithCrosscapsAvailable = true

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
  torusKleinBottleCylinderMobiusTopologiesIncluded : Bool
  closedOneLoopOmegaInvariantInterpretationUsed : Bool
  openOneLoopOmegaInvariantInterpretationUsed : Bool
  uvDivergenceAsMasslessClosedExchangeIdentified : Bool
  tadpoleCancellationRemovesMasslessExchangeDivergences : Bool
  supersymmetryImpliesTotalVacuumAmplitudeVanishing : Bool

/-- Section 17.5.1 package:
vacuum amplitude from the four one-loop topologies and tadpole-controlled
consistency. -/
def TypeIVacuumAmplitudePackage (data : TypeIVacuumAmplitudeData) : Prop :=
  data.torusKleinBottleCylinderMobiusTopologiesIncluded = true /\
  data.closedOneLoopOmegaInvariantInterpretationUsed = true /\
  data.openOneLoopOmegaInvariantInterpretationUsed = true /\
  data.uvDivergenceAsMasslessClosedExchangeIdentified = true /\
  data.tadpoleCancellationRemovesMasslessExchangeDivergences = true /\
  data.supersymmetryImpliesTotalVacuumAmplitudeVanishing = true

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
  stringCoupling : Real
  alphaPrime : Real
  gravitationalCoupling : Real
  yangMillsCouplingSq : Real
  effectiveActionFunctional : FieldConfig → Complex
  sphereAndDiscDilatonWeightsIncluded : Bool
  gravityAndGaugeCouplingsMatchedToThreePointAmplitudes : Bool
  rrChernSimonsCouplingsToGaugeFieldsIncluded : Bool
  greenSchwarzAnomalyCouplingsPresent : Bool
  actionInterpretedAsFunctionalNotScalarObservable : Bool

/-- Section 17.5.2 package:
type-I massless effective action with gauge/gravity coupling dictionary and
RR Chern-Simons/Green-Schwarz couplings. -/
def TypeIEffectiveActionPackage
    {FieldConfig : Type*} (data : TypeIEffectiveActionData FieldConfig) : Prop :=
  data.stringCoupling > 0 /\
  data.alphaPrime > 0 /\
  data.gravitationalCoupling > 0 /\
  data.yangMillsCouplingSq > 0 /\
  data.sphereAndDiscDilatonWeightsIncluded = true /\
  data.gravityAndGaugeCouplingsMatchedToThreePointAmplitudes = true /\
  data.rrChernSimonsCouplingsToGaugeFieldsIncluded = true /\
  data.greenSchwarzAnomalyCouplingsPresent = true /\
  data.actionInterpretedAsFunctionalNotScalarObservable = true

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
  d1AndD5AllowedByOmegaConsistencyCondition : Bool
  d1ChanPatonProjectionUsesSymmetricMatrix : Bool
  d5ChanPatonProjectionUsesAntisymmetricMatrix : Bool
  d1MasslessWorldvolumeModesAndChiralRamondSpectrumIdentified : Bool
  d1d9SectorHasChiralMasslessFermionsInSo32Vector : Bool
  d5d5SectorCarriesSpGaugeMultipletData : Bool
  d5d9SectorCarriesSixDimensionalHypermultipletData : Bool

/-- Section 17.6.1 package:
BPS D1/D5 branes in type-I from `Omega` projections of type-IIB D-brane sectors. -/
def TypeIBpsD1D5Package (data : TypeIBpsD1D5Data) : Prop :=
  data.d1AndD5AllowedByOmegaConsistencyCondition = true /\
  data.d1ChanPatonProjectionUsesSymmetricMatrix = true /\
  data.d5ChanPatonProjectionUsesAntisymmetricMatrix = true /\
  data.d1MasslessWorldvolumeModesAndChiralRamondSpectrumIdentified = true /\
  data.d1d9SectorHasChiralMasslessFermionsInSo32Vector = true /\
  data.d5d5SectorCarriesSpGaugeMultipletData = true /\
  data.d5d9SectorCarriesSixDimensionalHypermultipletData = true

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
  constructedFromTypeIibNonBpsBoundaryCondition : Bool
  omegaProjectionRemovesOpenStringTachyon : Bool
  bosonicCollectiveCoordinateModesRetained : Bool
  ramondGoldstinoModesPartiallyRetained : Bool
  d0d9MasslessFermionCount : Nat
  residualZTwoGaugeSymmetryRetained : Bool
  classicallyStableAfterProjection : Bool

/-- Section 17.6.2 package:
type-I non-BPS D0-brane with tachyon projection and `SO(32)` spinor-state
quantization data from D0-D9 fermionic modes. -/
def TypeINonBpsD0Package (data : TypeINonBpsD0Data) : Prop :=
  data.constructedFromTypeIibNonBpsBoundaryCondition = true /\
  data.omegaProjectionRemovesOpenStringTachyon = true /\
  data.bosonicCollectiveCoordinateModesRetained = true /\
  data.ramondGoldstinoModesPartiallyRetained = true /\
  data.d0d9MasslessFermionCount = 32 /\
  data.residualZTwoGaugeSymmetryRetained = true /\
  data.classicallyStableAfterProjection = true

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
  omegaTimesInvolutionQuotientDefined : Bool
  typeIIBEvenPAndTypeIIAOddPCompatibilityUsed : Bool
  opCrosscapStatesDefinedInNsnsAndRrSectors : Bool
  opNormalizationFixedByKleinBottleAndMobiusMatching : Bool
  opPlusMinusFamiliesFromSoSpChoiceIdentified : Bool
  opTensionAndRrChargeRelativeToDpDetermined : Bool
  tDualityMapFromO9ToTwoO8PlanesUsed : Bool

/-- Section 17.7 package:
orientifold-plane construction from `Omega * I`, crosscap normalization, and
`O p^+ / O p^-` charge-tension dictionary. -/
def OrientifoldPlanePackage (data : OrientifoldPlaneData) : Prop :=
  data.p ≤ 9 /\
  data.omegaTimesInvolutionQuotientDefined = true /\
  data.typeIIBEvenPAndTypeIIAOddPCompatibilityUsed = true /\
  data.opCrosscapStatesDefinedInNsnsAndRrSectors = true /\
  data.opNormalizationFixedByKleinBottleAndMobiusMatching = true /\
  data.opPlusMinusFamiliesFromSoSpChoiceIdentified = true /\
  data.opTensionAndRrChargeRelativeToDpDetermined = true /\
  data.tDualityMapFromO9ToTwoO8PlanesUsed = true

/-- Assumed Section 17.7 orientifold-plane package. -/
theorem orientifold_plane_package
    (data : OrientifoldPlaneData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringOrientifoldPlaneCrosscapChargeDictionary
      (OrientifoldPlanePackage data)) :
    OrientifoldPlanePackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
