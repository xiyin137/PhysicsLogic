import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Open+closed type-II perturbative data on super Riemann surfaces with boundary. -/
structure OpenClosedTypeIIPerturbationData where
  alphaPrime : Real
  openStringNormalizationKo : Real
  representativeAmplitude : Complex
  representativeReducedAmplitude : Complex
  boundarySuperRiemannSurfaceTransitionRulesUsed : Bool
  supermoduliDimensionRuleApplied : Bool
  boundarySpinStructureSummationIncluded : Bool
  pcoFiberIntegrationAndVerticalCorrectionsUsed : Bool
  discGhostMatterNormalizationConventionFixed : Bool
  openClosedCouplingDictionaryApplied : Bool
  actionFunctionalInterfaceAllowsComplexValues : Bool

/-- Section 14.1 package:
type-II open+closed amplitudes on BSRS supermoduli with spin-structure sums and
PCO/vertical-integration prescriptions. -/
def OpenClosedTypeIIPerturbationPackage
    (data : OpenClosedTypeIIPerturbationData) : Prop :=
  data.alphaPrime > 0 /\
  data.openStringNormalizationKo = -(1 / data.alphaPrime) /\
  data.boundarySuperRiemannSurfaceTransitionRulesUsed = true /\
  data.supermoduliDimensionRuleApplied = true /\
  data.boundarySpinStructureSummationIncluded = true /\
  data.pcoFiberIntegrationAndVerticalCorrectionsUsed = true /\
  data.discGhostMatterNormalizationConventionFixed = true /\
  data.openClosedCouplingDictionaryApplied = true /\
  data.actionFunctionalInterfaceAllowsComplexValues = true

/-- Assumed Section 14.1 open+closed type-II perturbation package. -/
theorem open_closed_typeII_perturbation_package
    (data : OpenClosedTypeIIPerturbationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIOpenClosedPerturbation
      (OpenClosedTypeIIPerturbationPackage data)) :
    OpenClosedTypeIIPerturbationPackage data := by
  exact h_phys

/-- Disc open-superstring gauge-amplitude data on stacked BPS D-branes. -/
structure DiscOpenGaugeAmplitudeData where
  alphaPrime : Real
  openCoupling : Real
  yMGaugeCoupling : Real
  stackSize : Nat
  chanPatonTraceOrderingIncluded : Bool
  threeGaugeBosonAmplitudeMatchesYangMillsVertex : Bool
  fourGaugeBosonAmplitudeHasGammaFunctionChannelStructure : Bool
  leadingLowEnergyLimitMatchesYangMillsFourPoint : Bool
  alphaPrimeSquaredT8F4CorrectionIdentified : Bool
  noOrderAlphaPrimeFcubeCorrection : Bool

/-- Section 14.2 package:
disc open-superstring amplitudes on a D-brane stack, including Yang-Mills
matching and the first `alpha'^2 t8 F^4` correction. -/
def DiscOpenGaugeAmplitudePackage
    (data : DiscOpenGaugeAmplitudeData) : Prop :=
  data.alphaPrime > 0 /\
  data.openCoupling > 0 /\
  data.stackSize > 0 /\
  data.yMGaugeCoupling = data.openCoupling / Real.sqrt (8 * data.alphaPrime) /\
  data.chanPatonTraceOrderingIncluded = true /\
  data.threeGaugeBosonAmplitudeMatchesYangMillsVertex = true /\
  data.fourGaugeBosonAmplitudeHasGammaFunctionChannelStructure = true /\
  data.leadingLowEnergyLimitMatchesYangMillsFourPoint = true /\
  data.alphaPrimeSquaredT8F4CorrectionIdentified = true /\
  data.noOrderAlphaPrimeFcubeCorrection = true

/-- Assumed Section 14.2 disc open-gauge amplitude package. -/
theorem disc_open_gauge_amplitude_package
    (data : DiscOpenGaugeAmplitudeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIDiscOpenGaugeAmplitudes
      (DiscOpenGaugeAmplitudePackage data)) :
    DiscOpenGaugeAmplitudePackage data := by
  exact h_phys

/-- Disc open+closed RR-coupling data for a BPS D-brane. -/
structure DiscOpenClosedRrCouplingData where
  rrClosedAndNsOpenDiscAmplitudeComputed : Bool
  worldvolumeChernSimonsCouplingA_wedge_FpIdentified : Bool
  transverseDisplacementCouplingToF_pPlusTwoIdentified : Bool
  dpBraneCarriesRrChargeUnderC_pPlusOne : Bool
  couplingNormalizationMatchesBoundaryStateDictionary : Bool

/-- Section 14.3 package:
disc amplitudes with one RR closed-string and one NS open-string insertion,
fixing Chern-Simons/worldvolume-displacement RR couplings. -/
def DiscOpenClosedRrCouplingPackage
    (data : DiscOpenClosedRrCouplingData) : Prop :=
  data.rrClosedAndNsOpenDiscAmplitudeComputed = true /\
  data.worldvolumeChernSimonsCouplingA_wedge_FpIdentified = true /\
  data.transverseDisplacementCouplingToF_pPlusTwoIdentified = true /\
  data.dpBraneCarriesRrChargeUnderC_pPlusOne = true /\
  data.couplingNormalizationMatchesBoundaryStateDictionary = true

/-- Assumed Section 14.3 disc open+closed RR-coupling package. -/
theorem disc_open_closed_rr_coupling_package
    (data : DiscOpenClosedRrCouplingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIDiscOpenClosedRrCouplings
      (DiscOpenClosedRrCouplingPackage data)) :
    DiscOpenClosedRrCouplingPackage data := by
  exact h_phys

/-- Cylinder-channel type-II interaction data between parallel D-branes. -/
structure CylinderTypeIICancellationData where
  nsnsCylinderAmplitudeComputed : Bool
  rrCylinderAmplitudeComputed : Bool
  jacobiThetaIdentityUsedForSectorCancellation : Bool
  parallelBpsBranePotentialCancels : Bool
  antiBraneFlipsRrContributionSign : Bool
  largeDistanceMasslessExchangeExtractionUsed : Bool

/-- Section 14.4 package:
type-II cylinder NSNS/RR exchange structure and BPS-force cancellation for
parallel D-branes. -/
def CylinderTypeIICancellationPackage
    (data : CylinderTypeIICancellationData) : Prop :=
  data.nsnsCylinderAmplitudeComputed = true /\
  data.rrCylinderAmplitudeComputed = true /\
  data.jacobiThetaIdentityUsedForSectorCancellation = true /\
  data.parallelBpsBranePotentialCancels = true /\
  data.antiBraneFlipsRrContributionSign = true /\
  data.largeDistanceMasslessExchangeExtractionUsed = true

/-- Assumed Section 14.4 cylinder NSNS/RR cancellation package. -/
theorem cylinder_typeII_cancellation_package
    (data : CylinderTypeIICancellationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIICylinderNsnsRrCancellation
      (CylinderTypeIICancellationPackage data)) :
    CylinderTypeIICancellationPackage data := by
  exact h_phys

/-- Kappa-symmetric BPS D-brane action data in flat type-II superspace. -/
structure BpsKappaSymmetricActionData where
  alphaPrime : Real
  openCoupling : Real
  braneTension : Real
  supersymmetryInvariantPiAndCalFConstructed : Bool
  dbiPlusWessZuminoActionUsed : Bool
  kappaSymmetryProjectorSquaresToOne : Bool
  staticGaugeAndKappaGaugeFixingImplemented : Bool
  staticGaugeActionContainsGoldstinoAndBornInfeldData : Bool
  t8f4MatchingFixesTension : Bool

/-- Section 14.5.1 package:
flat-space supersymmetric/kappa-symmetric DBI+WZ action and its static-gauge
reduction to maximally supersymmetric worldvolume dynamics. -/
def BpsKappaSymmetricActionPackage
    (data : BpsKappaSymmetricActionData) : Prop :=
  data.alphaPrime > 0 /\
  data.openCoupling > 0 /\
  data.braneTension = 2 / (Real.pi ^ (2 : Nat) * data.alphaPrime * data.openCoupling ^ (2 : Nat)) /\
  data.supersymmetryInvariantPiAndCalFConstructed = true /\
  data.dbiPlusWessZuminoActionUsed = true /\
  data.kappaSymmetryProjectorSquaresToOne = true /\
  data.staticGaugeAndKappaGaugeFixingImplemented = true /\
  data.staticGaugeActionContainsGoldstinoAndBornInfeldData = true /\
  data.t8f4MatchingFixesTension = true

/-- Assumed Section 14.5.1 kappa-symmetric BPS action package. -/
theorem bps_kappa_symmetric_action_package
    (data : BpsKappaSymmetricActionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIBpsKappaSymmetricAction
      (BpsKappaSymmetricActionPackage data)) :
    BpsKappaSymmetricActionPackage data := by
  exact h_phys

/-- BPS D-brane couplings to type-II massless closed-string backgrounds. -/
structure BpsBackgroundCouplingData where
  dbiTermIncludesDilatonMetricBAndWorldvolumeF : Bool
  wessZuminoTermIncludesRrPotentialSum : Bool
  rrChargeDensityEqualsTension : Bool
  gravitonDilatonExchangeMatchesCylinderLargeDistance : Bool
  rrCouplingsMatchDiscOpenClosedAmplitudes : Bool

/-- Section 14.5.2 package:
bosonic part of the BPS D-brane action in general backgrounds, including RR
Wess-Zumino couplings and force-cancellation consistency. -/
def BpsBackgroundCouplingPackage (data : BpsBackgroundCouplingData) : Prop :=
  data.dbiTermIncludesDilatonMetricBAndWorldvolumeF = true /\
  data.wessZuminoTermIncludesRrPotentialSum = true /\
  data.rrChargeDensityEqualsTension = true /\
  data.gravitonDilatonExchangeMatchesCylinderLargeDistance = true /\
  data.rrCouplingsMatchDiscOpenClosedAmplitudes = true

/-- Assumed Section 14.5.2 background-coupling package. -/
theorem bps_background_coupling_package
    (data : BpsBackgroundCouplingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIBpsBackgroundCouplings
      (BpsBackgroundCouplingPackage data)) :
    BpsBackgroundCouplingPackage data := by
  exact h_phys

/-- RR-charge quantization data for electric/magnetic dual D-branes. -/
structure RrChargeDiracQuantizationData where
  kappa : Real
  rrChargeDensityDp : Real
  rrChargeDensityDual : Real
  magneticFluxFromDualBraneSource : Bool
  diracQuantizationFromBraneActionSingleValuedness : Bool
  minimalChargeConditionSatisfied : Bool
  typeIIAAndTypeIIBPhysicalCouplingDictionariesUsed : Bool

/-- Section 14.5.3 package:
RR electric/magnetic duality and Dirac quantization of D-brane charges. -/
def RrChargeDiracQuantizationPackage
    (data : RrChargeDiracQuantizationData) : Prop :=
  data.kappa ≠ 0 /\
  data.rrChargeDensityDp * data.rrChargeDensityDual = Real.pi / (data.kappa ^ (2 : Nat)) /\
  data.magneticFluxFromDualBraneSource = true /\
  data.diracQuantizationFromBraneActionSingleValuedness = true /\
  data.minimalChargeConditionSatisfied = true /\
  data.typeIIAAndTypeIIBPhysicalCouplingDictionariesUsed = true

/-- Assumed Section 14.5.3 RR-charge quantization package. -/
theorem rr_charge_dirac_quantization_package
    (data : RrChargeDiracQuantizationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIRrChargeDiracQuantization
      (RrChargeDiracQuantizationPackage data)) :
    RrChargeDiracQuantizationPackage data := by
  exact h_phys

/-- General supersymmetric wrapped-D-brane condition data. -/
structure WrappedBraneSupersymmetryData where
  kappaProjectorConditionImplemented : Bool
  supersymmetryPreservationAsLinearProjectorConstraint : Bool
  matrixUpsilonSquaresToOneAlongConfiguration : Bool
  zeroWorldvolumeFluxLimitRecovered : Bool

/-- Section 14.6 package:
supersymmetric wrapped-D-brane criterion from kappa projector constraints. -/
def WrappedBraneSupersymmetryPackage
    (data : WrappedBraneSupersymmetryData) : Prop :=
  data.kappaProjectorConditionImplemented = true /\
  data.supersymmetryPreservationAsLinearProjectorConstraint = true /\
  data.matrixUpsilonSquaresToOneAlongConfiguration = true /\
  data.zeroWorldvolumeFluxLimitRecovered = true

/-- Assumed Section 14.6 wrapped-brane supersymmetry criterion package. -/
theorem wrapped_brane_supersymmetry_package
    (data : WrappedBraneSupersymmetryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIWrappedBraneSupersymmetry
      (WrappedBraneSupersymmetryPackage data)) :
    WrappedBraneSupersymmetryPackage data := by
  exact h_phys

/-- D2-brane holomorphic-curve BPS configuration data. -/
structure D2HolomorphicCurveBpsData where
  holomorphicEmbeddingInComplexCoordinates : Bool
  projectorConstraintsOnConstantSpinorImplemented : Bool
  quarterBpsFractionInFlatSpace : Bool
  halfBpsFractionInCalabiYauCompactification : Bool

/-- Section 14.6.1 package:
D2-branes wrapping holomorphic curves and corresponding preserved-supercharge
fractions in flat and compactified settings. -/
def D2HolomorphicCurveBpsPackage (data : D2HolomorphicCurveBpsData) : Prop :=
  data.holomorphicEmbeddingInComplexCoordinates = true /\
  data.projectorConstraintsOnConstantSpinorImplemented = true /\
  data.quarterBpsFractionInFlatSpace = true /\
  data.halfBpsFractionInCalabiYauCompactification = true

/-- Assumed Section 14.6.1 D2 holomorphic-curve BPS package. -/
theorem d2_holomorphic_curve_bps_package
    (data : D2HolomorphicCurveBpsData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIID2HolomorphicCurveBps
      (D2HolomorphicCurveBpsPackage data)) :
    D2HolomorphicCurveBpsPackage data := by
  exact h_phys

/-- D3-brane special-Lagrangian BPS configuration data. -/
structure D3SpecialLagrangianBpsData where
  lagrangianConditionOnEmbedding : Bool
  specialLagrangianPhaseConstraintOnHolomorphicThreeForm : Bool
  constantSpinorProjectorConstraintsImplemented : Bool
  eighthBpsFractionInFlatSpace : Bool
  halfBpsFractionInCalabiYauCompactification : Bool

/-- Section 14.6.2 package:
D3-branes wrapping special-Lagrangian cycles and supersymmetry projectors. -/
def D3SpecialLagrangianBpsPackage
    (data : D3SpecialLagrangianBpsData) : Prop :=
  data.lagrangianConditionOnEmbedding = true /\
  data.specialLagrangianPhaseConstraintOnHolomorphicThreeForm = true /\
  data.constantSpinorProjectorConstraintsImplemented = true /\
  data.eighthBpsFractionInFlatSpace = true /\
  data.halfBpsFractionInCalabiYauCompactification = true

/-- Assumed Section 14.6.2 D3 special-Lagrangian BPS package. -/
theorem d3_special_lagrangian_bps_package
    (data : D3SpecialLagrangianBpsData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIID3SpecialLagrangianBps
      (D3SpecialLagrangianBpsPackage data)) :
    D3SpecialLagrangianBpsPackage data := by
  exact h_phys

/-- Worldvolume-flux BPS and BIon configuration data. -/
structure WorldvolumeFluxBionData where
  bpsConditionRelatingTransverseSlopeAndElectricField : Bool
  quarterBpsProjectorConditionForBion : Bool
  bionCoulombLikeProfileExists : Bool
  bionEnergyDensityMatchesFundamentalStringTensionTimesCharge : Bool
  d1WithConstantElectricFieldInterpretedAsF1D1BoundState : Bool

/-- Section 14.6.3 package:
worldvolume flux preserving supersymmetry, including BIon solutions and
fundamental-string charge interpretation. -/
def WorldvolumeFluxBionPackage (data : WorldvolumeFluxBionData) : Prop :=
  data.bpsConditionRelatingTransverseSlopeAndElectricField = true /\
  data.quarterBpsProjectorConditionForBion = true /\
  data.bionCoulombLikeProfileExists = true /\
  data.bionEnergyDensityMatchesFundamentalStringTensionTimesCharge = true /\
  data.d1WithConstantElectricFieldInterpretedAsF1D1BoundState = true

/-- Assumed Section 14.6.3 worldvolume-flux/BIon package. -/
theorem worldvolume_flux_bion_package
    (data : WorldvolumeFluxBionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIIWorldvolumeFluxBion
      (WorldvolumeFluxBionPackage data)) :
    WorldvolumeFluxBionPackage data := by
  exact h_phys

/-- Non-Abelian low-energy effective theory data for coincident D-branes. -/
structure StackedDbraneNonAbelianData where
  stackSize : Nat
  maximallySupersymmetricYangMillsContentRealized : Bool
  scalarCommutatorPotentialPresent : Bool
  fermionYukawaCommutatorCouplingPresent : Bool
  adjointFieldContentFromChanPatonSector : Bool
  commutingScalarVacuaDiagonalizeToBranePositions : Bool
  stretchedStringMassFromEigenvalueSeparation : Bool

/-- Section 14.7 package:
low-energy non-Abelian worldvolume gauge theory for stacked D-branes. -/
def StackedDbraneNonAbelianPackage
    (data : StackedDbraneNonAbelianData) : Prop :=
  data.stackSize > 0 /\
  data.maximallySupersymmetricYangMillsContentRealized = true /\
  data.scalarCommutatorPotentialPresent = true /\
  data.fermionYukawaCommutatorCouplingPresent = true /\
  data.adjointFieldContentFromChanPatonSector = true /\
  data.commutingScalarVacuaDiagonalizeToBranePositions = true /\
  data.stretchedStringMassFromEigenvalueSeparation = true

/-- Assumed Section 14.7 stacked D-brane non-Abelian package. -/
theorem stacked_dbrane_non_abelian_package
    (data : StackedDbraneNonAbelianData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIINonAbelianStackedEffectiveTheory
      (StackedDbraneNonAbelianPackage data)) :
    StackedDbraneNonAbelianPackage data := by
  exact h_phys

/-- D0-brane scattering and BFSS matrix-quantum-mechanics data. -/
structure D0ScatteringBfssData where
  alphaPrime : Real
  typeIIAStringCoupling : Real
  d0Mass : Real
  movingD0CylinderAmplitudeComputed : Bool
  longDistancePotentialStartsAtV4OverR7 : Bool
  lowEnergyLimitGivesMatrixQuantumMechanics : Bool
  suNConstraintGeneratorConditionImplemented : Bool
  bfssHamiltonianAndSuperchargeAlgebraUsed : Bool
  thresholdBoundStateAndWittenIndexOneStatement : Bool

/-- Section 14.8 package:
D0-brane scattering from cylinder amplitudes and the BFSS matrix-QM effective
description of short-distance multi-D0 dynamics. -/
def D0ScatteringBfssPackage (data : D0ScatteringBfssData) : Prop :=
  data.alphaPrime > 0 /\
  data.typeIIAStringCoupling > 0 /\
  data.d0Mass = 1 / (data.typeIIAStringCoupling * Real.sqrt data.alphaPrime) /\
  data.movingD0CylinderAmplitudeComputed = true /\
  data.longDistancePotentialStartsAtV4OverR7 = true /\
  data.lowEnergyLimitGivesMatrixQuantumMechanics = true /\
  data.suNConstraintGeneratorConditionImplemented = true /\
  data.bfssHamiltonianAndSuperchargeAlgebraUsed = true /\
  data.thresholdBoundStateAndWittenIndexOneStatement = true

/-- Assumed Section 14.8 D0-scattering/BFSS package. -/
theorem d0_scattering_bfss_package
    (data : D0ScatteringBfssData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIID0ScatteringBfssMatrixQM
      (D0ScatteringBfssPackage data)) :
    D0ScatteringBfssPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
