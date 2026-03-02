import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev TypeIIDbraneClaim := Prop

/-- Open+closed type-II perturbative data on super Riemann surfaces with boundary. -/
structure OpenClosedTypeIIPerturbationData where
  alphaPrime : Real
  openStringNormalizationKo : Real
  representativeAmplitude : Complex
  representativeReducedAmplitude : Complex
  boundarySuperRiemannSurfaceTransitionRulesUsed : TypeIIDbraneClaim
  supermoduliDimensionRuleApplied : TypeIIDbraneClaim
  boundarySpinStructureSummationIncluded : TypeIIDbraneClaim
  pcoFiberIntegrationAndVerticalCorrectionsUsed : TypeIIDbraneClaim
  discGhostMatterNormalizationConventionFixed : TypeIIDbraneClaim
  openClosedCouplingDictionaryApplied : TypeIIDbraneClaim
  actionFunctionalInterfaceAllowsComplexValues : TypeIIDbraneClaim

/-- Section 14.1 package:
type-II open+closed amplitudes on BSRS supermoduli with spin-structure sums and
PCO/vertical-integration prescriptions. -/
def OpenClosedTypeIIPerturbationPackage
    (data : OpenClosedTypeIIPerturbationData) : Prop :=
  data.alphaPrime > 0 /\
  data.openStringNormalizationKo = -(1 / data.alphaPrime) /\
  data.boundarySuperRiemannSurfaceTransitionRulesUsed /\
  data.supermoduliDimensionRuleApplied /\
  data.boundarySpinStructureSummationIncluded /\
  data.pcoFiberIntegrationAndVerticalCorrectionsUsed /\
  data.discGhostMatterNormalizationConventionFixed /\
  data.openClosedCouplingDictionaryApplied /\
  data.actionFunctionalInterfaceAllowsComplexValues

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
  chanPatonTraceOrderingIncluded : TypeIIDbraneClaim
  threeGaugeBosonAmplitudeMatchesYangMillsVertex : TypeIIDbraneClaim
  fourGaugeBosonAmplitudeHasGammaFunctionChannelStructure : TypeIIDbraneClaim
  leadingLowEnergyLimitMatchesYangMillsFourPoint : TypeIIDbraneClaim
  alphaPrimeSquaredT8F4CorrectionIdentified : TypeIIDbraneClaim
  noOrderAlphaPrimeFcubeCorrection : TypeIIDbraneClaim

/-- Section 14.2 package:
disc open-superstring amplitudes on a D-brane stack, including Yang-Mills
matching and the first `alpha'^2 t8 F^4` correction. -/
def DiscOpenGaugeAmplitudePackage
    (data : DiscOpenGaugeAmplitudeData) : Prop :=
  data.alphaPrime > 0 /\
  data.openCoupling > 0 /\
  data.stackSize > 0 /\
  data.yMGaugeCoupling = data.openCoupling / Real.sqrt (8 * data.alphaPrime) /\
  data.chanPatonTraceOrderingIncluded /\
  data.threeGaugeBosonAmplitudeMatchesYangMillsVertex /\
  data.fourGaugeBosonAmplitudeHasGammaFunctionChannelStructure /\
  data.leadingLowEnergyLimitMatchesYangMillsFourPoint /\
  data.alphaPrimeSquaredT8F4CorrectionIdentified /\
  data.noOrderAlphaPrimeFcubeCorrection

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
  rrClosedAndNsOpenDiscAmplitudeComputed : TypeIIDbraneClaim
  worldvolumeChernSimonsCouplingA_wedge_FpIdentified : TypeIIDbraneClaim
  transverseDisplacementCouplingToF_pPlusTwoIdentified : TypeIIDbraneClaim
  dpBraneCarriesRrChargeUnderC_pPlusOne : TypeIIDbraneClaim
  couplingNormalizationMatchesBoundaryStateDictionary : TypeIIDbraneClaim

/-- Section 14.3 package:
disc amplitudes with one RR closed-string and one NS open-string insertion,
fixing Chern-Simons/worldvolume-displacement RR couplings. -/
def DiscOpenClosedRrCouplingPackage
    (data : DiscOpenClosedRrCouplingData) : Prop :=
  data.rrClosedAndNsOpenDiscAmplitudeComputed /\
  data.worldvolumeChernSimonsCouplingA_wedge_FpIdentified /\
  data.transverseDisplacementCouplingToF_pPlusTwoIdentified /\
  data.dpBraneCarriesRrChargeUnderC_pPlusOne /\
  data.couplingNormalizationMatchesBoundaryStateDictionary

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
  nsnsCylinderAmplitudeComputed : TypeIIDbraneClaim
  rrCylinderAmplitudeComputed : TypeIIDbraneClaim
  jacobiThetaIdentityUsedForSectorCancellation : TypeIIDbraneClaim
  parallelBpsBranePotentialCancels : TypeIIDbraneClaim
  antiBraneFlipsRrContributionSign : TypeIIDbraneClaim
  largeDistanceMasslessExchangeExtractionUsed : TypeIIDbraneClaim

/-- Section 14.4 package:
type-II cylinder NSNS/RR exchange structure and BPS-force cancellation for
parallel D-branes. -/
def CylinderTypeIICancellationPackage
    (data : CylinderTypeIICancellationData) : Prop :=
  data.nsnsCylinderAmplitudeComputed /\
  data.rrCylinderAmplitudeComputed /\
  data.jacobiThetaIdentityUsedForSectorCancellation /\
  data.parallelBpsBranePotentialCancels /\
  data.antiBraneFlipsRrContributionSign /\
  data.largeDistanceMasslessExchangeExtractionUsed

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
  supersymmetryInvariantPiAndCalFConstructed : TypeIIDbraneClaim
  dbiPlusWessZuminoActionUsed : TypeIIDbraneClaim
  kappaSymmetryProjectorSquaresToOne : TypeIIDbraneClaim
  staticGaugeAndKappaGaugeFixingImplemented : TypeIIDbraneClaim
  staticGaugeActionContainsGoldstinoAndBornInfeldData : TypeIIDbraneClaim
  t8f4MatchingFixesTension : TypeIIDbraneClaim

/-- Section 14.5.1 package:
flat-space supersymmetric/kappa-symmetric DBI+WZ action and its static-gauge
reduction to maximally supersymmetric worldvolume dynamics. -/
def BpsKappaSymmetricActionPackage
    (data : BpsKappaSymmetricActionData) : Prop :=
  data.alphaPrime > 0 /\
  data.openCoupling > 0 /\
  data.braneTension = 2 / (Real.pi ^ (2 : Nat) * data.alphaPrime * data.openCoupling ^ (2 : Nat)) /\
  data.supersymmetryInvariantPiAndCalFConstructed /\
  data.dbiPlusWessZuminoActionUsed /\
  data.kappaSymmetryProjectorSquaresToOne /\
  data.staticGaugeAndKappaGaugeFixingImplemented /\
  data.staticGaugeActionContainsGoldstinoAndBornInfeldData /\
  data.t8f4MatchingFixesTension

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
  dbiTermIncludesDilatonMetricBAndWorldvolumeF : TypeIIDbraneClaim
  wessZuminoTermIncludesRrPotentialSum : TypeIIDbraneClaim
  rrChargeDensityEqualsTension : TypeIIDbraneClaim
  gravitonDilatonExchangeMatchesCylinderLargeDistance : TypeIIDbraneClaim
  rrCouplingsMatchDiscOpenClosedAmplitudes : TypeIIDbraneClaim

/-- Section 14.5.2 package:
bosonic part of the BPS D-brane action in general backgrounds, including RR
Wess-Zumino couplings and force-cancellation consistency. -/
def BpsBackgroundCouplingPackage (data : BpsBackgroundCouplingData) : Prop :=
  data.dbiTermIncludesDilatonMetricBAndWorldvolumeF /\
  data.wessZuminoTermIncludesRrPotentialSum /\
  data.rrChargeDensityEqualsTension /\
  data.gravitonDilatonExchangeMatchesCylinderLargeDistance /\
  data.rrCouplingsMatchDiscOpenClosedAmplitudes

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
  magneticFluxFromDualBraneSource : TypeIIDbraneClaim
  diracQuantizationFromBraneActionSingleValuedness : TypeIIDbraneClaim
  minimalChargeConditionSatisfied : TypeIIDbraneClaim
  typeIIAAndTypeIIBPhysicalCouplingDictionariesUsed : TypeIIDbraneClaim

/-- Section 14.5.3 package:
RR electric/magnetic duality and Dirac quantization of D-brane charges. -/
def RrChargeDiracQuantizationPackage
    (data : RrChargeDiracQuantizationData) : Prop :=
  data.kappa ≠ 0 /\
  data.rrChargeDensityDp * data.rrChargeDensityDual = Real.pi / (data.kappa ^ (2 : Nat)) /\
  data.magneticFluxFromDualBraneSource /\
  data.diracQuantizationFromBraneActionSingleValuedness /\
  data.minimalChargeConditionSatisfied /\
  data.typeIIAAndTypeIIBPhysicalCouplingDictionariesUsed

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
  kappaProjectorConditionImplemented : TypeIIDbraneClaim
  supersymmetryPreservationAsLinearProjectorConstraint : TypeIIDbraneClaim
  matrixUpsilonSquaresToOneAlongConfiguration : TypeIIDbraneClaim
  zeroWorldvolumeFluxLimitRecovered : TypeIIDbraneClaim

/-- Section 14.6 package:
supersymmetric wrapped-D-brane criterion from kappa projector constraints. -/
def WrappedBraneSupersymmetryPackage
    (data : WrappedBraneSupersymmetryData) : Prop :=
  data.kappaProjectorConditionImplemented /\
  data.supersymmetryPreservationAsLinearProjectorConstraint /\
  data.matrixUpsilonSquaresToOneAlongConfiguration /\
  data.zeroWorldvolumeFluxLimitRecovered

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
  holomorphicEmbeddingInComplexCoordinates : TypeIIDbraneClaim
  projectorConstraintsOnConstantSpinorImplemented : TypeIIDbraneClaim
  quarterBpsFractionInFlatSpace : TypeIIDbraneClaim
  halfBpsFractionInCalabiYauCompactification : TypeIIDbraneClaim

/-- Section 14.6.1 package:
D2-branes wrapping holomorphic curves and corresponding preserved-supercharge
fractions in flat and compactified settings. -/
def D2HolomorphicCurveBpsPackage (data : D2HolomorphicCurveBpsData) : Prop :=
  data.holomorphicEmbeddingInComplexCoordinates /\
  data.projectorConstraintsOnConstantSpinorImplemented /\
  data.quarterBpsFractionInFlatSpace /\
  data.halfBpsFractionInCalabiYauCompactification

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
  lagrangianConditionOnEmbedding : TypeIIDbraneClaim
  specialLagrangianPhaseConstraintOnHolomorphicThreeForm : TypeIIDbraneClaim
  constantSpinorProjectorConstraintsImplemented : TypeIIDbraneClaim
  eighthBpsFractionInFlatSpace : TypeIIDbraneClaim
  halfBpsFractionInCalabiYauCompactification : TypeIIDbraneClaim

/-- Section 14.6.2 package:
D3-branes wrapping special-Lagrangian cycles and supersymmetry projectors. -/
def D3SpecialLagrangianBpsPackage
    (data : D3SpecialLagrangianBpsData) : Prop :=
  data.lagrangianConditionOnEmbedding /\
  data.specialLagrangianPhaseConstraintOnHolomorphicThreeForm /\
  data.constantSpinorProjectorConstraintsImplemented /\
  data.eighthBpsFractionInFlatSpace /\
  data.halfBpsFractionInCalabiYauCompactification

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
  bpsConditionRelatingTransverseSlopeAndElectricField : TypeIIDbraneClaim
  quarterBpsProjectorConditionForBion : TypeIIDbraneClaim
  bionCoulombLikeProfileExists : TypeIIDbraneClaim
  bionEnergyDensityMatchesFundamentalStringTensionTimesCharge : TypeIIDbraneClaim
  d1WithConstantElectricFieldInterpretedAsF1D1BoundState : TypeIIDbraneClaim

/-- Section 14.6.3 package:
worldvolume flux preserving supersymmetry, including BIon solutions and
fundamental-string charge interpretation. -/
def WorldvolumeFluxBionPackage (data : WorldvolumeFluxBionData) : Prop :=
  data.bpsConditionRelatingTransverseSlopeAndElectricField /\
  data.quarterBpsProjectorConditionForBion /\
  data.bionCoulombLikeProfileExists /\
  data.bionEnergyDensityMatchesFundamentalStringTensionTimesCharge /\
  data.d1WithConstantElectricFieldInterpretedAsF1D1BoundState

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
  maximallySupersymmetricYangMillsContentRealized : TypeIIDbraneClaim
  scalarCommutatorPotentialPresent : TypeIIDbraneClaim
  fermionYukawaCommutatorCouplingPresent : TypeIIDbraneClaim
  adjointFieldContentFromChanPatonSector : TypeIIDbraneClaim
  commutingScalarVacuaDiagonalizeToBranePositions : TypeIIDbraneClaim
  stretchedStringMassFromEigenvalueSeparation : TypeIIDbraneClaim

/-- Section 14.7 package:
low-energy non-Abelian worldvolume gauge theory for stacked D-branes. -/
def StackedDbraneNonAbelianPackage
    (data : StackedDbraneNonAbelianData) : Prop :=
  data.stackSize > 0 /\
  data.maximallySupersymmetricYangMillsContentRealized /\
  data.scalarCommutatorPotentialPresent /\
  data.fermionYukawaCommutatorCouplingPresent /\
  data.adjointFieldContentFromChanPatonSector /\
  data.commutingScalarVacuaDiagonalizeToBranePositions /\
  data.stretchedStringMassFromEigenvalueSeparation

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
  movingD0CylinderAmplitudeComputed : TypeIIDbraneClaim
  longDistancePotentialStartsAtV4OverR7 : TypeIIDbraneClaim
  lowEnergyLimitGivesMatrixQuantumMechanics : TypeIIDbraneClaim
  suNConstraintGeneratorConditionImplemented : TypeIIDbraneClaim
  bfssHamiltonianAndSuperchargeAlgebraUsed : TypeIIDbraneClaim
  thresholdBoundStateAndWittenIndexOneStatement : TypeIIDbraneClaim

/-- Section 14.8 package:
D0-brane scattering from cylinder amplitudes and the BFSS matrix-QM effective
description of short-distance multi-D0 dynamics. -/
def D0ScatteringBfssPackage (data : D0ScatteringBfssData) : Prop :=
  data.alphaPrime > 0 /\
  data.typeIIAStringCoupling > 0 /\
  data.d0Mass = 1 / (data.typeIIAStringCoupling * Real.sqrt data.alphaPrime) /\
  data.movingD0CylinderAmplitudeComputed /\
  data.longDistancePotentialStartsAtV4OverR7 /\
  data.lowEnergyLimitGivesMatrixQuantumMechanics /\
  data.suNConstraintGeneratorConditionImplemented /\
  data.bfssHamiltonianAndSuperchargeAlgebraUsed /\
  data.thresholdBoundStateAndWittenIndexOneStatement

/-- Assumed Section 14.8 D0-scattering/BFSS package. -/
theorem d0_scattering_bfss_package
    (data : D0ScatteringBfssData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsTypeIID0ScatteringBfssMatrixQM
      (D0ScatteringBfssPackage data)) :
    D0ScatteringBfssPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
