import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Open+closed perturbative bosonic-string data in the presence of D-brane boundaries. -/
structure OpenClosedBosonicPerturbationData where
  alphaPrime : Real
  openStringNormalizationKo : Real
  representativeAmplitude : Complex
  representativeReducedAmplitude : Complex
  moduliIntegralAmplitudeFunctionalComplex : Bool
  openClosedAmplitudeHasGenusBoundaryExpansion : Bool
  moduliDimensionRuleApplied : Bool
  boundaryOrientationConventionFixed : Bool
  bpzStripConjugationDefined : Bool
  openPlumbingFixtureMapUsed : Bool
  openChannelFactorizationPoleMatching : Bool
  momentumDeltaFactorSeparated : Bool

/-- Section 13.1 package:
open+closed amplitudes as moduli-space integrals with boundary orientation,
open-channel factorization, and normalization recursion constraints. -/
def OpenClosedBosonicPerturbationPackage
    (data : OpenClosedBosonicPerturbationData) : Prop :=
  data.alphaPrime > 0 /\
  data.openStringNormalizationKo = -(1 / data.alphaPrime) /\
  data.moduliIntegralAmplitudeFunctionalComplex = true /\
  data.openClosedAmplitudeHasGenusBoundaryExpansion = true /\
  data.moduliDimensionRuleApplied = true /\
  data.boundaryOrientationConventionFixed = true /\
  data.bpzStripConjugationDefined = true /\
  data.openPlumbingFixtureMapUsed = true /\
  data.openChannelFactorizationPoleMatching = true /\
  data.momentumDeltaFactorSeparated = true

/-- Assumed Section 13.1 open+closed perturbation package. -/
theorem open_closed_bosonic_perturbation_package
    (data : OpenClosedBosonicPerturbationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicOpenClosedPerturbation
      (OpenClosedBosonicPerturbationPackage data)) :
    OpenClosedBosonicPerturbationPackage data := by
  exact h_phys

/-- Disc-level open-string tachyon amplitude data on a D-brane. -/
structure DiscOpenTachyonAmplitudeData where
  alphaPrime : Real
  openCoupling : Real
  reducedThreeTachyonAmplitude : Real
  discGhostMatterNormalizationFixed : Bool
  tachyonCubicEffectiveInteractionMatchesThreePoint : Bool
  fourTachyonVenezianoChannelDecomposition : Bool
  tachyonCondensationInterpretationRetained : Bool

/-- Section 13.2 disc-amplitude package:
3-point tachyon coupling and 4-point Veneziano channel structure on the disc. -/
def DiscOpenTachyonAmplitudePackage (data : DiscOpenTachyonAmplitudeData) : Prop :=
  data.alphaPrime > 0 /\
  data.reducedThreeTachyonAmplitude = -(2 * data.openCoupling / data.alphaPrime) /\
  data.discGhostMatterNormalizationFixed = true /\
  data.tachyonCubicEffectiveInteractionMatchesThreePoint = true /\
  data.fourTachyonVenezianoChannelDecomposition = true /\
  data.tachyonCondensationInterpretationRetained = true

/-- Assumed Section 13.2 disc tachyon-amplitude package. -/
theorem disc_open_tachyon_amplitude_package
    (data : DiscOpenTachyonAmplitudeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicDiscTachyonAmplitudes
      (DiscOpenTachyonAmplitudePackage data)) :
    DiscOpenTachyonAmplitudePackage data := by
  exact h_phys

/-- Chan-Paton and gauge-structure data from disc amplitudes. -/
structure DiscChanPatonGaugeData where
  stackSize : Nat
  chanPatonFactorizationUsed : Bool
  threeTachyonAmplitudeHasTraceOrdering : Bool
  gaugeBosonTwoTachyonAmplitudeCommutatorStructure : Bool
  nonAbelianCovariantDerivativeInEffectiveAction : Bool
  adjointTachyonRepresentationUsed : Bool

/-- Section 13.2 Chan-Paton package:
disc amplitudes on coincident D-branes produce nonabelian trace/commutator
structures and adjoint tachyon couplings. -/
def DiscChanPatonGaugePackage (data : DiscChanPatonGaugeData) : Prop :=
  data.stackSize > 0 /\
  data.chanPatonFactorizationUsed = true /\
  data.threeTachyonAmplitudeHasTraceOrdering = true /\
  data.gaugeBosonTwoTachyonAmplitudeCommutatorStructure = true /\
  data.nonAbelianCovariantDerivativeInEffectiveAction = true /\
  data.adjointTachyonRepresentationUsed = true

/-- Assumed Section 13.2 Chan-Paton/gauge package. -/
theorem disc_chan_paton_gauge_package
    (data : DiscChanPatonGaugeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicDiscChanPatonGaugeStructure
      (DiscChanPatonGaugePackage data)) :
    DiscChanPatonGaugePackage data := by
  exact h_phys

/-- Cylinder-amplitude data for bosonic D-brane dynamics. -/
structure CylinderBosonicDbraneAmplitudeData where
  cylinderOpenTraceRepresentation : Bool
  cylinderClosedBoundaryStateRepresentation : Bool
  openClosedChannelModularCrossingUsed : Bool
  twoBoundaryInteractionPotentialInterpretation : Bool
  tachyonExchangeIrDivergenceIdentified : Bool
  masslessClosedExchangeTermExtracted : Bool
  masslessClosedExchangeMultiplicity : Nat

/-- Section 13.3 package:
cylinder amplitudes in open and closed channels with modular duality and
massless-exchange extraction. -/
def CylinderBosonicDbraneAmplitudePackage
    (data : CylinderBosonicDbraneAmplitudeData) : Prop :=
  data.cylinderOpenTraceRepresentation = true /\
  data.cylinderClosedBoundaryStateRepresentation = true /\
  data.openClosedChannelModularCrossingUsed = true /\
  data.twoBoundaryInteractionPotentialInterpretation = true /\
  data.tachyonExchangeIrDivergenceIdentified = true /\
  data.masslessClosedExchangeTermExtracted = true /\
  data.masslessClosedExchangeMultiplicity = 24

/-- Assumed Section 13.3 cylinder-amplitude package. -/
theorem cylinder_bosonic_dbrane_amplitude_package
    (data : CylinderBosonicDbraneAmplitudeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicCylinderOpenClosedDuality
      (CylinderBosonicDbraneAmplitudePackage data)) :
    CylinderBosonicDbraneAmplitudePackage data := by
  exact h_phys

/-- Nambu-Goto and tension-matching data for bosonic D-branes. -/
structure DbraneNambuGotoTensionData where
  alphaPrime : Real
  openCoupling : Real
  braneTension : Real
  worldvolumeReparameterizationGaugeRedundancy : Bool
  inducedMetricFromEmbeddingFields : Bool
  staticGaugeExpansionToQuarticDerivativeOrder : Bool
  masslessNgBosonsMatchedToOpenStringModes : Bool
  tensionMatchedFromLowEnergyDiscAmplitude : Bool

/-- Section 13.4 package:
Nambu-Goto worldvolume dynamics and low-energy matching of D-brane tension to
open-string coupling data. -/
def DbraneNambuGotoTensionPackage
    (data : DbraneNambuGotoTensionData) : Prop :=
  data.alphaPrime > 0 /\
  data.openCoupling ≠ 0 /\
  data.braneTension =
    1 / (2 * (Real.pi ^ (2 : Nat)) * data.alphaPrime * data.openCoupling ^ (2 : Nat)) /\
  data.worldvolumeReparameterizationGaugeRedundancy = true /\
  data.inducedMetricFromEmbeddingFields = true /\
  data.staticGaugeExpansionToQuarticDerivativeOrder = true /\
  data.masslessNgBosonsMatchedToOpenStringModes = true /\
  data.tensionMatchedFromLowEnergyDiscAmplitude = true

/-- Assumed Section 13.4 Nambu-Goto/tension package. -/
theorem dbrane_nambu_goto_tension_package
    (data : DbraneNambuGotoTensionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicNambuGotoTensionMatching
      (DbraneNambuGotoTensionPackage data)) :
    DbraneNambuGotoTensionPackage data := by
  exact h_phys

/-- Dilaton and T-duality data for bosonic D-brane effective actions. -/
structure DbraneDilatonTDualityData where
  alphaPrime : Real
  compactRadius : Real
  dualRadius : Real
  stringCoupling : Real
  dualStringCoupling : Real
  dilatonExponentialPrefactorInAction : Bool
  leftRightReflectionInDualCoordinate : Bool
  tensionDimensionalReductionRelationUsed : Bool
  energyDensityMatchUnderTDuality : Bool

/-- Section 13.4.1 package:
dilaton prefactor and T-duality relations for radius/coupling and tension
consistency across Dp <-> D(p-1) descriptions. -/
def DbraneDilatonTDualityPackage (data : DbraneDilatonTDualityData) : Prop :=
  data.alphaPrime > 0 /\
  data.compactRadius > 0 /\
  data.dualRadius = data.alphaPrime / data.compactRadius /\
  data.dualStringCoupling = Real.sqrt data.alphaPrime / data.compactRadius * data.stringCoupling /\
  data.dilatonExponentialPrefactorInAction = true /\
  data.leftRightReflectionInDualCoordinate = true /\
  data.tensionDimensionalReductionRelationUsed = true /\
  data.energyDensityMatchUnderTDuality = true

/-- Assumed Section 13.4.1 dilaton/T-duality package. -/
theorem dbrane_dilaton_t_duality_package
    (data : DbraneDilatonTDualityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicDilatonTDualityRelations
      (DbraneDilatonTDualityPackage data)) :
    DbraneDilatonTDualityPackage data := by
  exact h_phys

/-- Gauge-field and Born-Infeld data for bosonic D-branes. -/
structure DbraneBornInfeldGaugeData where
  worldsheetBoundaryCouplingIncludesBandA : Bool
  bFieldGaugeVariationCompensatedByWorldvolumeGaugeShift : Bool
  gaugeInvariantCombinationBplusTwoPiAlphaPrimeF : Bool
  tDualityDerivationOfFieldStrengthDependence : Bool
  bornInfeldSqrtDetStructureForSlowlyVaryingFields : Bool
  dbiActionIncludesDilatonAndPullbackBField : Bool

/-- Section 13.4.2 package:
gauge invariance and T-duality determine the DBI dependence on
`G + B + 2 pi alpha' F` (up to derivative corrections). -/
def DbraneBornInfeldGaugePackage (data : DbraneBornInfeldGaugeData) : Prop :=
  data.worldsheetBoundaryCouplingIncludesBandA = true /\
  data.bFieldGaugeVariationCompensatedByWorldvolumeGaugeShift = true /\
  data.gaugeInvariantCombinationBplusTwoPiAlphaPrimeF = true /\
  data.tDualityDerivationOfFieldStrengthDependence = true /\
  data.bornInfeldSqrtDetStructureForSlowlyVaryingFields = true /\
  data.dbiActionIncludesDilatonAndPullbackBField = true

/-- Assumed Section 13.4.2 Born-Infeld/gauge package. -/
theorem dbrane_born_infeld_gauge_package
    (data : DbraneBornInfeldGaugeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicBornInfeldGaugeInvariance
      (DbraneBornInfeldGaugePackage data)) :
    DbraneBornInfeldGaugePackage data := by
  exact h_phys

/-- Graviton/dilaton-exchange data for separated parallel bosonic D-branes. -/
structure DbraneGravitonDilatonExchangeData where
  alphaPrime : Real
  kappa : Real
  braneTension : Real
  einsteinFrameRescalingUsed : Bool
  linearizedBraneCouplingsExtracted : Bool
  deDonderGaugeFixingUsed : Bool
  gravitonAndDilatonPropagatorsUsed : Bool
  masslessExchangeMatchesCylinderConstantTerm : Bool
  kappaTensionNormalizationConsistencyChecked : Bool

/-- Section 13.5 package:
effective-theory graviton/dilaton exchange between D-branes matches the
massless term in the cylinder-channel expansion and reproduces tension/coupling
consistency relations. -/
def DbraneGravitonDilatonExchangePackage
    (data : DbraneGravitonDilatonExchangeData) : Prop :=
  data.alphaPrime > 0 /\
  data.kappa ≠ 0 /\
  data.braneTension > 0 /\
  data.einsteinFrameRescalingUsed = true /\
  data.linearizedBraneCouplingsExtracted = true /\
  data.deDonderGaugeFixingUsed = true /\
  data.gravitonAndDilatonPropagatorsUsed = true /\
  data.masslessExchangeMatchesCylinderConstantTerm = true /\
  data.kappaTensionNormalizationConsistencyChecked = true

/-- Assumed Section 13.5 graviton/dilaton exchange package. -/
theorem dbrane_graviton_dilaton_exchange_package
    (data : DbraneGravitonDilatonExchangeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicGravitonDilatonExchange
      (DbraneGravitonDilatonExchangePackage data)) :
    DbraneGravitonDilatonExchangePackage data := by
  exact h_phys

/-- `c=1` ZZ-brane and rolling-tachyon data. -/
structure COneZzRollingTachyonData where
  alphaPrime : Real
  stringCoupling : Real
  zzBraneMass : Real
  zzBoundaryStateFromCylinderCrossing : Bool
  zzOpenSpectrumContainsTachyon : Bool
  zzMassMatchesMqmFermionThreshold : Bool
  rollingTachyonBoundaryDeformationExactlyMarginal : Bool
  rollingTachyonEnergyExpansionControlled : Bool

/-- Section 13.6.1 package:
ZZ-brane boundary-state normalization, open-string tachyon instability, and
rolling-tachyon marginal deformation with MQM interpretation. -/
def COneZzRollingTachyonPackage (data : COneZzRollingTachyonData) : Prop :=
  data.alphaPrime > 0 /\
  data.stringCoupling > 0 /\
  data.zzBraneMass =
    1 / (4 * Real.pi * Real.sqrt data.alphaPrime * data.stringCoupling) /\
  data.zzBoundaryStateFromCylinderCrossing = true /\
  data.zzOpenSpectrumContainsTachyon = true /\
  data.zzMassMatchesMqmFermionThreshold = true /\
  data.rollingTachyonBoundaryDeformationExactlyMarginal = true /\
  data.rollingTachyonEnergyExpansionControlled = true

/-- Assumed Section 13.6.1 ZZ/rolling-tachyon package. -/
theorem cone_zz_rolling_tachyon_package
    (data : COneZzRollingTachyonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicCOneZzRollingTachyon
      (COneZzRollingTachyonPackage data)) :
    COneZzRollingTachyonPackage data := by
  exact h_phys

/-- `c=1` FZZT-brane and long-string data. -/
structure COneFzztLongStringData where
  alphaPrime : Real
  sParameter : Real
  zzFzztOpenStringEnergy : Real
  fzztBoundaryWavefunctionFromCylinderCrossing : Bool
  fzztUnitaryRangeConstraintUsed : Bool
  fzztStableRangeWithoutRelevantBoundaryDeformation : Bool
  longStringDoubleScalingLimitUsed : Bool
  longStringRenormalizedEnergyFinite : Bool
  adjointMqmDualityForLongStringScattering : Bool

/-- Section 13.6.2 package:
FZZT boundary data, stability range, ZZ-FZZT stretched-string energy relation,
and long-string dual MQM interpretation. -/
def COneFzztLongStringPackage (data : COneFzztLongStringData) : Prop :=
  data.alphaPrime > 0 /\
  data.sParameter >= 0 /\
  data.zzFzztOpenStringEnergy = data.sParameter / Real.sqrt data.alphaPrime /\
  data.fzztBoundaryWavefunctionFromCylinderCrossing = true /\
  data.fzztUnitaryRangeConstraintUsed = true /\
  data.fzztStableRangeWithoutRelevantBoundaryDeformation = true /\
  data.longStringDoubleScalingLimitUsed = true /\
  data.longStringRenormalizedEnergyFinite = true /\
  data.adjointMqmDualityForLongStringScattering = true

/-- Assumed Section 13.6.2 FZZT/long-string package. -/
theorem cone_fzzt_long_string_package
    (data : COneFzztLongStringData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicCOneFzztLongStrings
      (COneFzztLongStringPackage data)) :
    COneFzztLongStringPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
