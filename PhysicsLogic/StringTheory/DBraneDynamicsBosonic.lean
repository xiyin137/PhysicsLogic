import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev DbraneBosonicClaim := Prop

/-- Open+closed perturbative bosonic-string data in the presence of D-brane boundaries. -/
structure OpenClosedBosonicPerturbationData where
  alphaPrime : StringSlope
  openStringNormalizationKo : ScalingDimension
  representativeAmplitude : ComplexAmplitude
  representativeReducedAmplitude : ComplexAmplitude
  moduliIntegralAmplitudeFunctionalComplex : DbraneBosonicClaim
  openClosedAmplitudeHasGenusBoundaryExpansion : DbraneBosonicClaim
  moduliDimensionRuleApplied : DbraneBosonicClaim
  boundaryOrientationConventionFixed : DbraneBosonicClaim
  bpzStripConjugationDefined : DbraneBosonicClaim
  openPlumbingFixtureMapUsed : DbraneBosonicClaim
  openChannelFactorizationPoleMatching : DbraneBosonicClaim
  momentumDeltaFactorSeparated : DbraneBosonicClaim

/-- Section 13.1 package:
open+closed amplitudes as moduli-space integrals with boundary orientation,
open-channel factorization, and normalization recursion constraints. -/
def OpenClosedBosonicPerturbationPackage
    (data : OpenClosedBosonicPerturbationData) : Prop :=
  data.alphaPrime > 0 /\
  data.openStringNormalizationKo = -(1 / data.alphaPrime) /\
  data.moduliIntegralAmplitudeFunctionalComplex /\
  data.openClosedAmplitudeHasGenusBoundaryExpansion /\
  data.moduliDimensionRuleApplied /\
  data.boundaryOrientationConventionFixed /\
  data.bpzStripConjugationDefined /\
  data.openPlumbingFixtureMapUsed /\
  data.openChannelFactorizationPoleMatching /\
  data.momentumDeltaFactorSeparated

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
  alphaPrime : StringSlope
  openCoupling : DimensionlessCoupling
  reducedThreeTachyonAmplitude : ScalingDimension
  discGhostMatterNormalizationFixed : DbraneBosonicClaim
  tachyonCubicEffectiveInteractionMatchesThreePoint : DbraneBosonicClaim
  fourTachyonVenezianoChannelDecomposition : DbraneBosonicClaim
  tachyonCondensationInterpretationRetained : DbraneBosonicClaim

/-- Section 13.2 disc-amplitude package:
3-point tachyon coupling and 4-point Veneziano channel structure on the disc. -/
def DiscOpenTachyonAmplitudePackage (data : DiscOpenTachyonAmplitudeData) : Prop :=
  data.alphaPrime > 0 /\
  data.reducedThreeTachyonAmplitude = -(2 * data.openCoupling / data.alphaPrime) /\
  data.discGhostMatterNormalizationFixed /\
  data.tachyonCubicEffectiveInteractionMatchesThreePoint /\
  data.fourTachyonVenezianoChannelDecomposition /\
  data.tachyonCondensationInterpretationRetained

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
  chanPatonFactorizationUsed : DbraneBosonicClaim
  threeTachyonAmplitudeHasTraceOrdering : DbraneBosonicClaim
  gaugeBosonTwoTachyonAmplitudeCommutatorStructure : DbraneBosonicClaim
  nonAbelianCovariantDerivativeInEffectiveAction : DbraneBosonicClaim
  adjointTachyonRepresentationUsed : DbraneBosonicClaim

/-- Section 13.2 Chan-Paton package:
disc amplitudes on coincident D-branes produce nonabelian trace/commutator
structures and adjoint tachyon couplings. -/
def DiscChanPatonGaugePackage (data : DiscChanPatonGaugeData) : Prop :=
  data.stackSize > 0 /\
  data.chanPatonFactorizationUsed /\
  data.threeTachyonAmplitudeHasTraceOrdering /\
  data.gaugeBosonTwoTachyonAmplitudeCommutatorStructure /\
  data.nonAbelianCovariantDerivativeInEffectiveAction /\
  data.adjointTachyonRepresentationUsed

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
  cylinderOpenTraceRepresentation : DbraneBosonicClaim
  cylinderClosedBoundaryStateRepresentation : DbraneBosonicClaim
  openClosedChannelModularCrossingUsed : DbraneBosonicClaim
  twoBoundaryInteractionPotentialInterpretation : DbraneBosonicClaim
  tachyonExchangeIrDivergenceIdentified : DbraneBosonicClaim
  masslessClosedExchangeTermExtracted : DbraneBosonicClaim
  masslessClosedExchangeMultiplicity : Nat

/-- Section 13.3 package:
cylinder amplitudes in open and closed channels with modular duality and
massless-exchange extraction. -/
def CylinderBosonicDbraneAmplitudePackage
    (data : CylinderBosonicDbraneAmplitudeData) : Prop :=
  data.cylinderOpenTraceRepresentation /\
  data.cylinderClosedBoundaryStateRepresentation /\
  data.openClosedChannelModularCrossingUsed /\
  data.twoBoundaryInteractionPotentialInterpretation /\
  data.tachyonExchangeIrDivergenceIdentified /\
  data.masslessClosedExchangeTermExtracted /\
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
  alphaPrime : StringSlope
  openCoupling : DimensionlessCoupling
  braneTension : TensionScale
  worldvolumeReparameterizationGaugeRedundancy : DbraneBosonicClaim
  inducedMetricFromEmbeddingFields : DbraneBosonicClaim
  staticGaugeExpansionToQuarticDerivativeOrder : DbraneBosonicClaim
  masslessNgBosonsMatchedToOpenStringModes : DbraneBosonicClaim
  tensionMatchedFromLowEnergyDiscAmplitude : DbraneBosonicClaim

/-- Section 13.4 package:
Nambu-Goto worldvolume dynamics and low-energy matching of D-brane tension to
open-string coupling data. -/
def DbraneNambuGotoTensionPackage
    (data : DbraneNambuGotoTensionData) : Prop :=
  data.alphaPrime > 0 /\
  data.openCoupling ≠ 0 /\
  data.braneTension =
    1 / (2 * (Real.pi ^ (2 : Nat)) * data.alphaPrime * data.openCoupling ^ (2 : Nat)) /\
  data.worldvolumeReparameterizationGaugeRedundancy /\
  data.inducedMetricFromEmbeddingFields /\
  data.staticGaugeExpansionToQuarticDerivativeOrder /\
  data.masslessNgBosonsMatchedToOpenStringModes /\
  data.tensionMatchedFromLowEnergyDiscAmplitude

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
  alphaPrime : StringSlope
  compactRadius : LengthScale
  dualRadius : LengthScale
  stringCoupling : DimensionlessCoupling
  dualStringCoupling : DimensionlessCoupling
  dilatonExponentialPrefactorInAction : DbraneBosonicClaim
  leftRightReflectionInDualCoordinate : DbraneBosonicClaim
  tensionDimensionalReductionRelationUsed : DbraneBosonicClaim
  energyDensityMatchUnderTDuality : DbraneBosonicClaim

/-- Section 13.4.1 package:
dilaton prefactor and T-duality relations for radius/coupling and tension
consistency across Dp <-> D(p-1) descriptions. -/
def DbraneDilatonTDualityPackage (data : DbraneDilatonTDualityData) : Prop :=
  data.alphaPrime > 0 /\
  data.compactRadius > 0 /\
  data.dualRadius = data.alphaPrime / data.compactRadius /\
  data.dualStringCoupling = Real.sqrt data.alphaPrime / data.compactRadius * data.stringCoupling /\
  data.dilatonExponentialPrefactorInAction /\
  data.leftRightReflectionInDualCoordinate /\
  data.tensionDimensionalReductionRelationUsed /\
  data.energyDensityMatchUnderTDuality

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
  worldsheetBoundaryCouplingIncludesBandA : DbraneBosonicClaim
  bFieldGaugeVariationCompensatedByWorldvolumeGaugeShift : DbraneBosonicClaim
  gaugeInvariantCombinationBplusTwoPiAlphaPrimeF : DbraneBosonicClaim
  tDualityDerivationOfFieldStrengthDependence : DbraneBosonicClaim
  bornInfeldSqrtDetStructureForSlowlyVaryingFields : DbraneBosonicClaim
  dbiActionIncludesDilatonAndPullbackBField : DbraneBosonicClaim

/-- Section 13.4.2 package:
gauge invariance and T-duality determine the DBI dependence on
`G + B + 2 pi alpha' F` (up to derivative corrections). -/
def DbraneBornInfeldGaugePackage (data : DbraneBornInfeldGaugeData) : Prop :=
  data.worldsheetBoundaryCouplingIncludesBandA /\
  data.bFieldGaugeVariationCompensatedByWorldvolumeGaugeShift /\
  data.gaugeInvariantCombinationBplusTwoPiAlphaPrimeF /\
  data.tDualityDerivationOfFieldStrengthDependence /\
  data.bornInfeldSqrtDetStructureForSlowlyVaryingFields /\
  data.dbiActionIncludesDilatonAndPullbackBField

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
  alphaPrime : StringSlope
  kappa : CouplingScale
  braneTension : TensionScale
  einsteinFrameRescalingUsed : DbraneBosonicClaim
  linearizedBraneCouplingsExtracted : DbraneBosonicClaim
  deDonderGaugeFixingUsed : DbraneBosonicClaim
  gravitonAndDilatonPropagatorsUsed : DbraneBosonicClaim
  masslessExchangeMatchesCylinderConstantTerm : DbraneBosonicClaim
  kappaTensionNormalizationConsistencyChecked : DbraneBosonicClaim

/-- Section 13.5 package:
effective-theory graviton/dilaton exchange between D-branes matches the
massless term in the cylinder-channel expansion and reproduces tension/coupling
consistency relations. -/
def DbraneGravitonDilatonExchangePackage
    (data : DbraneGravitonDilatonExchangeData) : Prop :=
  data.alphaPrime > 0 /\
  data.kappa ≠ 0 /\
  data.braneTension > 0 /\
  data.einsteinFrameRescalingUsed /\
  data.linearizedBraneCouplingsExtracted /\
  data.deDonderGaugeFixingUsed /\
  data.gravitonAndDilatonPropagatorsUsed /\
  data.masslessExchangeMatchesCylinderConstantTerm /\
  data.kappaTensionNormalizationConsistencyChecked

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
  alphaPrime : StringSlope
  stringCoupling : DimensionlessCoupling
  zzBraneMass : InvariantMass
  zzBoundaryStateFromCylinderCrossing : DbraneBosonicClaim
  zzOpenSpectrumContainsTachyon : DbraneBosonicClaim
  zzMassMatchesMqmFermionThreshold : DbraneBosonicClaim
  rollingTachyonBoundaryDeformationExactlyMarginal : DbraneBosonicClaim
  rollingTachyonEnergyExpansionControlled : DbraneBosonicClaim

/-- Section 13.6.1 package:
ZZ-brane boundary-state normalization, open-string tachyon instability, and
rolling-tachyon marginal deformation with MQM interpretation. -/
def COneZzRollingTachyonPackage (data : COneZzRollingTachyonData) : Prop :=
  data.alphaPrime > 0 /\
  data.stringCoupling > 0 /\
  data.zzBraneMass =
    1 / (4 * Real.pi * Real.sqrt data.alphaPrime * data.stringCoupling) /\
  data.zzBoundaryStateFromCylinderCrossing /\
  data.zzOpenSpectrumContainsTachyon /\
  data.zzMassMatchesMqmFermionThreshold /\
  data.rollingTachyonBoundaryDeformationExactlyMarginal /\
  data.rollingTachyonEnergyExpansionControlled

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
  alphaPrime : StringSlope
  sParameter : Real
  zzFzztOpenStringEnergy : Energy
  fzztBoundaryWavefunctionFromCylinderCrossing : DbraneBosonicClaim
  fzztUnitaryRangeConstraintUsed : DbraneBosonicClaim
  fzztStableRangeWithoutRelevantBoundaryDeformation : DbraneBosonicClaim
  longStringDoubleScalingLimitUsed : DbraneBosonicClaim
  longStringRenormalizedEnergyFinite : DbraneBosonicClaim
  adjointMqmDualityForLongStringScattering : DbraneBosonicClaim

/-- Section 13.6.2 package:
FZZT boundary data, stability range, ZZ-FZZT stretched-string energy relation,
and long-string dual MQM interpretation. -/
def COneFzztLongStringPackage (data : COneFzztLongStringData) : Prop :=
  data.alphaPrime > 0 /\
  data.sParameter >= 0 /\
  data.zzFzztOpenStringEnergy = data.sParameter / Real.sqrt data.alphaPrime /\
  data.fzztBoundaryWavefunctionFromCylinderCrossing /\
  data.fzztUnitaryRangeConstraintUsed /\
  data.fzztStableRangeWithoutRelevantBoundaryDeformation /\
  data.longStringDoubleScalingLimitUsed /\
  data.longStringRenormalizedEnergyFinite /\
  data.adjointMqmDualityForLongStringScattering

/-- Assumed Section 13.6.2 FZZT/long-string package. -/
theorem cone_fzzt_long_string_package
    (data : COneFzztLongStringData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneDynamicsBosonicCOneFzztLongStrings
      (COneFzztLongStringPackage data)) :
    COneFzztLongStringPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
