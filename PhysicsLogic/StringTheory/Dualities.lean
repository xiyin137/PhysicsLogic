import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Heterotic/type-I strong-weak duality dictionary data. -/
structure HeteroticTypeIDualityData where
  einsteinFrameActionsMatched : Bool
  dilatonIdentificationPhiHetEqualsMinusPhiI : Bool
  heteroticFundamentalStringMatchesTypeID1Tension : Bool
  heteroticNs5MapsToTypeID5 : Bool
  oneLoopHetAndTreeTypeIAnomalyCouplingsMatch : Bool
  nonBpsTypeID0MatchesHetSo32SpinorStates : Bool

/-- Section 18.1 package:
heterotic `SO(32)` / type-I strong-weak dictionary. -/
def HeteroticTypeIDualityPackage
    (data : HeteroticTypeIDualityData) : Prop :=
  data.einsteinFrameActionsMatched = true /\
  data.dilatonIdentificationPhiHetEqualsMinusPhiI = true /\
  data.heteroticFundamentalStringMatchesTypeID1Tension = true /\
  data.heteroticNs5MapsToTypeID5 = true /\
  data.oneLoopHetAndTreeTypeIAnomalyCouplingsMatch = true /\
  data.nonBpsTypeID0MatchesHetSo32SpinorStates = true

/-- Assumed Section 18.1 heterotic/type-I duality package. -/
theorem heterotic_type_i_duality_package
    (data : HeteroticTypeIDualityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityHeteroticTypeIStrongWeak
      (HeteroticTypeIDualityPackage data)) :
    HeteroticTypeIDualityPackage data := by
  exact h_phys

/-- Type-II NS5-brane BPS supergravity-solution data. -/
structure TypeIINs5BpsData where
  ns5Charge : Nat
  hFluxDiracQuantizationUsed : Bool
  bpsMetricDilatonAndHFluxAnsatzUsed : Bool
  killingSpinorProjectionHalfBps : Bool
  ns5StringFrameSolutionWithHarmonicUofr : Bool
  ns5TensionScalesAsInverseStringCouplingSquared : Bool

/-- Section 18.2.1 package:
type-II NS5-brane BPS solution and charge/tension dictionary. -/
def TypeIINs5BpsPackage (data : TypeIINs5BpsData) : Prop :=
  data.ns5Charge > 0 /\
  data.hFluxDiracQuantizationUsed = true /\
  data.bpsMetricDilatonAndHFluxAnsatzUsed = true /\
  data.killingSpinorProjectionHalfBps = true /\
  data.ns5StringFrameSolutionWithHarmonicUofr = true /\
  data.ns5TensionScalesAsInverseStringCouplingSquared = true

/-- Assumed Section 18.2.1 type-II NS5 BPS package. -/
theorem type_ii_ns5_bps_package
    (data : TypeIINs5BpsData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityTypeIINS5BpsSoliton
      (TypeIINs5BpsPackage data)) :
    TypeIINs5BpsPackage data := by
  exact h_phys

/-- NS5 throat worldsheet SCFT data. -/
structure Ns5ThroatScftData where
  levelK : Nat
  nearThroatLinearDilatonAndS3GeometryUsed : Bool
  worldsheetFactorizationR15LinearDilatonSU2k : Bool
  littleStringTheoryInterpretationUsed : Bool
  exactWzwDescriptionForLevelAtLeastTwo : Bool

/-- Section 18.2.2 package:
NS5 throat SCFT and little-string-theory interpretation. -/
def Ns5ThroatScftPackage (data : Ns5ThroatScftData) : Prop :=
  data.levelK > 0 /\
  data.nearThroatLinearDilatonAndS3GeometryUsed = true /\
  data.worldsheetFactorizationR15LinearDilatonSU2k = true /\
  data.littleStringTheoryInterpretationUsed = true /\
  data.exactWzwDescriptionForLevelAtLeastTwo = true

/-- Assumed Section 18.2.2 NS5-throat SCFT package. -/
theorem ns5_throat_scft_package
    (data : Ns5ThroatScftData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityNS5ThroatLittleStringScft
      (Ns5ThroatScftPackage data)) :
    Ns5ThroatScftPackage data := by
  exact h_phys

/-- Heterotic NS5/gauge-instanton correspondence data. -/
structure HeteroticNs5InstantonData where
  hhatFluxQuantizationAtInfinityUsed : Bool
  supersymmetryRequiresSelfDualGaugeInstanton : Bool
  modifiedBianchiSourcesDilatonProfile : Bool
  instantonNumberQuantizationUsed : Bool
  smallInstantonLimitMatchesHeteroticNs5 : Bool
  heteroticNs5ToTypeID5DualityConsistency : Bool

/-- Section 18.2.3 package:
heterotic NS5-brane as small-instanton limit of gauge instantons. -/
def HeteroticNs5InstantonPackage
    (data : HeteroticNs5InstantonData) : Prop :=
  data.hhatFluxQuantizationAtInfinityUsed = true /\
  data.supersymmetryRequiresSelfDualGaugeInstanton = true /\
  data.modifiedBianchiSourcesDilatonProfile = true /\
  data.instantonNumberQuantizationUsed = true /\
  data.smallInstantonLimitMatchesHeteroticNs5 = true /\
  data.heteroticNs5ToTypeID5DualityConsistency = true

/-- Assumed Section 18.2.3 heterotic NS5/gauge-instanton package. -/
theorem heterotic_ns5_instanton_package
    (data : HeteroticNs5InstantonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityHeteroticNS5GaugeInstantonSmallInstanton
      (HeteroticNs5InstantonPackage data)) :
    HeteroticNs5InstantonPackage data := by
  exact h_phys

/-- Type-IIB S-duality and modular-coupling data. -/
structure TypeIibSdualityData where
  lowEnergySl2RActsOnAxioDilatonAndTwoForms : Bool
  exactStringDualityReducedToSl2Z : Bool
  fourGravitonR4CouplingObeysModularLaplacianEquation : Bool
  eisensteinEThreeHalfSolutionSelectedByDualityAndAsymptotics : Bool
  oneLoopAndDInstantonChecksMatchModularPrediction : Bool

/-- Section 18.3 package:
type-IIB S-duality and modularly completed `R^4` coupling. -/
def TypeIibSdualityPackage (data : TypeIibSdualityData) : Prop :=
  data.lowEnergySl2RActsOnAxioDilatonAndTwoForms = true /\
  data.exactStringDualityReducedToSl2Z = true /\
  data.fourGravitonR4CouplingObeysModularLaplacianEquation = true /\
  data.eisensteinEThreeHalfSolutionSelectedByDualityAndAsymptotics = true /\
  data.oneLoopAndDInstantonChecksMatchModularPrediction = true

/-- Assumed Section 18.3 type-IIB S-duality package. -/
theorem type_iib_s_duality_package
    (data : TypeIibSdualityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityTypeIIBSdualityModularInvariantCouplings
      (TypeIibSdualityPackage data)) :
    TypeIibSdualityPackage data := by
  exact h_phys

/-- `(p,q)` string and 5-brane bound-state data in type IIB. -/
structure PqStringsFiveBranesData where
  d1WorldvolumeElectricFluxQuantizationUsed : Bool
  f1D1ExchangedBySGenerator : Bool
  pOneBoundStateTensionFormulaUsed : Bool
  generalPqStringTensionFormulaUsed : Bool
  sl2zOrbitGeneratesPqFiveBraneFamily : Bool

/-- Section 18.4 package:
`(p,q)` strings and 5-branes from SL(2,Z) duality orbits. -/
def PqStringsFiveBranesPackage (data : PqStringsFiveBranesData) : Prop :=
  data.d1WorldvolumeElectricFluxQuantizationUsed = true /\
  data.f1D1ExchangedBySGenerator = true /\
  data.pOneBoundStateTensionFormulaUsed = true /\
  data.generalPqStringTensionFormulaUsed = true /\
  data.sl2zOrbitGeneratesPqFiveBraneFamily = true

/-- Assumed Section 18.4 `(p,q)` strings/5-branes package. -/
theorem pq_strings_five_branes_package
    (data : PqStringsFiveBranesData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityPQStringsAndFiveBranes
      (PqStringsFiveBranesPackage data)) :
    PqStringsFiveBranesPackage data := by
  exact h_phys

/-- Black p-brane supergravity dictionary data. -/
structure BlackPBraneData where
  braneDimension : Nat
  braneNumber : Nat
  rrFluxQuantizationConditionUsed : Bool
  bpsBlackBraneWarpedMetricAndFieldStrengthUsed : Bool
  radiusAndChargeDictionaryWithBraneNumberUsed : Bool
  supergravityValidityConditionsLargeNAndLargeEffectiveCouplingUsed : Bool

/-- Section 18.5 package:
RR-charged black p-brane supergravity solutions and parameter dictionaries. -/
def BlackPBranePackage (data : BlackPBraneData) : Prop :=
  data.braneDimension ≤ 8 /\
  data.braneNumber > 0 /\
  data.rrFluxQuantizationConditionUsed = true /\
  data.bpsBlackBraneWarpedMetricAndFieldStrengthUsed = true /\
  data.radiusAndChargeDictionaryWithBraneNumberUsed = true /\
  data.supergravityValidityConditionsLargeNAndLargeEffectiveCouplingUsed = true

/-- Assumed Section 18.5 black p-brane package. -/
theorem black_p_brane_package
    (data : BlackPBraneData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityBlackPBraneSupergravityDictionary
      (BlackPBranePackage data)) :
    BlackPBranePackage data := by
  exact h_phys

/-- D7/F-theory monodromy-geometry dictionary data. -/
structure D7FTheoryData where
  axioDilatonHasSl2ZMonodromyProfile : Bool
  jInvariantEllipticFibrationAnsatzUsed : Bool
  supersymmetryKillingSpinorConstraintApplied : Bool
  fTheoryOnEllipticK3InterpretationUsed : Bool
  senLimitMatchedToTypeIIBOrientifold : Bool

/-- Section 18.6 package:
D7-brane axio-dilaton monodromies and F-theory elliptic-fibration dictionary. -/
def D7FTheoryPackage (data : D7FTheoryData) : Prop :=
  data.axioDilatonHasSl2ZMonodromyProfile = true /\
  data.jInvariantEllipticFibrationAnsatzUsed = true /\
  data.supersymmetryKillingSpinorConstraintApplied = true /\
  data.fTheoryOnEllipticK3InterpretationUsed = true /\
  data.senLimitMatchedToTypeIIBOrientifold = true

/-- Assumed Section 18.6 D7/F-theory package. -/
theorem d7_f_theory_package
    (data : D7FTheoryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityD7BraneFTheoryEllipticMonodromy
      (D7FTheoryPackage data)) :
    D7FTheoryPackage data := by
  exact h_phys

/-- M-theory / type-IIA circle-reduction dictionary data. -/
structure MTheoryTypeIIACircleData where
  elevenDimensionalReductionReproducesTypeIIAFields : Bool
  kkMomentumModesMapToD0BoundStates : Bool
  mTheoryCircleRadiusMatchesTypeIIAStringCoupling : Bool
  elevenDimensionalPlanckScaleDictionaryUsed : Bool
  mTheoryAsStrongCouplingCompletionOfTypeIIA : Bool

/-- Section 18.7 package:
M-theory circle compactification and type-IIA dual dictionary. -/
def MTheoryTypeIIACirclePackage
    (data : MTheoryTypeIIACircleData) : Prop :=
  data.elevenDimensionalReductionReproducesTypeIIAFields = true /\
  data.kkMomentumModesMapToD0BoundStates = true /\
  data.mTheoryCircleRadiusMatchesTypeIIAStringCoupling = true /\
  data.elevenDimensionalPlanckScaleDictionaryUsed = true /\
  data.mTheoryAsStrongCouplingCompletionOfTypeIIA = true

/-- Assumed Section 18.7 M-theory/type-IIA circle package. -/
theorem m_theory_type_iia_circle_package
    (data : MTheoryTypeIIACircleData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityMTheoryTypeIIACircleRelation
      (MTheoryTypeIIACirclePackage data)) :
    MTheoryTypeIIACirclePackage data := by
  exact h_phys

/-- M2/M5 tension-and-wrapping dictionary data. -/
structure M2M5DictionaryData where
  m2ElectricChargeUnderC3Used : Bool
  m5MagneticChargeUnderC3Used : Bool
  m2AndM5TensionsScaleOnlyWithM11 : Bool
  wrappedM2MatchesFundamentalStringTension : Bool
  wrappedM5MatchesD4Tension : Bool

/-- Section 18.7.1 package:
M2/M5 brane tension relations and type-IIA wrapping maps. -/
def M2M5DictionaryPackage (data : M2M5DictionaryData) : Prop :=
  data.m2ElectricChargeUnderC3Used = true /\
  data.m5MagneticChargeUnderC3Used = true /\
  data.m2AndM5TensionsScaleOnlyWithM11 = true /\
  data.wrappedM2MatchesFundamentalStringTension = true /\
  data.wrappedM5MatchesD4Tension = true

/-- Assumed Section 18.7.1 M2/M5 dictionary package. -/
theorem m2_m5_dictionary_package
    (data : M2M5DictionaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityM2M5BraneTensionDictionary
      (M2M5DictionaryPackage data)) :
    M2M5DictionaryPackage data := by
  exact h_phys

/-- D6 / Kaluza-Klein monopole uplift data. -/
structure D6KkMonopoleData where
  taubNUTMetricUsedForMonopoleGeometry : Bool
  d6BraneMappedToKkMonopoleChargeSector : Bool
  smoothCoreUpToExpectedOrbifoldIdentification : Bool
  halfBpsKillingSpinorsPreserved : Bool
  upliftDictionaryMatchesTypeIIAParameterRelations : Bool

/-- Section 18.7.2 package:
D6-brane interpretation as Kaluza-Klein monopole in M-theory. -/
def D6KkMonopolePackage (data : D6KkMonopoleData) : Prop :=
  data.taubNUTMetricUsedForMonopoleGeometry = true /\
  data.d6BraneMappedToKkMonopoleChargeSector = true /\
  data.smoothCoreUpToExpectedOrbifoldIdentification = true /\
  data.halfBpsKillingSpinorsPreserved = true /\
  data.upliftDictionaryMatchesTypeIIAParameterRelations = true

/-- Assumed Section 18.7.2 D6/KK-monopole package. -/
theorem d6_kk_monopole_package
    (data : D6KkMonopoleData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityD6KaluzaKleinMonopoleUplift
      (D6KkMonopolePackage data)) :
    D6KkMonopolePackage data := by
  exact h_phys

/-- M-theory higher-derivative protected-coupling data. -/
structure MTheoryHigherDerivativeData where
  iiaToMTheoryDecompactificationLimitUsed : Bool
  rFourCouplingFromProtectedTypeIIAData : Bool
  dFourRFourConstraintAndD6RFourInformationUsed : Bool
  protectedTermsSurviveStrongCouplingLimit : Bool
  genericHigherDerivativeMTheoryCorrectionsUnknownBeyondProtectedSector : Bool

/-- Section 18.7.4 package:
protected higher-derivative couplings in M-theory from type-IIA data. -/
def MTheoryHigherDerivativePackage
    (data : MTheoryHigherDerivativeData) : Prop :=
  data.iiaToMTheoryDecompactificationLimitUsed = true /\
  data.rFourCouplingFromProtectedTypeIIAData = true /\
  data.dFourRFourConstraintAndD6RFourInformationUsed = true /\
  data.protectedTermsSurviveStrongCouplingLimit = true /\
  data.genericHigherDerivativeMTheoryCorrectionsUnknownBeyondProtectedSector = true

/-- Assumed Section 18.7.4 M-theory higher-derivative package. -/
theorem m_theory_higher_derivative_package
    (data : MTheoryHigherDerivativeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityMTheoryHigherDerivativeProtectedTerms
      (MTheoryHigherDerivativePackage data)) :
    MTheoryHigherDerivativePackage data := by
  exact h_phys

/-- Circle-compactified hetE/hetO Narain-lattice T-duality data. -/
structure HeteroticCircleTdualityData where
  narainLatticeWilsonLineDeformationUsed : Bool
  specificHetEAndHetOWilsonLineBackgroundsChosen : Bool
  latticeEmbeddingIsomorphismConstructedExplicitly : Bool
  radiusInversionWithRightMoverSignFlipApplied : Bool
  dualCompactificationBackgroundGaugeBreakingToSo16TimesSo16 : Bool

/-- Section 18.8.1 package:
hetE/hetO circle T-duality via Narain-lattice identification with Wilson lines. -/
def HeteroticCircleTdualityPackage
    (data : HeteroticCircleTdualityData) : Prop :=
  data.narainLatticeWilsonLineDeformationUsed = true /\
  data.specificHetEAndHetOWilsonLineBackgroundsChosen = true /\
  data.latticeEmbeddingIsomorphismConstructedExplicitly = true /\
  data.radiusInversionWithRightMoverSignFlipApplied = true /\
  data.dualCompactificationBackgroundGaugeBreakingToSo16TimesSo16 = true

/-- Assumed Section 18.8.1 heterotic-circle T-duality package. -/
theorem heterotic_circle_tduality_package
    (data : HeteroticCircleTdualityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityHeteroticE8SO32CircleTduality
      (HeteroticCircleTdualityPackage data)) :
    HeteroticCircleTdualityPackage data := by
  exact h_phys

/-- Strong-coupling hetE to M-theory-on-interval dictionary data. -/
structure HeteroticStrongCouplingIntervalData where
  dualityChainHetEToMTheoryIntervalUsed : Bool
  mTheoryIntervalLengthScalesWithHetECoupling : Bool
  boundaryGaugeSymmetryEnhancedToE8TimesE8 : Bool
  heteroticStringRealizedAsStretchedM2 : Bool
  boundaryGaugeCouplingMatchesPlanckScaleDictionary : Bool

/-- Sections 18.8.2 and 18.8.4 package:
strong-coupling hetE as M-theory on an interval with boundary gauge sectors. -/
def HeteroticStrongCouplingIntervalPackage
    (data : HeteroticStrongCouplingIntervalData) : Prop :=
  data.dualityChainHetEToMTheoryIntervalUsed = true /\
  data.mTheoryIntervalLengthScalesWithHetECoupling = true /\
  data.boundaryGaugeSymmetryEnhancedToE8TimesE8 = true /\
  data.heteroticStringRealizedAsStretchedM2 = true /\
  data.boundaryGaugeCouplingMatchesPlanckScaleDictionary = true

/-- Assumed strong-coupling hetE/M-theory-interval package. -/
theorem heterotic_strong_coupling_interval_package
    (data : HeteroticStrongCouplingIntervalData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityHeteroticStrongCouplingMTheoryInterval
      (HeteroticStrongCouplingIntervalPackage data)) :
    HeteroticStrongCouplingIntervalPackage data := by
  exact h_phys

/-- Horava-Witten bulk-boundary anomaly-inflow data. -/
structure HoravaWittenBoundaryData (BulkField BoundaryField : Type*) where
  effectiveActionFunctional : BulkField → BoundaryField → Complex
  boundaryConditionForG4IncludesGaugeAndCurvatureChernClasses : Bool
  c3GaugeShiftCompensatesBoundaryGaugeVariation : Bool
  bulkChernSimonsTermGeneratesBoundaryAnomalyInflow : Bool
  boundaryQuantumAnomalyPolynomialMatchedByInflow : Bool
  c3WedgeX8GreenSchwarzLikeBulkCountertermIncluded : Bool
  boundaryGaugeCouplingFixedByAnomalyCancellation : Bool
  actionTreatedAsFunctionalNotScalarObservable : Bool
  actionFunctionalAllowsComplexValues : Bool

/-- Section 18.8.3 package:
Horava-Witten bulk-boundary action and anomaly-inflow consistency. -/
def HoravaWittenBoundaryPackage
    {BulkField BoundaryField : Type*}
    (data : HoravaWittenBoundaryData BulkField BoundaryField) : Prop :=
  data.boundaryConditionForG4IncludesGaugeAndCurvatureChernClasses = true /\
  data.c3GaugeShiftCompensatesBoundaryGaugeVariation = true /\
  data.bulkChernSimonsTermGeneratesBoundaryAnomalyInflow = true /\
  data.boundaryQuantumAnomalyPolynomialMatchedByInflow = true /\
  data.c3WedgeX8GreenSchwarzLikeBulkCountertermIncluded = true /\
  data.boundaryGaugeCouplingFixedByAnomalyCancellation = true /\
  data.actionTreatedAsFunctionalNotScalarObservable = true /\
  data.actionFunctionalAllowsComplexValues = true

/-- Assumed Section 18.8.3 Horava-Witten boundary/anomaly package. -/
theorem horava_witten_boundary_package
    {BulkField BoundaryField : Type*}
    (data : HoravaWittenBoundaryData BulkField BoundaryField)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityHoravaWittenBoundaryAnomalyInflow
      (HoravaWittenBoundaryPackage data)) :
    HoravaWittenBoundaryPackage data := by
  exact h_phys

/-- Massive IIA / D8 / Romans-mass data. -/
structure MassiveIiaRomansD8Data where
  romansMassQuantizedInD8ChargeUnits : Bool
  tDualAxionMonodromyDerivationUsed : Bool
  massiveIiaFieldStrengthDeformationsIncluded : Bool
  dilatonPotentialFromRomansMassIncluded : Bool
  isolatedD8GloballyInconsistentWithoutAdditionalSources : Bool
  supersymmetricO8D8IntervalConfigurationsUsed : Bool

/-- Section 18.9 package:
massive IIA with Romans mass and D8/O8 system consistency. -/
def MassiveIiaRomansD8Package (data : MassiveIiaRomansD8Data) : Prop :=
  data.romansMassQuantizedInD8ChargeUnits = true /\
  data.tDualAxionMonodromyDerivationUsed = true /\
  data.massiveIiaFieldStrengthDeformationsIncluded = true /\
  data.dilatonPotentialFromRomansMassIncluded = true /\
  data.isolatedD8GloballyInconsistentWithoutAdditionalSources = true /\
  data.supersymmetricO8D8IntervalConfigurationsUsed = true

/-- Assumed Section 18.9 massive-IIA Romans/D8 package. -/
theorem massive_iia_romans_d8_package
    (data : MassiveIiaRomansD8Data)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDualityMassiveIIARomansD8System
      (MassiveIiaRomansD8Package data)) :
    MassiveIiaRomansD8Package data := by
  exact h_phys

end PhysicsLogic.StringTheory
