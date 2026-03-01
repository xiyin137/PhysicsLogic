import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Non-perturbative transseries data for closed-string amplitudes with D-instanton sectors. -/
structure DInstantonTransseriesData where
  stringCoupling : Real
  instantonActionScale : Real
  perturbativeAmplitudeSectorIncluded : Bool
  dInstantonAmplitudeSectorIncluded : Bool
  higherNonperturbativeSectorIncluded : Bool
  moduliSpaceIntegralOverBoundaryConditionsIncluded : Bool
  disconnectedWorldsheetExponentiationRuleUsed : Bool
  openStringBoundaryDivergencesRequireNonperturbativePrescription : Bool
  effectiveActionHandledAsFunctional : Bool
  effectiveActionFunctionalAllowsComplexValues : Bool

/-- Section 16.1 package:
non-perturbative D-instanton transseries, moduli-space integration, and
disconnected-worldsheet exponentiation structure. -/
def DInstantonTransseriesPackage (data : DInstantonTransseriesData) : Prop :=
  data.stringCoupling > 0 /\
  data.instantonActionScale > 0 /\
  data.perturbativeAmplitudeSectorIncluded = true /\
  data.dInstantonAmplitudeSectorIncluded = true /\
  data.higherNonperturbativeSectorIncluded = true /\
  data.moduliSpaceIntegralOverBoundaryConditionsIncluded = true /\
  data.disconnectedWorldsheetExponentiationRuleUsed = true /\
  data.openStringBoundaryDivergencesRequireNonperturbativePrescription = true /\
  data.effectiveActionHandledAsFunctional = true /\
  data.effectiveActionFunctionalAllowsComplexValues = true

/-- Assumed Section 16.1 D-instanton transseries/moduli package. -/
theorem d_instanton_transseries_package
    (data : DInstantonTransseriesData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonTransseriesAndModuliIntegral
      (DInstantonTransseriesPackage data)) :
    DInstantonTransseriesPackage data := by
  exact h_phys

/-- Data for the ZZ-instanton sector in `c=1` string theory and its MQM dual match. -/
structure COneZzInstantonData where
  stringCoupling : Real
  alphaPrime : Real
  matrixModelMu : Real
  zzInstantonAction : Real
  zzActionFromBraneMassRelationUsed : Bool
  matrixModelBounceDictionaryUsed : Bool
  leadingOneToNAmplitudeFromDiscOnePointFunctions : Bool
  normalizationMatchedToParticleHoleDualAmplitude : Bool
  nonperturbativeUnitarityDeficitInterpretedAsClosedToNonclosedTransition : Bool

/-- Section 16.2 package:
`c=1` ZZ-instanton action/normalization and dual matrix-model interpretation. -/
def COneZzInstantonPackage (data : COneZzInstantonData) : Prop :=
  data.stringCoupling > 0 /\
  data.alphaPrime > 0 /\
  data.matrixModelMu > 0 /\
  data.zzInstantonAction = 1 / (2 * data.stringCoupling) /\
  data.zzActionFromBraneMassRelationUsed = true /\
  data.matrixModelBounceDictionaryUsed = true /\
  data.leadingOneToNAmplitudeFromDiscOnePointFunctions = true /\
  data.normalizationMatchedToParticleHoleDualAmplitude = true /\
  data.nonperturbativeUnitarityDeficitInterpretedAsClosedToNonclosedTransition = true

/-- Assumed Section 16.2 `c=1` ZZ-instanton package. -/
theorem c_one_zz_instanton_package
    (data : COneZzInstantonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonCOneZzContributionAndNormalization
      (COneZzInstantonPackage data)) :
    COneZzInstantonPackage data := by
  exact h_phys

/-- Type-IIB D(-1)-instanton data in axio-dilaton variables. -/
structure TypeIIBDMinusOneInstantonData where
  tau1 : Real
  tau2 : Real
  axioDilaton : Complex
  dMinusOneAction : Complex
  antiDMinusOneAction : Complex
  antiInstantonActionUsesConjugateAxioDilaton : Bool
  nmInstantonActionUsed : Bool
  axionShiftBrokenToIntegerSubgroup : Bool
  leadingOneZeroSupermoduliIntegralUsed : Bool
  fourGravitonR4CouplingGetsInstantonCorrections : Bool

/-- Section 16.3 package:
type-IIB D(-1)-instanton/anti-instanton action dictionary and
axio-dilaton-dependent non-perturbative amplitude structure. -/
def TypeIIBDMinusOneInstantonPackage
    (data : TypeIIBDMinusOneInstantonData) : Prop :=
  data.tau2 > 0 /\
  data.axioDilaton = data.tau1 + data.tau2 * Complex.I /\
  data.dMinusOneAction = -2 * Real.pi * Complex.I * data.axioDilaton /\
  data.antiInstantonActionUsesConjugateAxioDilaton = true /\
  data.nmInstantonActionUsed = true /\
  data.axionShiftBrokenToIntegerSubgroup = true /\
  data.leadingOneZeroSupermoduliIntegralUsed = true /\
  data.fourGravitonR4CouplingGetsInstantonCorrections = true

/-- Assumed Section 16.3 type-IIB D(-1)-instanton package. -/
theorem type_iib_d_minus_one_instanton_package
    (data : TypeIIBDMinusOneInstantonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonTypeIIBAxioDilatonExpansion
      (TypeIIBDMinusOneInstantonPackage data)) :
    TypeIIBDMinusOneInstantonPackage data := by
  exact h_phys

/-- Open+closed SFT data for D-instanton zero-mode and gauge-volume treatment. -/
structure DInstantonOpenClosedSftZeroModeData (ClosedField OpenField : Type*) where
  coupledBvActionFunctional : ClosedField → OpenField → Complex
  closedEffectiveActionFunctional : ClosedField → Complex
  lagrangianSubmanifoldInOpenFieldSpaceChosen : Bool
  openCollectiveModesReparametrizeInstantonModuli : Bool
  openFieldSpaceBackgroundIndependenceMapUsed : Bool
  relaxedSiegelGaugeForZeroWeightModesUsed : Bool
  faddeevPopovGhostIntegralReplacedByGaugeOrbitVolumeFactor : Bool
  wickRotationForWrongSignZeroModesIncluded : Bool
  openTachyonContourChosenByLefschetzOrEquivalentPrescription : Bool

/-- Section 16.4 package:
D-instanton open+closed SFT formulation with zero-mode gauge-fixing repair and
non-Gaussian collective-mode treatment. -/
def DInstantonOpenClosedSftZeroModePackage
    {ClosedField OpenField : Type*}
    (data : DInstantonOpenClosedSftZeroModeData ClosedField OpenField) : Prop :=
  data.lagrangianSubmanifoldInOpenFieldSpaceChosen = true /\
  data.openCollectiveModesReparametrizeInstantonModuli = true /\
  data.openFieldSpaceBackgroundIndependenceMapUsed = true /\
  data.relaxedSiegelGaugeForZeroWeightModesUsed = true /\
  data.faddeevPopovGhostIntegralReplacedByGaugeOrbitVolumeFactor = true /\
  data.wickRotationForWrongSignZeroModesIncluded = true /\
  data.openTachyonContourChosenByLefschetzOrEquivalentPrescription = true

/-- Assumed Section 16.4 open+closed SFT zero-mode package for D-instantons. -/
theorem d_instanton_open_closed_sft_zero_mode_package
    {ClosedField OpenField : Type*}
    (data : DInstantonOpenClosedSftZeroModeData ClosedField OpenField)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonOpenClosedSftZeroModeGaugeFixing
      (DInstantonOpenClosedSftZeroModePackage data)) :
    DInstantonOpenClosedSftZeroModePackage data := by
  exact h_phys

/-- Normalization-extraction data for single D-instanton amplitudes in bosonic and type-IIB settings. -/
structure DInstantonNormalizationData where
  tau2 : Real
  alphaPrime : Real
  singleInstantonNormalizationScale : Real
  bosonicZzNormalizationMatchesDualMatrixModel : Bool
  typeIibZeroModeMeasureFromOpenSftDetermined : Bool
  uOneGaugeAngleNormalizationFixedFromSpectatorBraneCoupling : Bool
  leadingRFourInstantonCoefficientRecovered : Bool

/-- Section 16.5 package:
normalization of D-instanton amplitudes from open-string zero-mode measures and
gauge-volume factors. -/
def DInstantonNormalizationPackage (data : DInstantonNormalizationData) : Prop :=
  data.tau2 > 0 /\
  data.alphaPrime > 0 /\
  data.singleInstantonNormalizationScale > 0 /\
  data.bosonicZzNormalizationMatchesDualMatrixModel = true /\
  data.typeIibZeroModeMeasureFromOpenSftDetermined = true /\
  data.uOneGaugeAngleNormalizationFixedFromSpectatorBraneCoupling = true /\
  data.leadingRFourInstantonCoefficientRecovered = true

/-- Assumed Section 16.5 D-instanton normalization package. -/
theorem d_instanton_normalization_package
    (data : DInstantonNormalizationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonNormalizationFromZeroModeMeasure
      (DInstantonNormalizationPackage data)) :
    DInstantonNormalizationPackage data := by
  exact h_phys

/-- Data for `(k,0)` multi-D-instanton sectors and IKKT matrix-integral reduction. -/
structure MultipleDInstantonIkktData where
  instantonNumber : Nat
  tau2 : Real
  ikktMatrixIntegralValue : Real
  multiInstantonNormalizationScale : Real
  chanPatonKToFourFactorIncluded : Bool
  zeroModeMeasurePromotedToUKMatrices : Bool
  matrixModelActionFromTenDimensionalSymReductionUsed : Bool
  ikktLocalizationDivisorSumFormulaUsed : Bool
  leadingRFourCoefficientScalesWithSqrtKTimesZk : Bool

/-- Section 16.6 package:
multiple D-instantons with `U(k)` zero modes and IKKT matrix-integral
normalization of the leading four-supergraviton correction. -/
def MultipleDInstantonIkktPackage (data : MultipleDInstantonIkktData) : Prop :=
  data.instantonNumber > 0 /\
  data.tau2 > 0 /\
  data.ikktMatrixIntegralValue > 0 /\
  data.multiInstantonNormalizationScale > 0 /\
  data.chanPatonKToFourFactorIncluded = true /\
  data.zeroModeMeasurePromotedToUKMatrices = true /\
  data.matrixModelActionFromTenDimensionalSymReductionUsed = true /\
  data.ikktLocalizationDivisorSumFormulaUsed = true /\
  data.leadingRFourCoefficientScalesWithSqrtKTimesZk = true

/-- Assumed Section 16.6 multiple D-instanton IKKT package. -/
theorem multiple_d_instanton_ikkt_package
    (data : MultipleDInstantonIkktData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonMultipleIkktIntegralScaling
      (MultipleDInstantonIkktPackage data)) :
    MultipleDInstantonIkktPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
