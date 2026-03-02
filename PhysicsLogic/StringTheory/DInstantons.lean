import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev DInstantonClaim := Prop

/-- Non-perturbative transseries data for closed-string amplitudes with D-instanton sectors. -/
structure DInstantonTransseriesData where
  stringCoupling : DimensionlessCoupling
  instantonSectorScale : ActionScale
  perturbativeAmplitudeSectorIncluded : DInstantonClaim
  dInstantonAmplitudeSectorIncluded : DInstantonClaim
  higherNonperturbativeSectorIncluded : DInstantonClaim
  moduliSpaceIntegralOverBoundaryConditionsIncluded : DInstantonClaim
  disconnectedWorldsheetExponentiationRuleUsed : DInstantonClaim
  openStringBoundaryDivergencesRequireNonperturbativePrescription : DInstantonClaim
  effectiveActionHandledAsFunctional : DInstantonClaim
  effectiveActionFunctionalAllowsComplexValues : DInstantonClaim

/-- Section 16.1 package:
non-perturbative D-instanton transseries, moduli-space integration, and
disconnected-worldsheet exponentiation structure. -/
def DInstantonTransseriesPackage (data : DInstantonTransseriesData) : Prop :=
  data.stringCoupling > 0 /\
  data.instantonSectorScale > 0 /\
  data.perturbativeAmplitudeSectorIncluded /\
  data.dInstantonAmplitudeSectorIncluded /\
  data.higherNonperturbativeSectorIncluded /\
  data.moduliSpaceIntegralOverBoundaryConditionsIncluded /\
  data.disconnectedWorldsheetExponentiationRuleUsed /\
  data.openStringBoundaryDivergencesRequireNonperturbativePrescription /\
  data.effectiveActionHandledAsFunctional /\
  data.effectiveActionFunctionalAllowsComplexValues

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
  InstantonConfiguration : Type
  selectedConfiguration : InstantonConfiguration
  stringCoupling : DimensionlessCoupling
  alphaPrime : StringSlope
  matrixModelMu : MassScale
  zzInstantonActionFunctional : InstantonConfiguration → ComplexActionValue
  zzActionFromBraneMassRelationUsed : DInstantonClaim
  matrixModelBounceDictionaryUsed : DInstantonClaim
  leadingOneToNAmplitudeFromDiscOnePointFunctions : DInstantonClaim
  normalizationMatchedToParticleHoleDualAmplitude : DInstantonClaim
  nonperturbativeUnitarityDeficitInterpretedAsClosedToNonclosedTransition : DInstantonClaim

/-- Section 16.2 package:
`c=1` ZZ-instanton action/normalization and dual matrix-model interpretation. -/
def COneZzInstantonPackage (data : COneZzInstantonData) : Prop :=
  data.stringCoupling > 0 /\
  data.alphaPrime > 0 /\
  data.matrixModelMu > 0 /\
  data.zzInstantonActionFunctional data.selectedConfiguration =
    ((1 / (2 * data.stringCoupling) : ℝ) : ℂ) /\
  data.zzActionFromBraneMassRelationUsed /\
  data.matrixModelBounceDictionaryUsed /\
  data.leadingOneToNAmplitudeFromDiscOnePointFunctions /\
  data.normalizationMatchedToParticleHoleDualAmplitude /\
  data.nonperturbativeUnitarityDeficitInterpretedAsClosedToNonclosedTransition

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
  InstantonConfiguration : Type
  selectedConfiguration : InstantonConfiguration
  tau1 : Real
  tau2 : Real
  axioDilatonField : InstantonConfiguration → ComplexDimensionless
  dMinusOneActionFunctional : InstantonConfiguration → ComplexActionValue
  antiDMinusOneActionFunctional : InstantonConfiguration → ComplexActionValue
  antiInstantonActionUsesConjugateAxioDilaton : DInstantonClaim
  nmInstantonActionUsed : DInstantonClaim
  axionShiftBrokenToIntegerSubgroup : DInstantonClaim
  leadingOneZeroSupermoduliIntegralUsed : DInstantonClaim
  fourGravitonR4CouplingGetsInstantonCorrections : DInstantonClaim

/-- Section 16.3 package:
type-IIB D(-1)-instanton/anti-instanton action dictionary and
axio-dilaton-dependent non-perturbative amplitude structure. -/
def TypeIIBDMinusOneInstantonPackage
    (data : TypeIIBDMinusOneInstantonData) : Prop :=
  data.tau2 > 0 /\
  data.axioDilatonField data.selectedConfiguration =
    data.tau1 + data.tau2 * Complex.I /\
  data.dMinusOneActionFunctional data.selectedConfiguration =
    -2 * Real.pi * Complex.I *
      data.axioDilatonField data.selectedConfiguration /\
  data.antiDMinusOneActionFunctional data.selectedConfiguration =
    -2 * Real.pi * Complex.I *
      star (data.axioDilatonField data.selectedConfiguration) /\
  data.antiInstantonActionUsesConjugateAxioDilaton /\
  data.nmInstantonActionUsed /\
  data.axionShiftBrokenToIntegerSubgroup /\
  data.leadingOneZeroSupermoduliIntegralUsed /\
  data.fourGravitonR4CouplingGetsInstantonCorrections

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
  coupledBvActionFunctional : ClosedField → OpenField → ComplexActionValue
  closedEffectiveActionFunctional : ClosedField → ComplexActionValue
  lagrangianSubmanifoldInOpenFieldSpaceChosen : DInstantonClaim
  openCollectiveModesReparametrizeInstantonModuli : DInstantonClaim
  openFieldSpaceBackgroundIndependenceMapUsed : DInstantonClaim
  relaxedSiegelGaugeForZeroWeightModesUsed : DInstantonClaim
  faddeevPopovGhostIntegralReplacedByGaugeOrbitVolumeFactor : DInstantonClaim
  wickRotationForWrongSignZeroModesIncluded : DInstantonClaim
  openTachyonContourChosenByLefschetzOrEquivalentPrescription : DInstantonClaim

/-- Section 16.4 package:
D-instanton open+closed SFT formulation with zero-mode gauge-fixing repair and
non-Gaussian collective-mode treatment. -/
def DInstantonOpenClosedSftZeroModePackage
    {ClosedField OpenField : Type*}
    (data : DInstantonOpenClosedSftZeroModeData ClosedField OpenField) : Prop :=
  data.lagrangianSubmanifoldInOpenFieldSpaceChosen /\
  data.openCollectiveModesReparametrizeInstantonModuli /\
  data.openFieldSpaceBackgroundIndependenceMapUsed /\
  data.relaxedSiegelGaugeForZeroWeightModesUsed /\
  data.faddeevPopovGhostIntegralReplacedByGaugeOrbitVolumeFactor /\
  data.wickRotationForWrongSignZeroModesIncluded /\
  data.openTachyonContourChosenByLefschetzOrEquivalentPrescription

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
  alphaPrime : StringSlope
  singleInstantonNormalizationScale : Dimless
  bosonicZzNormalizationMatchesDualMatrixModel : DInstantonClaim
  typeIibZeroModeMeasureFromOpenSftDetermined : DInstantonClaim
  uOneGaugeAngleNormalizationFixedFromSpectatorBraneCoupling : DInstantonClaim
  leadingRFourInstantonCoefficientRecovered : DInstantonClaim

/-- Section 16.5 package:
normalization of D-instanton amplitudes from open-string zero-mode measures and
gauge-volume factors. -/
def DInstantonNormalizationPackage (data : DInstantonNormalizationData) : Prop :=
  data.tau2 > 0 /\
  data.alphaPrime > 0 /\
  data.singleInstantonNormalizationScale > 0 /\
  data.bosonicZzNormalizationMatchesDualMatrixModel /\
  data.typeIibZeroModeMeasureFromOpenSftDetermined /\
  data.uOneGaugeAngleNormalizationFixedFromSpectatorBraneCoupling /\
  data.leadingRFourInstantonCoefficientRecovered

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
  multiInstantonNormalizationScale : Dimless
  chanPatonKToFourFactorIncluded : DInstantonClaim
  zeroModeMeasurePromotedToUKMatrices : DInstantonClaim
  matrixModelActionFromTenDimensionalSymReductionUsed : DInstantonClaim
  ikktLocalizationDivisorSumFormulaUsed : DInstantonClaim
  leadingRFourCoefficientScalesWithSqrtKTimesZk : DInstantonClaim

/-- Section 16.6 package:
multiple D-instantons with `U(k)` zero modes and IKKT matrix-integral
normalization of the leading four-supergraviton correction. -/
def MultipleDInstantonIkktPackage (data : MultipleDInstantonIkktData) : Prop :=
  data.instantonNumber > 0 /\
  data.tau2 > 0 /\
  data.ikktMatrixIntegralValue > 0 /\
  data.multiInstantonNormalizationScale > 0 /\
  data.chanPatonKToFourFactorIncluded /\
  data.zeroModeMeasurePromotedToUKMatrices /\
  data.matrixModelActionFromTenDimensionalSymReductionUsed /\
  data.ikktLocalizationDivisorSumFormulaUsed /\
  data.leadingRFourCoefficientScalesWithSqrtKTimesZk

/-- Assumed Section 16.6 multiple D-instanton IKKT package. -/
theorem multiple_d_instanton_ikkt_package
    (data : MultipleDInstantonIkktData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDinstantonMultipleIkktIntegralScaling
      (MultipleDInstantonIkktPackage data)) :
    MultipleDInstantonIkktPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
