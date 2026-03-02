import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev HeteroticClaim := Prop

/-- Worldsheet field-content and gauge-fixing data for heterotic strings. -/
structure HeteroticWorldsheetData where
  spacetimeDimension : ℕ
  leftMovingFermionCount : ℕ
  rightMovingTargetFermionCount : ℕ
  rightTargetFermionCount_matches_dimension :
    rightMovingTargetFermionCount = spacetimeDimension
  leftMatterCentralCharge : ℝ
  rightMatterCentralCharge : ℝ
  leftGhostCentralCharge : ℝ
  rightGhostCentralCharge : ℝ
  left_matter_formula :
    leftMatterCentralCharge =
      (spacetimeDimension : ℝ) + (leftMovingFermionCount : ℝ) / 2
  right_matter_formula :
    rightMatterCentralCharge =
      (spacetimeDimension : ℝ) + (rightMovingTargetFermionCount : ℝ) / 2
  left_ghost_formula : leftGhostCentralCharge = -26
  right_ghost_formula : rightGhostCentralCharge = -15
  left_central_charge_cancels : leftMatterCentralCharge + leftGhostCentralCharge = 0
  right_central_charge_cancels : rightMatterCentralCharge + rightGhostCentralCharge = 0
  localChiralSupersymmetry : HeteroticClaim
  superconformalGaugeFixing01 : HeteroticClaim
  totalCentralChargeCancels : HeteroticClaim
  gravitationalAndWeylAnomalyCanceled : HeteroticClaim

/-- Heterotic worldsheet package:
chiral local supersymmetry with explicit left/right central-charge cancellation
data for a critical `(0,1)` gauge-fixed SCFT. -/
def HeteroticWorldsheetPackage (data : HeteroticWorldsheetData) : Prop :=
  data.localChiralSupersymmetry ∧
  data.superconformalGaugeFixing01 ∧
  data.totalCentralChargeCancels ∧
  data.gravitationalAndWeylAnomalyCanceled

/-- Right-moving central-charge cancellation implies critical target dimension `D=10`. -/
theorem HeteroticWorldsheetData.spacetime_dimension_eq_ten
    (data : HeteroticWorldsheetData) : (data.spacetimeDimension : ℝ) = 10 := by
  have h_right_cancel :
      (data.spacetimeDimension : ℝ) + (data.rightMovingTargetFermionCount : ℝ) / 2 - 15 = 0 := by
    calc
      (data.spacetimeDimension : ℝ) + (data.rightMovingTargetFermionCount : ℝ) / 2 - 15
          = data.rightMatterCentralCharge + data.rightGhostCentralCharge := by
            rw [data.right_matter_formula, data.right_ghost_formula]
            ring
      _ = 0 := data.right_central_charge_cancels
  have h_right_count :
      (data.rightMovingTargetFermionCount : ℝ) = (data.spacetimeDimension : ℝ) := by
    norm_num [data.rightTargetFermionCount_matches_dimension]
  nlinarith [h_right_cancel, h_right_count]

/-- Left-moving central-charge cancellation then fixes the gauge-fermion count to `32`. -/
theorem HeteroticWorldsheetData.left_moving_fermion_count_eq_thirty_two
    (data : HeteroticWorldsheetData) : (data.leftMovingFermionCount : ℝ) = 32 := by
  have h_left_cancel :
      (data.spacetimeDimension : ℝ) + (data.leftMovingFermionCount : ℝ) / 2 - 26 = 0 := by
    calc
      (data.spacetimeDimension : ℝ) + (data.leftMovingFermionCount : ℝ) / 2 - 26
          = data.leftMatterCentralCharge + data.leftGhostCentralCharge := by
            rw [data.left_matter_formula, data.left_ghost_formula]
            ring
      _ = 0 := data.left_central_charge_cancels
  have h_dim : (data.spacetimeDimension : ℝ) = 10 := data.spacetime_dimension_eq_ten
  nlinarith [h_left_cancel, h_dim]

/-- Nat-valued critical target-dimension consequence. -/
theorem HeteroticWorldsheetData.spacetime_dimension_nat_eq_ten
    (data : HeteroticWorldsheetData) : data.spacetimeDimension = 10 := by
  exact Nat.cast_injective (by simpa using data.spacetime_dimension_eq_ten)

/-- Nat-valued left-moving gauge-fermion count consequence. -/
theorem HeteroticWorldsheetData.left_moving_fermion_count_nat_eq_thirty_two
    (data : HeteroticWorldsheetData) : data.leftMovingFermionCount = 32 := by
  exact Nat.cast_injective (by simpa using data.left_moving_fermion_count_eq_thirty_two)

/-- Assumed heterotic worldsheet/chiral-supersymmetry package from Section 11.1. -/
theorem heterotic_worldsheet_package
    (data : HeteroticWorldsheetData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticWorldsheetChiralSupersymmetry
      (HeteroticWorldsheetPackage data)) :
    HeteroticWorldsheetPackage data := by
  exact h_phys

/-- GSO/chiral-CFT data for the left-moving fermion system in heterotic strings. -/
structure HeteroticLambdaGsoData where
  rightMovingChiralGsoApplied : HeteroticClaim
  leftMovingChiralGsoApplied : HeteroticClaim
  so32CurrentAlgebraRealized : HeteroticClaim
  e8TimesE8CurrentAlgebraRealized : HeteroticClaim
  narainGamma16Realization : HeteroticClaim
  narainGamma8PlusGamma8Realization : HeteroticClaim
  modularInvariantProjection : HeteroticClaim

/-- Heterotic `λ`-sector package:
chiral GSO projections produce either `Spin(32)/Z_2` or `E_8×E_8`
current algebra sectors with Narain-lattice realizations. -/
def HeteroticLambdaGsoPackage (data : HeteroticLambdaGsoData) : Prop :=
  data.rightMovingChiralGsoApplied ∧
  data.leftMovingChiralGsoApplied ∧
  data.so32CurrentAlgebraRealized ∧
  data.e8TimesE8CurrentAlgebraRealized ∧
  data.narainGamma16Realization ∧
  data.narainGamma8PlusGamma8Realization ∧
  data.modularInvariantProjection

/-- Assumed heterotic `λ`-sector GSO/current-algebra package from Section 11.1. -/
theorem heterotic_lambda_gso_package
    (data : HeteroticLambdaGsoData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticLambdaGsoCurrentAlgebras
      (HeteroticLambdaGsoPackage data)) :
    HeteroticLambdaGsoPackage data := by
  exact h_phys

/-- Physical-state and spectrum data for the heterotic BRST construction. -/
structure HeteroticSpectrumData where
  alphaPrime : StringSlope
  momentumSq : MomentumSquaredScale
  leftOscillatorLevel : ℤ
  rightOscillatorLevel : ℤ
  brstCohomologyWithSiegelConstraint : HeteroticClaim
  rightChiralGsoProjection : HeteroticClaim
  tachyonFreeSpectrum : HeteroticClaim
  masslessNOneSupergravityMultipletPresent : HeteroticClaim
  masslessGaugeMultipletPresent : HeteroticClaim

/-- Heterotic physical-spectrum package:
BRST/Siegel cohomology with level matching and right-moving GSO, yielding
tachyon-free spectrum with 10D `N=1` supergravity plus gauge multiplets. -/
def HeteroticSpectrumPackage (data : HeteroticSpectrumData) : Prop :=
  data.alphaPrime > 0 ∧
  ((-data.alphaPrime / 4) * data.momentumSq).value = (data.leftOscillatorLevel : ℝ) ∧
  ((-data.alphaPrime / 4) * data.momentumSq).value = (data.rightOscillatorLevel : ℝ) ∧
  data.leftOscillatorLevel ≥ -1 ∧
  data.rightOscillatorLevel ≥ 0 ∧
  data.brstCohomologyWithSiegelConstraint ∧
  data.rightChiralGsoProjection ∧
  data.tachyonFreeSpectrum ∧
  data.masslessNOneSupergravityMultipletPresent ∧
  data.masslessGaugeMultipletPresent

/-- Assumed heterotic physical-spectrum package from Section 11.1. -/
theorem heterotic_spectrum_package
    (data : HeteroticSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticPhysicalSpectrumCohomology
      (HeteroticSpectrumPackage data)) :
    HeteroticSpectrumPackage data := by
  exact h_phys

/-- Perturbative heterotic amplitude prescription data. -/
structure HeteroticAmplitudePrescriptionData where
  genus : ℕ
  punctures : ℕ
  oddSupermoduliComplexDimension : ℤ
  phasePower : ℤ
  normalizationPrefactor : ComplexAmplitude
  contourIntegral : ComplexAmplitude
  amplitude : ComplexAmplitude
  antiholomorphicSupermoduliOnly : HeteroticClaim
  pcoReplacementEquivalent : HeteroticClaim
  spuriousSingularitiesControlled : HeteroticClaim

/-- Heterotic perturbative-amplitude package:
only anti-holomorphic supermoduli are integrated, with PCO-equivalent
prescription and controlled spurious singularities. -/
def HeteroticAmplitudePrescriptionPackage
    (data : HeteroticAmplitudePrescriptionData) : Prop :=
  data.oddSupermoduliComplexDimension =
    2 * (data.genus : ℤ) - 2 + (data.punctures : ℤ) ∧
  data.phasePower = 3 * (data.genus : ℤ) - 3 + (data.punctures : ℤ) ∧
  data.antiholomorphicSupermoduliOnly ∧
  data.pcoReplacementEquivalent ∧
  data.spuriousSingularitiesControlled ∧
  data.amplitude = data.normalizationPrefactor * data.contourIntegral

/-- Assumed perturbative heterotic amplitude prescription from Section 11.2. -/
theorem heterotic_amplitude_prescription_package
    (data : HeteroticAmplitudePrescriptionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticPerturbativeAmplitudePrescription
      (HeteroticAmplitudePrescriptionPackage data)) :
    HeteroticAmplitudePrescriptionPackage data := by
  exact h_phys

/-- Tree-level coupling data in the 10D heterotic effective description. -/
structure HeteroticTreeEffectiveCouplingData where
  stringCoupling : DimensionlessCoupling
  alphaPrime : StringSlope
  gravitationalCoupling : CouplingScale
  yangMillsCoupling : CouplingScale
  gravitonThreePointContainsRiemannSqCorrection : HeteroticClaim
  gravitonThreePointHasNoRiemannCubeCorrection : HeteroticClaim
  gaugeThreePointMatchesYangMillsWithoutFcube : HeteroticClaim
  lowEnergyCompletionIsTenDimensionalNOneSupergravity : HeteroticClaim

/-- Heterotic tree-level effective-coupling package:
`κ = π g_s`, `g_YM = 2π g_s / sqrt(α') = 2κ / sqrt(α')`,
with tree-level `R^2`-type correction but no independent `R^3` term. -/
def HeteroticTreeEffectiveCouplingPackage
    (data : HeteroticTreeEffectiveCouplingData) : Prop :=
  data.stringCoupling > 0 ∧
  data.alphaPrime > 0 ∧
  data.gravitationalCoupling = Real.pi * data.stringCoupling ∧
  data.yangMillsCoupling =
    2 * Real.pi * data.stringCoupling / Real.sqrt data.alphaPrime ∧
  data.yangMillsCoupling =
    2 * data.gravitationalCoupling / Real.sqrt data.alphaPrime ∧
  data.gravitonThreePointContainsRiemannSqCorrection ∧
  data.gravitonThreePointHasNoRiemannCubeCorrection ∧
  data.gaugeThreePointMatchesYangMillsWithoutFcube ∧
  data.lowEnergyCompletionIsTenDimensionalNOneSupergravity

/-- Assumed heterotic tree-level effective-coupling package from Section 11.2. -/
theorem heterotic_tree_effective_coupling_package
    (data : HeteroticTreeEffectiveCouplingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticTreeLevelEffectiveCouplings
      (HeteroticTreeEffectiveCouplingPackage data)) :
    HeteroticTreeEffectiveCouplingPackage data := by
  exact h_phys

/-- Green-Schwarz anomaly-cancellation data in heterotic perturbation theory. -/
structure HeteroticGreenSchwarzData where
  parityOddBTwoWedgeX8CouplingPresent : HeteroticClaim
  x8PolynomialMatchesGaugeGravitationalAnomaly : HeteroticClaim
  oddSpinStructureOneLoopFivePointContributionPresent : HeteroticClaim
  oneLoopBfFourExtractionConsistent : HeteroticClaim
  anomalyCancellationByBFieldVariation : HeteroticClaim

/-- Heterotic Green-Schwarz package:
`B_2 ∧ X_8` is generated with odd-spin-structure contribution and cancels
the 10D gauge/gravitational anomaly. -/
def HeteroticGreenSchwarzPackage (data : HeteroticGreenSchwarzData) : Prop :=
  data.parityOddBTwoWedgeX8CouplingPresent ∧
  data.x8PolynomialMatchesGaugeGravitationalAnomaly ∧
  data.oddSpinStructureOneLoopFivePointContributionPresent ∧
  data.oneLoopBfFourExtractionConsistent ∧
  data.anomalyCancellationByBFieldVariation

/-- Assumed heterotic Green-Schwarz anomaly-coupling package from Section 11.2. -/
theorem heterotic_green_schwarz_package
    (data : HeteroticGreenSchwarzData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticGreenSchwarzAnomalyCoupling
      (HeteroticGreenSchwarzPackage data)) :
    HeteroticGreenSchwarzPackage data := by
  exact h_phys

/-- Data for non-BPS `SO(32)` spinor-state mass renormalization. -/
structure HeteroticNonBpsSpinorMassRenormalizationData where
  alphaPrime : StringSlope
  stringCoupling : DimensionlessCoupling
  classicalMassSq : MassSquaredScale
  oneLoopMassShiftSq : MassSquaredScale
  correctedMassSq : MassSquaredScale
  has128BosonsAnd128Fermions : HeteroticClaim
  stableAgainstDecayToMasslessStates : HeteroticClaim
  offShellOnePiFrameworkRequired : HeteroticClaim
  torusTwoPointAmplitudeControlsShift : HeteroticClaim

/-- Non-BPS spinor mass-renormalization package:
classical `m^2 = 4/α'`, positive one-loop shift from the torus 2-point function,
and off-shell 1PI control of the physical pole. -/
def HeteroticNonBpsSpinorMassRenormalizationPackage
    (data : HeteroticNonBpsSpinorMassRenormalizationData) : Prop :=
  data.alphaPrime > 0 ∧
  data.stringCoupling > 0 ∧
  data.classicalMassSq = 4 / data.alphaPrime ∧
  data.correctedMassSq = data.classicalMassSq + data.oneLoopMassShiftSq ∧
  data.oneLoopMassShiftSq > 0 ∧
  data.has128BosonsAnd128Fermions ∧
  data.stableAgainstDecayToMasslessStates ∧
  data.offShellOnePiFrameworkRequired ∧
  data.torusTwoPointAmplitudeControlsShift

/-- Assumed heterotic non-BPS spinor mass-renormalization package from Section 11.3. -/
theorem heterotic_non_bps_spinor_mass_renormalization_package
    (data : HeteroticNonBpsSpinorMassRenormalizationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticNonBpsSpinorMassRenormalization
      (HeteroticNonBpsSpinorMassRenormalizationPackage data)) :
    HeteroticNonBpsSpinorMassRenormalizationPackage data := by
  exact h_phys

/-- Background-field `(0,1)` sigma-model data for heterotic strings. -/
structure HeteroticBackgroundNlsmData where
  Configuration : Type
  actionFunctional : Configuration → ComplexActionValue
  alphaPrime : StringSlope
  hasMetricBackground : HeteroticClaim
  hasBFieldBackground : HeteroticClaim
  hasGaugeBundleBackground : HeteroticClaim
  worldsheet01Supersymmetry : HeteroticClaim
  gaugeTransformationActsOnLambdaFermions : HeteroticClaim
  bFieldTransformsUnderGaugeAndLorentzAnomalies : HeteroticClaim
  modifiedHThreeGaugeInvariant : HeteroticClaim
  modifiedBianchiIdentityIncludesF2AndR2 : HeteroticClaim
  oneLoopGaugeBetaIsCovariantDivergence : HeteroticClaim
  twoLoopMetricBetaIncludesRiemannSqAndFSq : HeteroticClaim

/-- Heterotic background sigma-model package:
`(0,1)` NLSM with gauge bundle, anomalous `B` transformation, gauge-invariant
`H-hat`, modified Bianchi identity, and beta-function/EOM matching. -/
def HeteroticBackgroundNlsmPackage (data : HeteroticBackgroundNlsmData) : Prop :=
  data.alphaPrime > 0 ∧
  data.hasMetricBackground ∧
  data.hasBFieldBackground ∧
  data.hasGaugeBundleBackground ∧
  data.worldsheet01Supersymmetry ∧
  data.gaugeTransformationActsOnLambdaFermions ∧
  data.bFieldTransformsUnderGaugeAndLorentzAnomalies ∧
  data.modifiedHThreeGaugeInvariant ∧
  data.modifiedBianchiIdentityIncludesF2AndR2 ∧
  data.oneLoopGaugeBetaIsCovariantDivergence ∧
  data.twoLoopMetricBetaIncludesRiemannSqAndFSq

/-- Assumed heterotic background `(0,1)` sigma-model package from Section 11.4. -/
theorem heterotic_background_nlsm_package
    (data : HeteroticBackgroundNlsmData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticBackgroundNlsmGaugeLorentzAnomaly
      (HeteroticBackgroundNlsmPackage data)) :
    HeteroticBackgroundNlsmPackage data := by
  exact h_phys

/-- Calabi-Yau compactification with gauge-bundle data in heterotic strings. -/
structure HeteroticCalabiYauGaugeBundleData where
  complexDimension : ℕ
  targetKahler : HeteroticClaim
  gaugeFieldStrengthHermitian : HeteroticClaim
  worldsheetU1RSymmetryEnhancedTo02 : HeteroticClaim
  standardEmbeddingApplied : HeteroticClaim
  hHatThreeVanishesForFlatBInStandardEmbedding : HeteroticClaim
  preservesFourDimensionalNOneSupersymmetry : HeteroticClaim
  unbrokenGaugeGroupSO26TimesU1OrE6TimesE8 : HeteroticClaim

/-- Heterotic Calabi-Yau/gauge-bundle package:
Hermitian gauge bundle and standard embedding reduce to `(2,2)` structure with
4D `N=1` vacua and expected unbroken gauge algebra. -/
def HeteroticCalabiYauGaugeBundlePackage
    (data : HeteroticCalabiYauGaugeBundleData) : Prop :=
  data.complexDimension > 0 ∧
  data.targetKahler ∧
  data.gaugeFieldStrengthHermitian ∧
  data.worldsheetU1RSymmetryEnhancedTo02 ∧
  data.standardEmbeddingApplied ∧
  data.hHatThreeVanishesForFlatBInStandardEmbedding ∧
  data.preservesFourDimensionalNOneSupersymmetry ∧
  data.unbrokenGaugeGroupSO26TimesU1OrE6TimesE8

/-- Assumed heterotic Calabi-Yau standard-embedding package from Section 11.5. -/
theorem heterotic_calabi_yau_gauge_bundle_package
    (data : HeteroticCalabiYauGaugeBundleData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticCalabiYauStandardEmbedding
      (HeteroticCalabiYauGaugeBundlePackage data)) :
    HeteroticCalabiYauGaugeBundlePackage data := by
  exact h_phys

/-- Strominger-system data for heterotic supersymmetric backgrounds. -/
structure HeteroticStromingerSystemData where
  complexStructureIntegrable : HeteroticClaim
  metricHermitianWithRespectToComplexStructure : HeteroticClaim
  gaugeBundleHolomorphic : HeteroticClaim
  hThreeEqualsIPartialMinusBarPartialOmega : HeteroticClaim
  hHatThreeReceivesAlphaPrimeChernSimonsCorrection : HeteroticClaim
  hermitianYangMillsCondition : HeteroticClaim
  secondChernCharacterConstraintSatisfied : HeteroticClaim
  torsionalConnectionHasSU3Holonomy : HeteroticClaim
  expMinusTwoPhiOmegaClosedAndHolomorphic : HeteroticClaim

/-- Heterotic Strominger-system package:
integrable complex/Hermitian geometry with torsion, corrected `H-hat`
constraint, Hermitian Yang-Mills bundle, and supersymmetry conditions. -/
def HeteroticStromingerSystemPackage
    (data : HeteroticStromingerSystemData) : Prop :=
  data.complexStructureIntegrable ∧
  data.metricHermitianWithRespectToComplexStructure ∧
  data.gaugeBundleHolomorphic ∧
  data.hThreeEqualsIPartialMinusBarPartialOmega ∧
  data.hHatThreeReceivesAlphaPrimeChernSimonsCorrection ∧
  data.hermitianYangMillsCondition ∧
  data.secondChernCharacterConstraintSatisfied ∧
  data.torsionalConnectionHasSU3Holonomy ∧
  data.expMinusTwoPhiOmegaClosedAndHolomorphic

/-- Assumed heterotic Strominger-system package from Section 11.5. -/
theorem heterotic_strominger_system_package
    (data : HeteroticStromingerSystemData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticStromingerSystem
      (HeteroticStromingerSystemPackage data)) :
    HeteroticStromingerSystemPackage data := by
  exact h_phys

/-- 4D effective-theory/FI-potential data in quantum-corrected heterotic vacua. -/
structure HeteroticFourDEffectiveTheoryData where
  kappa4 : CouplingScale
  alphaPrime : StringSlope
  anomalyCoefficient : ℤ
  inverseDilatonRealPart : DimensionlessCoupling
  chargedScalarQuadraticContribution : MassSquaredScale
  uOneMomentMap : MassSquaredScale
  dTermPotentialContribution : PotentialScale
  axionShiftCancelsUOneAnomaly : HeteroticClaim
  dilatonInChiralMultiplet : HeteroticClaim

/-- Heterotic 4D effective/FI package:
anomalous `U(1)` axion shift, moment-map FI piece from the dilaton multiplet,
and the induced `D`-term scalar-potential contribution. -/
def HeteroticFourDEffectiveTheoryPackage
    (data : HeteroticFourDEffectiveTheoryData) : Prop :=
  data.kappa4 > 0 ∧
  data.alphaPrime > 0 ∧
  data.inverseDilatonRealPart > 0 ∧
  data.uOneMomentMap =
    data.chargedScalarQuadraticContribution +
      ((data.anomalyCoefficient : ℝ) /
        (Real.pi ^ (2 : ℕ) * data.alphaPrime) * data.inverseDilatonRealPart) ∧
  data.dTermPotentialContribution =
    (data.kappa4 ^ (2 : ℕ) / (3 * data.alphaPrime)) * data.uOneMomentMap ^ (2 : ℕ) ∧
  data.axionShiftCancelsUOneAnomaly ∧
  data.dilatonInChiralMultiplet

/-- Assumed heterotic 4D effective/FI package from Section 11.6.1. -/
theorem heterotic_four_d_effective_theory_package
    (data : HeteroticFourDEffectiveTheoryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticFourDEffectiveFiPotential
      (HeteroticFourDEffectiveTheoryPackage data)) :
    HeteroticFourDEffectiveTheoryPackage data := by
  exact h_phys

/-- One-loop Fayet-Iliopoulos mass-term data for charged heterotic scalars. -/
structure HeteroticOneLoopFiMassTermData where
  charge : ℤ
  kappa4 : CouplingScale
  alphaPrime : StringSlope
  h21 : ℕ
  h11 : ℕ
  deltaMassSq : MassSquaredScale
  offShellRegularizationUsed : HeteroticClaim
  oddSpinStructureContributionVanishes : HeteroticClaim
  ramondIndexTraceDeterminesIntegral : HeteroticClaim

/-- One-loop FI mass package:
`δm^2 = q κ^2 (h^{2,1}-h^{1,1}) /(3 π^2 α'^2)` from the regulated torus 2-point
analysis and Ramond-index reduction. -/
def HeteroticOneLoopFiMassTermPackage
    (data : HeteroticOneLoopFiMassTermData) : Prop :=
  data.kappa4 > 0 ∧
  data.alphaPrime > 0 ∧
  data.deltaMassSq =
    ((data.charge : ℝ) * data.kappa4 ^ (2 : ℕ) /
      (3 * Real.pi ^ (2 : ℕ) * data.alphaPrime ^ (2 : ℕ)) *
      ((data.h21 : ℝ) - (data.h11 : ℝ))) ∧
  data.offShellRegularizationUsed ∧
  data.oddSpinStructureContributionVanishes ∧
  data.ramondIndexTraceDeterminesIntegral

/-- Assumed heterotic one-loop FI mass package from Section 11.6.2. -/
theorem heterotic_one_loop_fi_mass_term_package
    (data : HeteroticOneLoopFiMassTermData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticOneLoopFiMassTerm
      (HeteroticOneLoopFiMassTermPackage data)) :
    HeteroticOneLoopFiMassTermPackage data := by
  exact h_phys

/-- Two-loop vacuum-energy data in the quantum-corrected heterotic vacuum analysis. -/
structure HeteroticTwoLoopVacuumEnergyData where
  anomalyCoefficient : ℤ
  twoLoopVacuumAmplitude : ComplexAmplitude
  boundaryOfGenusTwoModuliControlsAmplitude : HeteroticClaim
  spuriousSingularityResiduesRequired : HeteroticClaim
  factorizesIntoTorusCurrentIntegrals : HeteroticClaim

/-- Heterotic two-loop vacuum package:
genus-two boundary/degeneration contributions with spurious-residue control
yield a nonzero vacuum amplitude when the anomaly coefficient is nonzero. -/
def HeteroticTwoLoopVacuumEnergyPackage
    (data : HeteroticTwoLoopVacuumEnergyData) : Prop :=
  data.boundaryOfGenusTwoModuliControlsAmplitude ∧
  data.spuriousSingularityResiduesRequired ∧
  data.factorizesIntoTorusCurrentIntegrals ∧
  (data.anomalyCoefficient ≠ 0 → data.twoLoopVacuumAmplitude ≠ 0)

/-- Assumed heterotic two-loop vacuum-energy package from Section 11.6.3. -/
theorem heterotic_two_loop_vacuum_energy_package
    (data : HeteroticTwoLoopVacuumEnergyData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticTwoLoopVacuumEnergyFromBoundary
      (HeteroticTwoLoopVacuumEnergyPackage data)) :
    HeteroticTwoLoopVacuumEnergyPackage data := by
  exact h_phys

/-- Shifted-vacuum data for quantum restoration of supersymmetry. -/
structure HeteroticShiftedVacuumData where
  h11 : ℕ
  h21 : ℕ
  hasBothPositiveAndNegativeUOneCharges : HeteroticClaim
  nonzeroChargedScalarVevCancelsDTerm : HeteroticClaim
  supersymmetryRestoredInShiftedVacuum : HeteroticClaim

/-- Shifted heterotic vacuum package:
if both K\"ahler and complex-structure charged multiplets are present, a charged
VEV can cancel the FI `D`-term and restore spacetime supersymmetry. -/
def HeteroticShiftedVacuumPackage (data : HeteroticShiftedVacuumData) : Prop :=
  data.h11 > 0 ∧
  data.h21 > 0 ∧
  data.hasBothPositiveAndNegativeUOneCharges ∧
  data.nonzeroChargedScalarVevCancelsDTerm ∧
  data.supersymmetryRestoredInShiftedVacuum

/-- Assumed shifted-vacuum supersymmetry-restoration package from Section 11.6.4. -/
theorem heterotic_shifted_vacuum_package
    (data : HeteroticShiftedVacuumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringHeteroticShiftedVacuumSupersymmetryRestoration
      (HeteroticShiftedVacuumPackage data)) :
    HeteroticShiftedVacuumPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
