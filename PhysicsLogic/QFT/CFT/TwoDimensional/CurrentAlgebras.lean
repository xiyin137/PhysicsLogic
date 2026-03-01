import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.QFT.CFT.TwoDimensional

set_option autoImplicit false

/-- Kronecker delta on integer mode labels. -/
def kroneckerDeltaInt (m n : ℤ) : ℝ :=
  if m = n then 1 else 0

/-- Bosonic AdS3 `SL(2,R)` WZW data in the 2D CFT lane. -/
structure AdS3Sl2BosonicWzwData where
  levelK : ℝ
  radius : ℝ
  alphaPrime : ℝ

/-- Bosonic AdS3 WZW level/radius package:
`k = R^2/alpha'`. -/
def AdS3Sl2BosonicWzwLevelRadiusRelation
    (data : AdS3Sl2BosonicWzwData) : Prop :=
  data.levelK > 2 /\
  data.radius > 0 /\
  data.alphaPrime > 0 /\
  data.levelK = data.radius ^ (2 : Nat) / data.alphaPrime

/-- Assumed bosonic AdS3 WZW level/radius relation in the 2D CFT lane. -/
theorem ads3_sl2_bosonic_wzw_level_radius_relation
    (data : AdS3Sl2BosonicWzwData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3BosonicWzwLevelRadius
      (AdS3Sl2BosonicWzwLevelRadiusRelation data)) :
    AdS3Sl2BosonicWzwLevelRadiusRelation data := by
  exact h_phys

/-- AdS3 `SL(2,R)` spectral-flow data for affine currents and Sugawara Virasoro modes. -/
structure AdS3Sl2SpectralFlowData where
  levelK : ℝ
  flowW : ℤ
  jPlusMode : ℤ → ℂ
  jMinusMode : ℤ → ℂ
  jThreeMode : ℤ → ℝ
  virasoroMode : ℤ → ℝ
  flowedJPlusMode : ℤ → ℂ
  flowedJMinusMode : ℤ → ℂ
  flowedJThreeMode : ℤ → ℝ
  flowedVirasoroMode : ℤ → ℝ

/-- Spectral-flow package:
`J'^±_n = J^±_(n ± w)`,
`J'^3_n = J^3_n - (k/2) w δ_{n,0}`,
`L'_n = L_n + w J^3_n - (k/4) w^2 δ_{n,0}`. -/
def AdS3Sl2SpectralFlowAutomorphism
    (data : AdS3Sl2SpectralFlowData) : Prop :=
  data.levelK > 2 /\
  (forall n : ℤ, data.flowedJPlusMode n = data.jPlusMode (n + data.flowW)) /\
  (forall n : ℤ, data.flowedJMinusMode n = data.jMinusMode (n - data.flowW)) /\
  (forall n : ℤ,
    data.flowedJThreeMode n =
      data.jThreeMode n
        - (data.levelK / 2) * (data.flowW : ℝ) * kroneckerDeltaInt n 0) /\
  (forall n : ℤ,
    data.flowedVirasoroMode n =
      data.virasoroMode n
        + (data.flowW : ℝ) * data.jThreeMode n
        - (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : Nat) * kroneckerDeltaInt n 0)

/-- Assumed AdS3 spectral-flow automorphism package in the 2D CFT lane. -/
theorem ads3_sl2_spectral_flow_automorphism
    (data : AdS3Sl2SpectralFlowData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3Sl2SpectralFlowAutomorphism
      (AdS3Sl2SpectralFlowAutomorphism data)) :
    AdS3Sl2SpectralFlowAutomorphism data := by
  exact h_phys

/-- AdS3 representation-window data for discrete/continuous spectral-flow sectors. -/
structure AdS3Sl2RepresentationSpectrumData where
  levelK : ℝ
  jDiscrete : ℝ
  jReflected : ℝ
  jContinuousRealPart : ℝ
  continuousParameter : ℝ
  alphaParameter : ℝ

/-- AdS3 representation-window package:
discrete `1/2 < j < (k-1)/2` with reflected `j^vee = k/2-j` in same window,
continuous `j = 1/2 + i s`, `s >= 0`, and `alpha in [0,1)`. -/
def AdS3Sl2RepresentationSpectrumPackage
    (data : AdS3Sl2RepresentationSpectrumData) : Prop :=
  data.levelK > 2 /\
  (1 / 2 : ℝ) < data.jDiscrete /\
  data.jDiscrete < (data.levelK - 1) / 2 /\
  data.jReflected = data.levelK / 2 - data.jDiscrete /\
  (1 / 2 : ℝ) < data.jReflected /\
  data.jReflected < (data.levelK - 1) / 2 /\
  data.jContinuousRealPart = (1 / 2 : ℝ) /\
  data.continuousParameter >= 0 /\
  0 <= data.alphaParameter /\
  data.alphaParameter < 1

/-- Assumed AdS3 representation-window package in the 2D CFT lane. -/
theorem ads3_sl2_representation_spectrum_package
    (data : AdS3Sl2RepresentationSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3Sl2RepresentationSpectrum
      (AdS3Sl2RepresentationSpectrumPackage data)) :
    AdS3Sl2RepresentationSpectrumPackage data := by
  exact h_phys

/-- AdS3 bosonic mass-shell and spacetime-energy data in the 2D CFT lane. -/
structure AdS3Sl2MassShellData where
  levelK : ℝ
  spinJ : ℝ
  mQuantum : ℝ
  flowW : ℤ
  currentDescendantLevel : ℝ
  virasoroDescendantLevel : ℝ
  internalWeight : ℝ
  j0Three : ℝ
  spacetimeEnergy : ℝ
  spacetimeAngularMomentum : ℝ

/-- AdS3 mass-shell/energy package:
`-j(j-1)/(k-2) - w m - k w^2/4 + N + ell + h - 1 = 0`,
`J_0^3 = m + k w/2`, and `(E+J)/2 = J_0^3`. -/
def AdS3Sl2MassShellEnergyRelation
    (data : AdS3Sl2MassShellData) : Prop :=
  data.levelK > 2 /\
  data.currentDescendantLevel >= 0 /\
  data.virasoroDescendantLevel >= 0 /\
  data.internalWeight >= 0 /\
  data.j0Three = data.mQuantum + (data.levelK / 2) * (data.flowW : ℝ) /\
  (data.spacetimeEnergy + data.spacetimeAngularMomentum) / 2 = data.j0Three /\
  -(data.spinJ * (data.spinJ - 1)) / (data.levelK - 2)
    - (data.flowW : ℝ) * data.mQuantum
    - (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : Nat)
    + data.currentDescendantLevel + data.virasoroDescendantLevel + data.internalWeight - 1 = 0

/-- Assumed AdS3 mass-shell/energy package in the 2D CFT lane. -/
theorem ads3_sl2_mass_shell_energy_relation
    (data : AdS3Sl2MassShellData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3Sl2MassShellEnergyRelation
      (AdS3Sl2MassShellEnergyRelation data)) :
    AdS3Sl2MassShellEnergyRelation data := by
  exact h_phys

/-- Purely `(NS,NS)` AdS3xS3xM4 worldsheet matter-SCFT data. -/
structure AdS3NsnsWorldsheetMatterData where
  levelK : ℝ
  radius : ℝ
  alphaPrime : ℝ
  slCentralCharge : ℝ
  suCentralCharge : ℝ
  internalCentralCharge : ℝ
  totalMatterCentralCharge : ℝ

/-- `(NS,NS)` worldsheet-matter package:
`R^2 = k alpha'`,
`c_sl = 3(k+2)/k + 3/2`, `c_su = 3(k-2)/k + 3/2`,
`c_int = 6`, total `c = 15`. -/
def AdS3NsnsWorldsheetMatterScftPackage
    (data : AdS3NsnsWorldsheetMatterData) : Prop :=
  data.levelK > 0 /\
  data.radius > 0 /\
  data.alphaPrime > 0 /\
  data.radius ^ (2 : Nat) = data.levelK * data.alphaPrime /\
  data.slCentralCharge = 3 * (data.levelK + 2) / data.levelK + (3 / 2 : ℝ) /\
  data.suCentralCharge = 3 * (data.levelK - 2) / data.levelK + (3 / 2 : ℝ) /\
  data.internalCentralCharge = 6 /\
  data.totalMatterCentralCharge =
    data.slCentralCharge + data.suCentralCharge + data.internalCentralCharge /\
  data.totalMatterCentralCharge = 15

/-- Assumed `(NS,NS)` worldsheet matter-SCFT package in the 2D CFT lane. -/
theorem ads3_nsns_worldsheet_matter_scft_package
    (data : AdS3NsnsWorldsheetMatterData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsWorldsheetMatterScft
      (AdS3NsnsWorldsheetMatterScftPackage data)) :
    AdS3NsnsWorldsheetMatterScftPackage data := by
  exact h_phys

/-- Bosonic-level shifts used in supersymmetric AdS3/S3 WZW current-algebra construction. -/
structure AdS3NsnsAffineLevelShiftData where
  levelK : ℝ
  slBosonicLevel : ℝ
  suBosonicLevel : ℝ
  slCurrentShiftByFermionBilinearUsed : Bool
  suCurrentShiftByFermionBilinearUsed : Bool

/-- `(NS,NS)` affine-level-shift package:
`sl` bosonic level `k+2`, `su` bosonic level `k-2`, and superconformal-current
construction via fermion-bilinear shifts of bosonic currents. -/
def AdS3NsnsAffineLevelShiftPackage
    (data : AdS3NsnsAffineLevelShiftData) : Prop :=
  data.levelK > 2 /\
  data.slBosonicLevel = data.levelK + 2 /\
  data.suBosonicLevel = data.levelK - 2 /\
  data.slCurrentShiftByFermionBilinearUsed = true /\
  data.suCurrentShiftByFermionBilinearUsed = true

/-- Assumed `(NS,NS)` affine-level-shift package in the 2D CFT lane. -/
theorem ads3_nsns_affine_level_shift_package
    (data : AdS3NsnsAffineLevelShiftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsAffineLevelShift
      (AdS3NsnsAffineLevelShiftPackage data)) :
    AdS3NsnsAffineLevelShiftPackage data := by
  exact h_phys

/-- Sign assignment data for Ramond spin fields in the AdS3/S3/T4 worldsheet SCFT. -/
structure AdS3NsnsSpinFieldGsoData where
  epsilon1 : ℤ
  epsilon2 : ℤ
  epsilon3 : ℤ
  epsilon4 : ℤ
  epsilon5 : ℤ
  supersymmetryCurrentCount : Nat

/-- Two-valued sign condition (`epsilon` equals plus or minus `1`). -/
def IsSign (ε : ℤ) : Prop :=
  ε = 1 \/ ε = -1

/-- AdS3 `(NS,NS)` spin-field/GSO package:
`epsilon_1 epsilon_2 epsilon_3 = 1`, `epsilon_4 epsilon_5 = 1`, each sign in
`{+1,-1}`, and `16` BRST-invariant supersymmetry currents. -/
def AdS3NsnsSpinFieldGsoConstraintPackage
    (data : AdS3NsnsSpinFieldGsoData) : Prop :=
  IsSign data.epsilon1 /\
  IsSign data.epsilon2 /\
  IsSign data.epsilon3 /\
  IsSign data.epsilon4 /\
  IsSign data.epsilon5 /\
  data.epsilon1 * data.epsilon2 * data.epsilon3 = 1 /\
  data.epsilon4 * data.epsilon5 = 1 /\
  data.supersymmetryCurrentCount = 16

/-- Assumed AdS3 `(NS,NS)` spin-field/GSO package in the 2D CFT lane. -/
theorem ads3_nsns_spin_field_gso_constraint_package
    (data : AdS3NsnsSpinFieldGsoData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsSpinFieldGsoConstraints
      (AdS3NsnsSpinFieldGsoConstraintPackage data)) :
    AdS3NsnsSpinFieldGsoConstraintPackage data := by
  exact h_phys

/-- Spectral-flow data for the supersymmetric `hatSL(2)_k` algebra in the `(NS,NS)` sector. -/
structure AdS3NsnsSl2SpectralFlowData where
  levelK : ℝ
  flowW : ℤ
  psiPlusMode : ℚ → ℂ
  psiMinusMode : ℚ → ℂ
  psiThreeMode : ℚ → ℂ
  currentPlusMode : ℤ → ℂ
  currentMinusMode : ℤ → ℂ
  currentThreeMode : ℤ → ℝ
  virasoroMode : ℤ → ℝ
  supercurrentMode : ℚ → ℂ
  flowedPsiPlusMode : ℚ → ℂ
  flowedPsiMinusMode : ℚ → ℂ
  flowedPsiThreeMode : ℚ → ℂ
  flowedCurrentPlusMode : ℤ → ℂ
  flowedCurrentMinusMode : ℤ → ℂ
  flowedCurrentThreeMode : ℤ → ℝ
  flowedVirasoroMode : ℤ → ℝ
  flowedSupercurrentMode : ℚ → ℂ

/-- `(NS,NS)` supersymmetric `hatSL(2)_k` spectral-flow package:
`psi'^±_r = psi^±_(r ± w)`, `psi'^3_r = psi^3_r`,
`J'^±_n = J^±_(n ± w)`, `J'^3_n = J^3_n - (k/2)w delta_{n,0}`,
`L'_n = L_n + w J_n^3 - (k/4)w^2 delta_{n,0}`,
`G'_r = G_r + w psi_r^3`. -/
def AdS3NsnsSl2SpectralFlowAutomorphism
    (data : AdS3NsnsSl2SpectralFlowData) : Prop :=
  data.levelK > 0 /\
  (forall r : ℚ,
    data.flowedPsiPlusMode r = data.psiPlusMode (r + (data.flowW : ℚ))) /\
  (forall r : ℚ,
    data.flowedPsiMinusMode r = data.psiMinusMode (r - (data.flowW : ℚ))) /\
  (forall r : ℚ, data.flowedPsiThreeMode r = data.psiThreeMode r) /\
  (forall n : ℤ,
    data.flowedCurrentPlusMode n = data.currentPlusMode (n + data.flowW)) /\
  (forall n : ℤ,
    data.flowedCurrentMinusMode n = data.currentMinusMode (n - data.flowW)) /\
  (forall n : ℤ,
    data.flowedCurrentThreeMode n =
      data.currentThreeMode n -
        (data.levelK / 2) * (data.flowW : ℝ) * kroneckerDeltaInt n 0) /\
  (forall n : ℤ,
    data.flowedVirasoroMode n =
      data.virasoroMode n + (data.flowW : ℝ) * data.currentThreeMode n -
        (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : Nat) * kroneckerDeltaInt n 0) /\
  (forall r : ℚ,
    data.flowedSupercurrentMode r =
      data.supercurrentMode r + ((data.flowW : ℂ) * data.psiThreeMode r))

/-- Assumed `(NS,NS)` supersymmetric `hatSL(2)_k` spectral-flow package in the 2D CFT lane. -/
theorem ads3_nsns_sl2_spectral_flow_automorphism
    (data : AdS3NsnsSl2SpectralFlowData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsSl2SpectralFlowAutomorphism
      (AdS3NsnsSl2SpectralFlowAutomorphism data)) :
    AdS3NsnsSl2SpectralFlowAutomorphism data := by
  exact h_phys

/-- `(NS,NS)` superstring mass-shell/BPS data in the AdS3/S3/M4 worldsheet SCFT. -/
structure AdS3NsnsSuperstringMassShellData where
  levelK : ℝ
  spinJ : ℝ
  mQuantum : ℝ
  flowW : ℤ
  adsDescendantLevel : ℝ
  suDescendantLevel : ℝ
  internalWeight : ℝ
  suSpin : ℝ
  j0Three : ℝ
  flowedLZero : ℝ

/-- `(NS,NS)` superstring mass-shell package:
`L0^flow = -j(j-1)/k - w m - k w^2/4 + N`,
`L0^flow + N_su + h_int = 1/2`,
`J_0^3 = m + k w/2`,
and BPS lower bound `J_0^3 >= j' + h_int`. -/
def AdS3NsnsSuperstringMassShellBpsPackage
    (data : AdS3NsnsSuperstringMassShellData) : Prop :=
  data.levelK > 0 /\
  data.adsDescendantLevel >= 0 /\
  data.suDescendantLevel >= 0 /\
  data.internalWeight >= 0 /\
  data.j0Three = data.mQuantum + (data.levelK / 2) * (data.flowW : ℝ) /\
  data.flowedLZero =
    -(data.spinJ * (data.spinJ - 1)) / data.levelK -
      (data.flowW : ℝ) * data.mQuantum -
      (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : Nat) +
      data.adsDescendantLevel /\
  data.flowedLZero + data.suDescendantLevel + data.internalWeight = (1 / 2 : ℝ) /\
  data.j0Three >= data.suSpin + data.internalWeight

/-- Assumed `(NS,NS)` superstring mass-shell/BPS package in the 2D CFT lane. -/
theorem ads3_nsns_superstring_mass_shell_bps_package
    (data : AdS3NsnsSuperstringMassShellData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsSuperstringMassShellBps
      (AdS3NsnsSuperstringMassShellBpsPackage data)) :
    AdS3NsnsSuperstringMassShellBpsPackage data := by
  exact h_phys

/-- Mixed `(NS,NS)`/`(R,R)` AdS3 worldsheet deformation data in the 2D-CFT lane. -/
structure AdS3MixedFluxWorldsheetData where
  stringCoupling : ℝ
  alphaPrime : ℝ
  nsFluxK5 : ℕ
  rrFluxQ5 : ℕ
  radius : ℝ
  mu : ℝ
  longStringContinuumPresent : Bool
  longStringSpectrumDiscrete : Bool
  shortLongDistinctionSharp : Bool
  longStringsReachBoundaryAtFiniteEnergy : Bool
  nsnsLongStringThresholdDimension : ℝ

/-- Mixed-flux worldsheet deformation package:
`R^2 = alpha' sqrt(K5^2 + g_B^2 Q5^2)`, `mu = g_B Q5 / K5`,
plus long-string threshold/discretization transition across `mu=0`. -/
def AdS3MixedFluxWorldsheetDeformationPackage
    (data : AdS3MixedFluxWorldsheetData) : Prop :=
  data.stringCoupling > 0 /\
  data.alphaPrime > 0 /\
  data.nsFluxK5 > 0 /\
  data.radius > 0 /\
  data.radius ^ (2 : Nat) =
    data.alphaPrime *
      Real.sqrt
        ((data.nsFluxK5 : ℝ) ^ (2 : Nat) +
          (data.stringCoupling * (data.rrFluxQ5 : ℝ)) ^ (2 : Nat)) /\
  data.mu = data.stringCoupling * (data.rrFluxQ5 : ℝ) / (data.nsFluxK5 : ℝ) /\
  (data.mu = 0 -> data.longStringContinuumPresent = true) /\
  (data.mu = 0 -> data.longStringSpectrumDiscrete = false) /\
  (data.mu = 0 -> data.shortLongDistinctionSharp = true) /\
  (data.mu = 0 -> data.longStringsReachBoundaryAtFiniteEnergy = true) /\
  (data.mu = 0 ->
    data.nsnsLongStringThresholdDimension = (data.nsFluxK5 : ℝ) / 2) /\
  (data.mu ≠ 0 -> data.longStringContinuumPresent = false) /\
  (data.mu ≠ 0 -> data.longStringSpectrumDiscrete = true) /\
  (data.mu ≠ 0 -> data.longStringsReachBoundaryAtFiniteEnergy = false) /\
  (data.mu ≠ 0 -> data.shortLongDistinctionSharp = false)

/-- Assumed mixed-flux worldsheet deformation package in the 2D CFT lane. -/
theorem ads3_mixed_flux_worldsheet_deformation_package
    (data : AdS3MixedFluxWorldsheetData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxWorldsheetDeformation
      (AdS3MixedFluxWorldsheetDeformationPackage data)) :
    AdS3MixedFluxWorldsheetDeformationPackage data := by
  exact h_phys

/-- Data for the mixed-flux parameter-definition block `mu = g_B Q5 / K5`, `k = K5`
in the QFT lane. -/
structure AdS3MixedFluxMuKDefinitionCftData where
  stringCoupling : ℝ
  rrFluxQ5 : ℕ
  nsFluxK5 : ℕ
  mu : ℝ
  levelK : ℝ

/-- Mixed-flux `mu`/`k` definition package in the QFT lane:
`mu = g_B Q5 / K5` and `k = K5`, with positive coupling and flux data. -/
def AdS3MixedFluxMuKDefinitionCftPackage
    (data : AdS3MixedFluxMuKDefinitionCftData) : Prop :=
  data.stringCoupling > 0 /\
  data.rrFluxQ5 > 0 /\
  data.nsFluxK5 > 0 /\
  data.levelK > 0 /\
  data.levelK = (data.nsFluxK5 : ℝ) /\
  data.mu = data.stringCoupling * (data.rrFluxQ5 : ℝ) / (data.nsFluxK5 : ℝ)

/-- Assumed mixed-flux `mu`/`k` definition package in the 2D CFT lane. -/
theorem ads3_mixed_flux_mu_k_definition_cft_package
    (data : AdS3MixedFluxMuKDefinitionCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxMuKDefinition
      (AdS3MixedFluxMuKDefinitionCftPackage data)) :
    AdS3MixedFluxMuKDefinitionCftPackage data := by
  exact h_phys

/-- Data for the mixed-flux pulsating turning-point relation in the QFT lane. -/
structure AdS3MixedFluxPulsatingTurningPointCftData where
  alphaPrime : ℝ
  radiusSquared : ℝ
  k5Flux : ℝ
  maximalRadius : ℝ
  turningPointEnergy : ℝ
  radialVelocityAtTurningPoint : ℝ
  maximalRadiusIsTurningPoint : Bool

/-- Mixed-flux pulsating turning-point package in the QFT lane:
`r0` is maximal radius of oscillatory motion, with turning-point condition
`dot r = 0`, and
`Delta = (R^2/alpha') r0 sqrt(1+r0^2) - K5 r0^2`. -/
def AdS3MixedFluxPulsatingTurningPointCftPackage
    (data : AdS3MixedFluxPulsatingTurningPointCftData) : Prop :=
  data.alphaPrime > 0 /\
  data.radiusSquared > 0 /\
  data.k5Flux > 0 /\
  data.maximalRadius >= 0 /\
  data.maximalRadiusIsTurningPoint = true /\
  data.radialVelocityAtTurningPoint = 0 /\
  data.turningPointEnergy =
    (data.radiusSquared / data.alphaPrime) * data.maximalRadius *
      Real.sqrt (1 + data.maximalRadius ^ (2 : Nat)) -
      data.k5Flux * data.maximalRadius ^ (2 : Nat)

/-- Assumed mixed-flux pulsating turning-point package in the 2D CFT lane. -/
theorem ads3_mixed_flux_pulsating_turning_point_cft_package
    (data : AdS3MixedFluxPulsatingTurningPointCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingTurningPoint
      (AdS3MixedFluxPulsatingTurningPointCftPackage data)) :
    AdS3MixedFluxPulsatingTurningPointCftPackage data := by
  exact h_phys

/-- Data for mixed-flux pulsating integral quantization in the QFT lane. -/
structure AdS3MixedFluxPulsatingIntegralQuantizationCftData where
  alphaPrime : ℝ
  radiusSquared : ℝ
  excitationNumber : ℤ
  maximalRadius : ℝ
  bohrSommerfeldPeriod : ℝ
  bohrSommerfeldPeriodRepresentsTwoPi : Bool
  bohrSommerfeldIntegral : ℝ

/-- Mixed-flux pulsating integral-quantization package in the QFT lane:
`2 ∮_0^{r0} dr (R^2/alpha') (dot r/(1+r^2)) = period * n`,
with `period` marked as `2pi`. -/
def AdS3MixedFluxPulsatingIntegralQuantizationCftPackage
    (data : AdS3MixedFluxPulsatingIntegralQuantizationCftData) : Prop :=
  data.alphaPrime > 0 /\
  data.radiusSquared > 0 /\
  data.maximalRadius >= 0 /\
  (data.excitationNumber : ℝ) >= 0 /\
  data.bohrSommerfeldPeriod > 0 /\
  data.bohrSommerfeldPeriodRepresentsTwoPi = true /\
  data.bohrSommerfeldIntegral =
    data.bohrSommerfeldPeriod * (data.excitationNumber : ℝ)

/-- Assumed mixed-flux pulsating integral-quantization package in the 2D CFT lane. -/
theorem ads3_mixed_flux_pulsating_integral_quantization_cft_package
    (data : AdS3MixedFluxPulsatingIntegralQuantizationCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingIntegralQuantization
      (AdS3MixedFluxPulsatingIntegralQuantizationCftPackage data)) :
    AdS3MixedFluxPulsatingIntegralQuantizationCftPackage data := by
  exact h_phys

/-- Data for mixed-flux pulsating Bohr-Sommerfeld quantization in the QFT lane. -/
structure AdS3MixedFluxPulsatingBohrSommerfeldCftData where
  turningPoint : AdS3MixedFluxPulsatingTurningPointCftData
  integral : AdS3MixedFluxPulsatingIntegralQuantizationCftData

/-- Mixed-flux pulsating Bohr-Sommerfeld package in the QFT lane:
compositional package combining the turning-point relation and integral
quantization unit, with shared `alpha'`, `R^2`, and `r0` data. -/
def AdS3MixedFluxPulsatingBohrSommerfeldCftPackage
    (data : AdS3MixedFluxPulsatingBohrSommerfeldCftData) : Prop :=
  AdS3MixedFluxPulsatingTurningPointCftPackage data.turningPoint /\
  AdS3MixedFluxPulsatingIntegralQuantizationCftPackage data.integral /\
  data.turningPoint.alphaPrime = data.integral.alphaPrime /\
  data.turningPoint.radiusSquared = data.integral.radiusSquared /\
  data.turningPoint.maximalRadius = data.integral.maximalRadius

/-- Assumed mixed-flux pulsating Bohr-Sommerfeld package in the 2D CFT lane. -/
theorem ads3_mixed_flux_pulsating_bohr_sommerfeld_cft_package
    (data : AdS3MixedFluxPulsatingBohrSommerfeldCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingBohrSommerfeld
      (AdS3MixedFluxPulsatingBohrSommerfeldCftPackage data)) :
    AdS3MixedFluxPulsatingBohrSommerfeldCftPackage data := by
  exact h_phys

/-- Semiclassical circular-pulsating spectrum data in mixed-flux AdS3 backgrounds. -/
structure AdS3MixedFluxPulsatingSpectrumData where
  excitationNumber : ℝ
  levelK : ℝ
  mu : ℝ
  delta : ℝ

/-- Mixed-flux circular-pulsating spectrum package:
`Delta = -2n + 2sqrt(nk) + mu^2 (...)` to leading nontrivial order. -/
def AdS3MixedFluxPulsatingSpectrumPackage
    (data : AdS3MixedFluxPulsatingSpectrumData) : Prop :=
  data.excitationNumber > 0 /\
  data.levelK > 0 /\
  data.mu >= 0 /\
  data.delta =
    -2 * data.excitationNumber + 2 * Real.sqrt (data.excitationNumber * data.levelK) +
      data.mu ^ (2 : Nat) *
        (Real.sqrt (data.excitationNumber * data.levelK) / 2 +
          (2 * data.excitationNumber * data.levelK -
              3 * data.excitationNumber * Real.sqrt (data.excitationNumber * data.levelK)) /
            (2 * (2 * Real.sqrt data.excitationNumber - Real.sqrt data.levelK) ^ (2 : Nat)))

/-- Assumed mixed-flux circular-pulsating spectrum package in the 2D CFT lane. -/
theorem ads3_mixed_flux_pulsating_spectrum_package
    (data : AdS3MixedFluxPulsatingSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingSpectrumShift
      (AdS3MixedFluxPulsatingSpectrumPackage data)) :
    AdS3MixedFluxPulsatingSpectrumPackage data := by
  exact h_phys

/-- Data for the mixed-flux pulsating-threshold relation in the QFT lane. -/
structure AdS3MixedFluxPulsatingThresholdCftData where
  excitationNumber : ℝ
  levelK : ℝ
  poleExcitationNumber : ℝ
  muOrderTwoCorrectionDenominator : ℝ
  shortStringEnergyAtPole : ℝ
  nsnsLongStringThresholdDimension : ℝ

/-- Mixed-flux pulsating-threshold package in the QFT lane:
the order-`mu^2` pulsating correction denominator vanishes at `n = k/4`,
and the `mu=0` short-string energy at that point equals the NSNS long-string
continuum threshold `Delta = k/2`. -/
def AdS3MixedFluxPulsatingThresholdCftPackage
    (data : AdS3MixedFluxPulsatingThresholdCftData) : Prop :=
  data.excitationNumber > 0 /\
  data.levelK > 0 /\
  data.poleExcitationNumber = data.levelK / 4 /\
  data.muOrderTwoCorrectionDenominator =
    2 * Real.sqrt data.excitationNumber - Real.sqrt data.levelK /\
  (data.excitationNumber = data.poleExcitationNumber ->
    data.muOrderTwoCorrectionDenominator = 0) /\
  data.shortStringEnergyAtPole =
    -2 * data.poleExcitationNumber +
      2 * Real.sqrt (data.poleExcitationNumber * data.levelK) /\
  data.nsnsLongStringThresholdDimension = data.levelK / 2 /\
  data.shortStringEnergyAtPole = data.nsnsLongStringThresholdDimension

/-- Assumed mixed-flux pulsating-threshold package in the 2D CFT lane. -/
theorem ads3_mixed_flux_pulsating_threshold_cft_package
    (data : AdS3MixedFluxPulsatingThresholdCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingThresholdPole
      (AdS3MixedFluxPulsatingThresholdCftPackage data)) :
    AdS3MixedFluxPulsatingThresholdCftPackage data := by
  exact h_phys

/-- `(NS,NS)/(R,R)` mixed-flux RR-deformation data in the worldsheet-SFT/CFT lane. -/
structure AdS3MixedFluxSftRrDeformationCftData where
  mu : ℝ
  levelK : ℝ
  firstOrderRrVertexUsed : Bool
  projectedTwoStringBracketVanishesAtFiniteK : Bool
  secondOrderFieldSetToZero : Bool
  secondOrderCorrectionUsesSiegelResolvent : Bool
  secondOrderEquationCoefficient : ℝ
  largeKNormalizationMatchingUsed : Bool

/-- Worldsheet-SFT RR-deformation package for mixed-flux AdS3 backgrounds:
`Q_B W^(2) = -(1/2) P^+ [W^(1) ⊗ W^(1)]`, finite-`k` vanishing of projected
two-string bracket, and resulting order-`mu^2` Siegel-resolvent correction. -/
def AdS3MixedFluxSftRrDeformationCftPackage
    (data : AdS3MixedFluxSftRrDeformationCftData) : Prop :=
  data.mu >= 0 /\
  data.levelK > 0 /\
  data.firstOrderRrVertexUsed = true /\
  data.projectedTwoStringBracketVanishesAtFiniteK = true /\
  data.secondOrderFieldSetToZero = true /\
  data.secondOrderCorrectionUsesSiegelResolvent = true /\
  data.secondOrderEquationCoefficient = (-(1 / 2 : ℝ)) /\
  data.largeKNormalizationMatchingUsed = true

/-- Assumed mixed-flux RR-deformation SFT package in the 2D CFT lane. -/
theorem ads3_mixed_flux_sft_rr_deformation_cft_package
    (data : AdS3MixedFluxSftRrDeformationCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxSftRrDeformation
      (AdS3MixedFluxSftRrDeformationCftPackage data)) :
    AdS3MixedFluxSftRrDeformationCftPackage data := by
  exact h_phys

/-- Mass-shift data from RR-deformation four-point amplitudes in mixed-flux AdS3. -/
structure AdS3MixedFluxMassShiftFromFourPointCftData where
  mu : ℝ
  alphaPrime : ℝ
  scalingDimensionMu : ℝ
  scalingDimensionZero : ℝ
  massSquaredShift : ℝ
  fourPointAmplitude : ℝ
  noZeroWeightInWOneBracket : Bool
  noZeroWeightInNestedBracket : Bool

/-- RR-deformation mass-shift package:
`Delta(mu) = Delta(0) - (alpha'/2) delta m^2` and
`delta m^2|_{mu^2} = mu^2 A_(0,4) / alpha'` with no-zero-weight intermediate
states in the relevant nested brackets. -/
def AdS3MixedFluxMassShiftFromFourPointCftPackage
    (data : AdS3MixedFluxMassShiftFromFourPointCftData) : Prop :=
  data.mu >= 0 /\
  data.alphaPrime > 0 /\
  data.noZeroWeightInWOneBracket = true /\
  data.noZeroWeightInNestedBracket = true /\
  data.scalingDimensionMu =
    data.scalingDimensionZero - (data.alphaPrime / 2) * data.massSquaredShift /\
  data.massSquaredShift =
    data.mu ^ (2 : Nat) * data.fourPointAmplitude / data.alphaPrime

/-- Assumed RR-deformation mass-shift package in the 2D CFT lane. -/
theorem ads3_mixed_flux_mass_shift_from_four_point_cft_package
    (data : AdS3MixedFluxMassShiftFromFourPointCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxMassShiftFromFourPoint
      (AdS3MixedFluxMassShiftFromFourPointCftPackage data)) :
    AdS3MixedFluxMassShiftFromFourPointCftPackage data := by
  exact h_phys

/-- Finite-`k` WZW four-point-reduction data in the mixed-flux AdS3 QFT lane. -/
structure AdS3MixedFluxFiniteKWzwFourPointReductionCftData where
  levelK : ℝ
  mu : ℝ
  slBosonicLevel : ℝ
  suBosonicLevel : ℝ
  usesSlFundamentalPair : Bool
  usesSuFundamentalPair : Bool
  usesSlGenericPair : Bool
  usesSuGenericPair : Bool
  reductionToSlFourPointFunctions : Bool
  reductionToSuFourPointFunctions : Bool
  largeKFiniteNOverKAgreementWithSemiclassical : Bool

/-- Finite-`k` mixed-flux WZW reduction package in the QFT lane:
RR-deformation mass-shift data reduced to bosonic
`SL(2)_{k+2}`/`SU(2)_{k-2}` four-point functions with fundamental and generic
pair insertions, plus large-`k` (`n/k` fixed) semiclassical agreement. -/
def AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage
    (data : AdS3MixedFluxFiniteKWzwFourPointReductionCftData) : Prop :=
  data.levelK > 2 /\
  data.mu >= 0 /\
  data.slBosonicLevel = data.levelK + 2 /\
  data.suBosonicLevel = data.levelK - 2 /\
  data.usesSlFundamentalPair = true /\
  data.usesSuFundamentalPair = true /\
  data.usesSlGenericPair = true /\
  data.usesSuGenericPair = true /\
  data.reductionToSlFourPointFunctions = true /\
  data.reductionToSuFourPointFunctions = true /\
  data.largeKFiniteNOverKAgreementWithSemiclassical = true

/-- Assumed finite-`k` WZW four-point-reduction package in the 2D CFT lane. -/
theorem ads3_mixed_flux_finite_k_wzw_four_point_reduction_cft_package
    (data : AdS3MixedFluxFiniteKWzwFourPointReductionCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxFiniteKWzwFourPointReduction
      (AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage data)) :
    AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage data := by
  exact h_phys

/-- Finite-`k` WZW OPE-constant normalization data in the mixed-flux AdS3 QFT lane. -/
structure AdS3MixedFluxWzwOpeStructureConstantCftData where
  levelK : ℝ
  cSuHalfHalfOne : ℝ
  cSlMinusHalfMinusHalfMinusOne : ℝ
  suIdentityOpeCoefficient : ℝ
  slIdentityOpeCoefficient : ℝ
  cSuLargeKAsymptoticValue : ℝ
  cSlLargeKAsymptoticValue : ℝ

/-- Finite-`k` WZW OPE-constant package in the QFT lane:
identity OPE normalization, `SL(2)`/`SU(2)` structure-constant relation
`C^sl_{-1/2,-1/2,-1} = (4/3)/C^su_{1/2,1/2,1}`, and shared large-`k`
asymptotic value `2/sqrt(3)`. -/
def AdS3MixedFluxWzwOpeStructureConstantCftPackage
    (data : AdS3MixedFluxWzwOpeStructureConstantCftData) : Prop :=
  data.levelK > 3 /\
  data.suIdentityOpeCoefficient = 1 /\
  data.slIdentityOpeCoefficient = 1 /\
  data.cSuHalfHalfOne > 0 /\
  data.cSlMinusHalfMinusHalfMinusOne > 0 /\
  data.cSlMinusHalfMinusHalfMinusOne = (4 / 3 : ℝ) / data.cSuHalfHalfOne /\
  data.cSuLargeKAsymptoticValue = 2 / Real.sqrt 3 /\
  data.cSlLargeKAsymptoticValue = 2 / Real.sqrt 3

/-- Assumed finite-`k` WZW OPE-constant package in the 2D CFT lane. -/
theorem ads3_mixed_flux_wzw_ope_structure_constant_cft_package
    (data : AdS3MixedFluxWzwOpeStructureConstantCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxWzwOpeStructureConstants
      (AdS3MixedFluxWzwOpeStructureConstantCftPackage data)) :
    AdS3MixedFluxWzwOpeStructureConstantCftPackage data := by
  exact h_phys

/-- Data for the explicit mixed-flux RR-deformation two-string bracket in the QFT lane. -/
structure AdS3MixedFluxRrTwoStringBracketCftData where
  levelK : ℝ
  mu : ℝ
  z0Abs : ℝ
  normalizationN1 : ℝ
  overallCoefficient : ℝ
  cSlMinusHalfMinusHalfMinusOne : ℝ
  cSuHalfHalfOne : ℝ
  slPower : ℝ
  suPower : ℝ
  slRelativeSign : ℤ
  suRelativeSign : ℤ
  projectedZeroWeightVanishesAtFiniteK : Bool

/-- Mixed-flux RR-deformation two-string-bracket package in the QFT lane:
`[W^(1) ⊗ W^(1)]` split into `SL(2)`/`SU(2)` adjoint channels with opposite
`|2 z0|^{±4/k}` powers and finite-`k` vanishing projected zero-weight part. -/
def AdS3MixedFluxRrTwoStringBracketCftPackage
    (data : AdS3MixedFluxRrTwoStringBracketCftData) : Prop :=
  data.levelK > 0 /\
  data.mu >= 0 /\
  data.z0Abs > 0 /\
  data.normalizationN1 > 0 /\
  data.cSlMinusHalfMinusHalfMinusOne > 0 /\
  data.cSuHalfHalfOne > 0 /\
  data.overallCoefficient = -16 * data.normalizationN1 ^ (2 : Nat) /\
  data.slPower = -(4 / data.levelK) /\
  data.suPower = 4 / data.levelK /\
  data.suPower = -data.slPower /\
  data.slRelativeSign = -1 /\
  data.suRelativeSign = 1 /\
  data.projectedZeroWeightVanishesAtFiniteK = true

/-- Assumed mixed-flux RR-deformation two-string-bracket package in the 2D CFT lane. -/
theorem ads3_mixed_flux_rr_two_string_bracket_cft_package
    (data : AdS3MixedFluxRrTwoStringBracketCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxRrTwoStringBracketStructure
      (AdS3MixedFluxRrTwoStringBracketCftPackage data)) :
    AdS3MixedFluxRrTwoStringBracketCftPackage data := by
  exact h_phys

end PhysicsLogic.QFT.CFT.TwoDimensional
