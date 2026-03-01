import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

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

end PhysicsLogic.QFT.CFT.TwoDimensional
