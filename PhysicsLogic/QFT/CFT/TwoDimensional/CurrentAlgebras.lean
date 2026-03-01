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
  shortLongDistinctionSharp : Bool

/-- Mixed-flux worldsheet deformation package:
`R^2 = alpha' sqrt(K5^2 + g_B^2 Q5^2)`, `mu = g_B Q5 / K5`,
and qualitative long-string-spectrum transition away from `mu=0`. -/
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
  (data.mu ≠ 0 -> data.longStringContinuumPresent = false) /\
  (data.mu ≠ 0 -> data.shortLongDistinctionSharp = false)

/-- Assumed mixed-flux worldsheet deformation package in the 2D CFT lane. -/
theorem ads3_mixed_flux_worldsheet_deformation_package
    (data : AdS3MixedFluxWorldsheetData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxWorldsheetDeformation
      (AdS3MixedFluxWorldsheetDeformationPackage data)) :
    AdS3MixedFluxWorldsheetDeformationPackage data := by
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

end PhysicsLogic.QFT.CFT.TwoDimensional
