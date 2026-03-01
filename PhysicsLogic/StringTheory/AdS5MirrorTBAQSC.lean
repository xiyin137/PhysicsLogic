import PhysicsLogic.Assumptions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Double-Wick map data relating physical and mirror magnon kinematics. -/
structure MirrorDoubleWickData where
  physicalEnergy : ℝ
  physicalMomentum : ℝ
  mirrorEnergy : ℝ
  mirrorMomentum : ℝ

/-- Double-Wick map package:
`E = i p_tilde`, `p = i E_tilde` in complexified kinematics. -/
def MirrorDoubleWickMapPackage (data : MirrorDoubleWickData) : Prop :=
  (data.physicalEnergy : ℂ) = Complex.I * (data.mirrorMomentum : ℂ) ∧
  (data.physicalMomentum : ℂ) = Complex.I * (data.mirrorEnergy : ℂ)

/-- Assumed mirror double-Wick map package. -/
theorem mirror_double_wick_map_package
    (data : MirrorDoubleWickData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorDoubleWickMap
      (MirrorDoubleWickMapPackage data)) :
    MirrorDoubleWickMapPackage data := by
  exact h_phys

/-- Mirror-magnon dispersion data. -/
structure MirrorMagnonDispersionData where
  mirrorMomentum : ℝ
  interpolatingCoupling : ℝ
  mirrorEnergy : ℝ

/-- Mirror-magnon dispersion package from the all-order magnon relation:
`sinh(E_tilde/2) = sqrt(1+p_tilde^2)/(4 h)`. -/
def MirrorMagnonDispersionPackage (data : MirrorMagnonDispersionData) : Prop :=
  data.interpolatingCoupling > 0 ∧
  Real.sinh (data.mirrorEnergy / 2) =
    Real.sqrt (1 + data.mirrorMomentum ^ (2 : ℕ)) / (4 * data.interpolatingCoupling)

/-- Assumed mirror-magnon dispersion package. -/
theorem mirror_magnon_dispersion_package
    (data : MirrorMagnonDispersionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorMagnonDispersion
      (MirrorMagnonDispersionPackage data)) :
    MirrorMagnonDispersionPackage data := by
  exact h_phys

/-- One-species TBA data. -/
structure OneSpeciesMirrorTBAData where
  inverseTemperature : ℝ
  singleParticleEnergy : ℝ → ℂ
  chemicalPotential : ℂ
  pseudoEnergy : ℝ → ℂ
  convolutionTerm : ℝ → ℂ

/-- One-species TBA package:
`zeta = beta epsilon + mu + K * log(1 + exp(-zeta))`. -/
def OneSpeciesMirrorTBAPackage (data : OneSpeciesMirrorTBAData) : Prop :=
  data.inverseTemperature > 0 ∧
  ∀ u : ℝ,
    data.pseudoEnergy u =
      (data.inverseTemperature : ℂ) * data.singleParticleEnergy u +
        data.chemicalPotential + data.convolutionTerm u

/-- Assumed one-species mirror-TBA package. -/
theorem one_species_mirror_tba_package
    (data : OneSpeciesMirrorTBAData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorSingleSpeciesTba
      (OneSpeciesMirrorTBAPackage data)) :
    OneSpeciesMirrorTBAPackage data := by
  exact h_phys

/-- Excited-state TBA data with defect rapidities. -/
structure MirrorExcitedStateTBAData where
  defectCount : ℕ
  shiftedPseudoEnergy : ℂ → ℂ
  sourceTerm : ℂ → ℂ
  defectShift : ℂ → ℂ
  convolutionTerm : ℂ → ℂ
  defectSpectralParameter : Fin defectCount → ℂ
  quantumNumber : Fin defectCount → ℤ

/-- Excited-state quantization package:
modified TBA equation plus zero condition `1 + exp(-zeta(u_j)) = 0`. -/
def MirrorExcitedStateQuantizationPackage (data : MirrorExcitedStateTBAData) : Prop :=
  (∀ u : ℂ,
    data.shiftedPseudoEnergy u =
      data.sourceTerm u - data.defectShift u + data.convolutionTerm u) ∧
  (∀ j : Fin data.defectCount,
    data.shiftedPseudoEnergy (data.defectSpectralParameter j) =
      -2 * Real.pi * Complex.I * ((data.quantumNumber j : ℂ) + (1 / 2 : ℂ)))

/-- Assumed excited-state mirror-TBA quantization package. -/
theorem mirror_excited_state_quantization_package
    (data : MirrorExcitedStateTBAData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorExcitedStateQuantization
      (MirrorExcitedStateQuantizationPackage data)) :
    MirrorExcitedStateQuantizationPackage data := by
  exact h_phys

/-- Generic mirror Bethe-Yang factorization data. -/
structure MirrorBetheYangFactorizationData (Excitation : Type*) where
  spatialLength : ℝ
  momentum : Excitation → ℂ
  phaseFactor : Excitation → ℂ
  factorizedScattering : Excitation → ℂ

/-- Bethe-Yang factorization package:
`exp(i p_A L) = product_B S^{BA}` in compressed form. -/
def MirrorBetheYangFactorizationPackage {Excitation : Type*}
    (data : MirrorBetheYangFactorizationData Excitation) : Prop :=
  data.spatialLength > 0 ∧
  ∀ e : Excitation,
    data.phaseFactor e =
        Complex.exp (Complex.I * data.momentum e * (data.spatialLength : ℂ)) ∧
      data.phaseFactor e = data.factorizedScattering e

/-- Assumed mirror Bethe-Yang factorization package. -/
theorem mirror_bethe_yang_factorization_package
    {Excitation : Type*}
    (data : MirrorBetheYangFactorizationData Excitation)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorBetheYangSystem
      (MirrorBetheYangFactorizationPackage data)) :
    MirrorBetheYangFactorizationPackage data := by
  exact h_phys

/-- Mirror Bethe-string classification data. -/
structure MirrorBetheStringData where
  interpolatingCoupling : ℝ
  zhukovsky : ℂ → ℂ
  levelITag : String
  levelIITag : String
  levelIIIStringTag : String

/-- Mirror Bethe-string package:
branch-cut Zhukovsky relation and level-I/II/III string-family tags. -/
def MirrorBetheStringPackage (data : MirrorBetheStringData) : Prop :=
  data.interpolatingCoupling > 0 ∧
  (∀ u : ℂ, data.zhukovsky u + 1 / data.zhukovsky u = u / (data.interpolatingCoupling : ℂ)) ∧
  data.levelITag = "bullet_n mirror Q-particles" ∧
  data.levelIITag = "oplus/ominus y-particles and n|yw strings" ∧
  data.levelIIIStringTag = "n|w strings"

/-- Assumed mirror Bethe-string classification package. -/
theorem mirror_bethe_string_package
    (data : MirrorBetheStringData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorBetheStrings
      (MirrorBetheStringPackage data)) :
    MirrorBetheStringPackage data := by
  exact h_phys

/-- Multi-species mirror-TBA data. -/
structure MirrorMultiSpeciesTBAData (Species : Type*) where
  inverseTemperature : ℝ
  pseudoEnergy : Species → ℂ → ℂ
  sourceEnergy : Species → ℂ → ℂ
  chemicalPotential : Species → ℂ
  convolutionTerm : Species → ℂ → ℂ

/-- Multi-species mirror-TBA package:
`zeta_A = beta epsilon_A + mu_A + sum_B K_AB * log(1 + exp(-zeta_B))`. -/
def MirrorMultiSpeciesTBAPackage {Species : Type*}
    (data : MirrorMultiSpeciesTBAData Species) : Prop :=
  data.inverseTemperature > 0 ∧
  ∀ A : Species, ∀ u : ℂ,
    data.pseudoEnergy A u =
      (data.inverseTemperature : ℂ) * data.sourceEnergy A u +
        data.chemicalPotential A + data.convolutionTerm A u

/-- Assumed multi-species mirror-TBA package. -/
theorem mirror_multi_species_tba_package
    {Species : Type*}
    (data : MirrorMultiSpeciesTBAData Species)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorTbaEquationSystem
      (MirrorMultiSpeciesTBAPackage data)) :
    MirrorMultiSpeciesTBAPackage data := by
  exact h_phys

/-- Y-system/Hirota data on a T-hook-like index set. -/
structure MirrorYSystemData where
  y : ℤ → ℤ → ℂ
  yShiftPlus : ℤ → ℤ → ℂ
  yShiftMinus : ℤ → ℤ → ℂ
  t : ℤ → ℤ → ℂ
  tShiftPlus : ℤ → ℤ → ℂ
  tShiftMinus : ℤ → ℤ → ℂ
  tHookIndex : ℤ → ℤ → Prop

/-- Mirror Y-system/Hirota package:
Y-system ratio equation and Hirota bilinear relation on the selected index set. -/
def MirrorYSystemPackage (data : MirrorYSystemData) : Prop :=
  (∀ n m : ℤ, data.tHookIndex n m →
    data.yShiftPlus n m * data.yShiftMinus n m /
        (data.y (n + 1) m * data.y (n - 1) m) =
      ((1 + data.y n (m + 1)) * (1 + data.y n (m - 1))) /
        ((1 + data.y (n + 1) m) * (1 + data.y (n - 1) m)) ) ∧
  (∀ n m : ℤ, data.tHookIndex n m →
    data.tShiftPlus n m * data.tShiftMinus n m =
      data.t (n + 1) m * data.t (n - 1) m +
        data.t n (m + 1) * data.t n (m - 1))

/-- Assumed mirror Y-system/Hirota package. -/
theorem mirror_y_system_package
    (data : MirrorYSystemData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorYSystemHirota
      (MirrorYSystemPackage data)) :
    MirrorYSystemPackage data := by
  exact h_phys

/-- Finite-volume mirror-energy data for excited states. -/
structure FiniteVolumeMirrorEnergyData where
  boundStateCount : ℕ
  physicalDefectCount : ℕ
  physicalDefectMomentum : Fin physicalDefectCount → ℂ
  mirrorDensityContribution : ℂ
  totalEnergy : ℂ

/-- Finite-volume mirror-energy package:
physical-defect energy plus thermal mirror-bath correction. -/
def FiniteVolumeMirrorEnergyPackage (data : FiniteVolumeMirrorEnergyData) : Prop :=
  data.totalEnergy =
    (∑ j : Fin data.physicalDefectCount, Complex.I * data.physicalDefectMomentum j) -
      data.mirrorDensityContribution

/-- Assumed finite-volume mirror-energy package. -/
theorem finite_volume_mirror_energy_package
    (data : FiniteVolumeMirrorEnergyData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorFiniteVolumeEnergy
      (FiniteVolumeMirrorEnergyPackage data)) :
    FiniteVolumeMirrorEnergyPackage data := by
  exact h_phys

/-- Konishi wrapping-correction data in the mirror-TBA framework. -/
structure KonishiWrappingData where
  asymptoticEnergy : ℝ
  wrappingCorrection : ℝ
  fullScalingDimension : ℝ
  circumference : ℕ

/-- Konishi wrapping package:
`Delta_K = Delta_ASY + Delta_wrap` with mirror-TBA circumference assignment. -/
def KonishiWrappingCorrectionPackage (data : KonishiWrappingData) : Prop :=
  data.circumference = 4 ∧
  data.fullScalingDimension = data.asymptoticEnergy + data.wrappingCorrection

/-- Assumed Konishi wrapping-correction package. -/
theorem konishi_wrapping_correction_package
    (data : KonishiWrappingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorKonishiWrapping
      (KonishiWrappingCorrectionPackage data)) :
    KonishiWrappingCorrectionPackage data := by
  exact h_phys

private def idx1 : Fin 4 := ⟨0, by decide⟩
private def idx2 : Fin 4 := ⟨1, by decide⟩
private def idx3 : Fin 4 := ⟨2, by decide⟩
private def idx4 : Fin 4 := ⟨3, by decide⟩

/-- `Pmu`-system data for the AdS5xS5 quantum spectral curve. -/
structure QuantumSpectralCurvePMuData where
  p : Fin 4 → ℂ → ℂ
  pRaised : Fin 4 → ℂ → ℂ
  mu : Fin 4 → Fin 4 → ℂ → ℂ
  pMonodromy : Fin 4 → ℂ → ℂ
  muMonodromy : Fin 4 → Fin 4 → ℂ → ℂ

/-- `Pmu`-system package:
antisymmetric `mu`, quadratic constraint, monodromy relation for `mu`,
and linear monodromy map for `P`. -/
def QuantumSpectralCurvePMuPackage (data : QuantumSpectralCurvePMuData) : Prop :=
  (∀ a b : Fin 4, ∀ u : ℂ, data.mu a b u = -data.mu b a u) ∧
  (∀ u : ℂ,
    data.mu idx1 idx2 u * data.mu idx3 idx4 u -
      data.mu idx1 idx3 u * data.mu idx2 idx4 u +
      data.mu idx1 idx4 u * data.mu idx2 idx3 u = 1) ∧
  (∀ u : ℂ, data.mu idx1 idx4 u = data.mu idx2 idx3 u) ∧
  (∀ a b : Fin 4, ∀ u : ℂ,
    data.muMonodromy a b u - data.mu a b u =
      data.p a u * data.pMonodromy b u - data.p b u * data.pMonodromy a u) ∧
  (∀ a : Fin 4, ∀ u : ℂ,
    data.pMonodromy a u = ∑ b : Fin 4, data.mu a b u * data.pRaised b u)

/-- Assumed `Pmu` quantum-spectral-curve package. -/
theorem quantum_spectral_curve_pmu_package
    (data : QuantumSpectralCurvePMuData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorQuantumSpectralCurvePMu
      (QuantumSpectralCurvePMuPackage data)) :
    QuantumSpectralCurvePMuPackage data := by
  exact h_phys

/-- Large-`u` asymptotic data for the `Pmu` system. -/
structure PMuAsymptoticData where
  chargeJ : ℝ
  scalingDimension : ℝ
  lorentzSpin : ℝ
  a1 : ℂ
  a2 : ℂ
  a3 : ℂ
  a4 : ℂ
  pLeadingPower : Fin 4 → ℝ
  mu12LeadingPower : ℝ
  mu13LeadingPower : ℝ
  mu14LeadingPower : ℝ
  mu24LeadingPower : ℝ
  mu34LeadingPower : ℝ

/-- `Pmu` asymptotic package:
large-`u` powers for `P_a`, `mu_ab`, and coefficient products
`A1 A4`, `A2 A3` fixed by `(J,K,Delta)`. -/
def PMuAsymptoticPackage (data : PMuAsymptoticData) : Prop :=
  data.chargeJ > 1 ∧
  data.pLeadingPower idx1 = -data.chargeJ / 2 ∧
  data.pLeadingPower idx2 = -data.chargeJ / 2 - 1 ∧
  data.pLeadingPower idx3 = data.chargeJ / 2 ∧
  data.pLeadingPower idx4 = data.chargeJ / 2 - 1 ∧
  data.mu12LeadingPower = data.scalingDimension - data.chargeJ ∧
  data.mu13LeadingPower = data.scalingDimension + 1 ∧
  data.mu14LeadingPower = data.scalingDimension ∧
  data.mu24LeadingPower = data.scalingDimension - 1 ∧
  data.mu34LeadingPower = data.scalingDimension + data.chargeJ ∧
  data.a1 * data.a4 =
    Complex.I *
      ((((data.chargeJ + data.lorentzSpin - 2) ^ (2 : ℕ) - data.scalingDimension ^ (2 : ℕ)) : ℂ) *
        (((data.chargeJ - data.lorentzSpin) ^ (2 : ℕ) - data.scalingDimension ^ (2 : ℕ)) : ℂ) /
        (16 * data.chargeJ * (data.chargeJ - 1) : ℂ)) ∧
  data.a2 * data.a3 =
    Complex.I *
      ((((data.chargeJ - data.lorentzSpin + 2) ^ (2 : ℕ) - data.scalingDimension ^ (2 : ℕ)) : ℂ) *
        (((data.chargeJ + data.lorentzSpin) ^ (2 : ℕ) - data.scalingDimension ^ (2 : ℕ)) : ℂ) /
        (16 * data.chargeJ * (data.chargeJ + 1) : ℂ))

/-- Assumed large-`u` asymptotic package for the `Pmu` system. -/
theorem p_mu_asymptotic_package
    (data : PMuAsymptoticData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorPMuAsymptotics
      (PMuAsymptoticPackage data)) :
    PMuAsymptoticPackage data := by
  exact h_phys

/-- Weak-coupling Baxter-reduction data for the `Pmu` system. -/
structure WeakCouplingBaxterData where
  chainLength : ℕ
  spin : ℕ
  baxterQ : ℂ → ℂ
  baxterT : ℂ → ℂ
  oneLoopRoot : Fin spin → ℝ
  oneLoopAnomalousDimension : ℝ

/-- Weak-coupling package:
`Pmu` reduction to the one-loop `SL(2)` Baxter equation and the
one-loop anomalous-dimension root sum. -/
def WeakCouplingBaxterPackage (data : WeakCouplingBaxterData) : Prop :=
  data.chainLength > 0 ∧
  (∀ u : ℂ,
    data.baxterT u * data.baxterQ u =
      data.baxterQ (u + Complex.I) / (u + Complex.I / 2) ^ data.chainLength +
        data.baxterQ (u - Complex.I) / (u - Complex.I / 2) ^ data.chainLength) ∧
  data.oneLoopAnomalousDimension =
    2 * ∑ j : Fin data.spin, 1 / (data.oneLoopRoot j ^ (2 : ℕ) + (1 / 4 : ℝ))

/-- Assumed weak-coupling Baxter-reduction package. -/
theorem weak_coupling_baxter_package
    (data : WeakCouplingBaxterData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorWeakCouplingBaxter
      (WeakCouplingBaxterPackage data)) :
    WeakCouplingBaxterPackage data := by
  exact h_phys

/-- Small-spin expansion data for solving the `Pmu` system. -/
structure SmallSpinExpansionData where
  lorentzSpin : ℝ
  deltaMinusJ : ℝ
  pScale : ℝ
  mu12Leading : ℂ
  mu13Leading : ℂ
  mu14Leading : ℂ
  mu23Leading : ℂ
  mu24Leading : ℂ
  mu34Leading : ℂ

/-- Small-spin expansion package:
`K -> 0` analytic continuation around the BPS vacuum with
`P_a = O(K^{1/2})`, `Delta-J = O(K)`, and leading periodic `mu` data. -/
def SmallSpinExpansionPackage (data : SmallSpinExpansionData) : Prop :=
  data.lorentzSpin ≥ 0 ∧
  data.deltaMinusJ = data.pScale * data.lorentzSpin ∧
  data.mu12Leading = -1 ∧
  data.mu13Leading = 0 ∧
  data.mu14Leading = 1 ∧
  data.mu23Leading = 1 ∧
  data.mu24Leading = -Complex.sinh (2 * Real.pi) ∧
  data.mu34Leading = 0

/-- Assumed small-spin expansion package for the `Pmu` system. -/
theorem small_spin_expansion_package
    (data : SmallSpinExpansionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5MirrorSmallSpinExpansion
      (SmallSpinExpansionPackage data)) :
    SmallSpinExpansionPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
