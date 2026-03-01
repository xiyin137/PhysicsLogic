import PhysicsLogic.Assumptions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- One-loop planar spin-chain data in the `SU(2)` sector. -/
structure OneLoopSpinChainData where
  chainLength : ℕ
  tHooftCoupling : ℝ
  permutationEigenvalue : Fin chainLength → ℝ
  oneLoopHamiltonian : ℝ
  anomalousDimension : ℝ

/-- One-loop Heisenberg spin-chain package:
`H_1 = (1/(8 pi^2)) sum_l (1-P_{l,l+1})` and `gamma^(1) = lambda H_1`. -/
def OneLoopSpinChainPackage (data : OneLoopSpinChainData) : Prop :=
  data.chainLength > 0 ∧
  data.tHooftCoupling ≥ 0 ∧
  data.oneLoopHamiltonian =
    (1 / (8 * Real.pi ^ (2 : ℕ))) *
      (∑ ℓ : Fin data.chainLength, (1 - data.permutationEigenvalue ℓ)) ∧
  data.anomalousDimension = data.tHooftCoupling * data.oneLoopHamiltonian

/-- Assumed one-loop `SU(2)` Heisenberg spin-chain package in planar `N=4` SYM. -/
theorem one_loop_spin_chain_package
    (data : OneLoopSpinChainData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityOneLoopSpinChain
      (OneLoopSpinChainPackage data)) :
    OneLoopSpinChainPackage data := by
  exact h_phys

/-- Single-magnon kinematics data on a periodic spin chain. -/
structure SingleMagnonDispersionData where
  chainLength : ℕ
  modeNumber : ℤ
  momentum : ℝ
  oneLoopEnergy : ℝ

/-- One-loop single-magnon dispersion package:
`p = 2 pi n / L` and `epsilon(p) = (1/(2 pi^2)) sin^2(p/2)`. -/
def SingleMagnonDispersionPackage (data : SingleMagnonDispersionData) : Prop :=
  data.chainLength > 0 ∧
  data.momentum = (2 * Real.pi * (data.modeNumber : ℝ)) / (data.chainLength : ℝ) ∧
  data.oneLoopEnergy =
    (1 / (2 * Real.pi ^ (2 : ℕ))) * Real.sin (data.momentum / 2) ^ (2 : ℕ)

/-- Assumed one-loop single-magnon quantization/dispersion package. -/
theorem single_magnon_dispersion_package
    (data : SingleMagnonDispersionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilitySingleMagnonDispersion
      (SingleMagnonDispersionPackage data)) :
    SingleMagnonDispersionPackage data := by
  exact h_phys

/-- Bethe-root data for the one-loop Heisenberg chain. -/
structure HeisenbergBetheRootsData where
  chainLength : ℕ
  magnonCount : ℕ
  betheRoot : Fin magnonCount → ℂ

/-- Heisenberg one-loop asymptotic Bethe-ansatz package:
root equations and cyclicity condition in Bethe-root variables. -/
def HeisenbergBetheRootsPackage (data : HeisenbergBetheRootsData) : Prop :=
  data.chainLength > 0 ∧
  (∀ k : Fin data.magnonCount,
    data.betheRoot k ≠ Complex.I / 2 ∧ data.betheRoot k ≠ -Complex.I / 2) ∧
  (∀ k : Fin data.magnonCount,
    ((data.betheRoot k + Complex.I / 2) / (data.betheRoot k - Complex.I / 2)) ^
        data.chainLength =
      Finset.prod (Finset.univ.erase k) (fun j =>
        (data.betheRoot k - data.betheRoot j + Complex.I) /
          (data.betheRoot k - data.betheRoot j - Complex.I))) ∧
  (∏ k : Fin data.magnonCount,
      (data.betheRoot k + Complex.I / 2) / (data.betheRoot k - Complex.I / 2)) = 1

/-- Assumed one-loop Heisenberg Bethe-root package. -/
theorem heisenberg_bethe_roots_package
    (data : HeisenbergBetheRootsData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityHeisenbergBetheRoots
      (HeisenbergBetheRootsPackage data)) :
    HeisenbergBetheRootsPackage data := by
  exact h_phys

/-- BMN/pp-wave kinematics map data from global AdS charges. -/
structure BmnPpWaveMapData where
  mu : ℝ
  adsRadius : ℝ
  deltaMinusJ : ℝ
  deltaPlusJ : ℝ
  pPlus : ℝ
  pMinus : ℝ

/-- BMN/pp-wave charge map package:
`P_+ = -mu (Delta-J)` and `P_- = -(Delta+J)/(2 mu R^2)`. -/
def BmnPpWaveMapPackage (data : BmnPpWaveMapData) : Prop :=
  data.mu > 0 ∧
  data.adsRadius > 0 ∧
  data.pPlus = -data.mu * data.deltaMinusJ ∧
  data.pMinus = -data.deltaPlusJ / (2 * data.mu * data.adsRadius ^ (2 : ℕ))

/-- Assumed BMN/pp-wave lightcone-charge map package. -/
theorem bmn_pp_wave_map_package
    (data : BmnPpWaveMapData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityBmnPpWaveMap
      (BmnPpWaveMapPackage data)) :
    BmnPpWaveMapPackage data := by
  exact h_phys

/-- Lightcone pp-wave oscillator-spectrum data. -/
structure PpWaveSpectrumData where
  modeCount : ℕ
  modeNumber : Fin modeCount → ℤ
  occupationNumber : Fin modeCount → ℕ
  mu : ℝ
  alphaPrimePplus : ℝ
  modeFrequency : Fin modeCount → ℝ
  pMinus : ℝ
  levelMatchingCharge : ℤ

/-- Lightcone pp-wave spectrum package:
`omega_n = sqrt(mu^2 + n^2/(alpha' p^+)^2)`,
`p^- = sum_n N_n omega_n`, and level matching `sum_n n N_n = 0`. -/
def PpWaveSpectrumPackage (data : PpWaveSpectrumData) : Prop :=
  data.mu > 0 ∧
  data.alphaPrimePplus > 0 ∧
  (∀ i : Fin data.modeCount,
    data.modeFrequency i =
      Real.sqrt
        (data.mu ^ (2 : ℕ) +
          ((data.modeNumber i : ℝ) ^ (2 : ℕ)) / data.alphaPrimePplus ^ (2 : ℕ))) ∧
  data.pMinus =
    ∑ i : Fin data.modeCount, (data.occupationNumber i : ℝ) * data.modeFrequency i ∧
  data.levelMatchingCharge =
    ∑ i : Fin data.modeCount, data.modeNumber i * (data.occupationNumber i : ℤ) ∧
  data.levelMatchingCharge = 0

/-- Assumed pp-wave lightcone oscillator-spectrum package. -/
theorem pp_wave_spectrum_package
    (data : PpWaveSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityPpWaveSpectrum
      (PpWaveSpectrumPackage data)) :
    PpWaveSpectrumPackage data := by
  exact h_phys

/-- Magnon data for centrally extended `su(2|2)` kinematics. -/
structure CentrallyExtendedMagnonData where
  momentum : ℝ
  interpolatingCoupling : ℝ
  excitationEnergy : ℝ

/-- All-order magnon dispersion package:
`E(p) = sqrt(1 + 16 h(lambda)^2 sin^2(p/2))`. -/
def CentrallyExtendedMagnonDispersion (data : CentrallyExtendedMagnonData) : Prop :=
  data.interpolatingCoupling ≥ 0 ∧
  data.excitationEnergy =
    Real.sqrt
      (1 +
        16 * data.interpolatingCoupling ^ (2 : ℕ) *
          Real.sin (data.momentum / 2) ^ (2 : ℕ))

/-- Assumed centrally-extended all-order magnon dispersion package. -/
theorem centrally_extended_magnon_dispersion
    (data : CentrallyExtendedMagnonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityMagnonDispersion
      (CentrallyExtendedMagnonDispersion data)) :
    CentrallyExtendedMagnonDispersion data := by
  exact h_phys

/-- Weak-coupling map data for `h(lambda)`. -/
structure WeakCouplingInterpolatingMapData where
  tHooftCoupling : ℝ
  interpolatingCoupling : ℝ

/-- Weak-coupling matching package:
`h(lambda) = sqrt(lambda)/(4 pi)` in the one-loop normalization. -/
def WeakCouplingInterpolatingMapPackage
    (data : WeakCouplingInterpolatingMapData) : Prop :=
  data.tHooftCoupling ≥ 0 ∧
  data.interpolatingCoupling = Real.sqrt data.tHooftCoupling / (4 * Real.pi)

/-- Assumed weak-coupling matching of the magnon interpolating coupling. -/
theorem weak_coupling_interpolating_map_package
    (data : WeakCouplingInterpolatingMapData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityWeakCouplingMap
      (WeakCouplingInterpolatingMapPackage data)) :
    WeakCouplingInterpolatingMapPackage data := by
  exact h_phys

/-- Zhukovsky-variable data for magnon kinematics. -/
structure ZhukovskyVariablesData where
  momentum : ℝ
  interpolatingCoupling : ℝ
  xPlus : ℂ
  xMinus : ℂ

/-- Zhukovsky-kinematics package:
`x^+/x^- = e^{ip}` and
`x^+ + 1/x^+ - x^- - 1/x^- = i/h(lambda)`. -/
def ZhukovskyVariablesPackage (data : ZhukovskyVariablesData) : Prop :=
  data.interpolatingCoupling > 0 ∧
  data.xPlus ≠ 0 ∧
  data.xMinus ≠ 0 ∧
  data.xPlus / data.xMinus = Complex.exp (Complex.I * (data.momentum : ℂ)) ∧
  data.xPlus + 1 / data.xPlus - data.xMinus - 1 / data.xMinus =
    Complex.I / (data.interpolatingCoupling : ℂ)

/-- Assumed Zhukovsky-variable package for integrable magnon kinematics. -/
theorem zhukovsky_variables_package
    (data : ZhukovskyVariablesData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityZhukovskyVariables
      (ZhukovskyVariablesPackage data)) :
    ZhukovskyVariablesPackage data := by
  exact h_phys

/-- Scalar-factor consistency data for magnon two-body scattering. -/
structure MagnonSMatrixConsistencyData where
  scalarFactor12 : ℂ
  scalarFactor21 : ℂ
  scalarFactorCrossed12 : ℂ
  crossingKernel : ℂ

/-- Scalar-factor consistency package:
analytic unitarity `S12 S21 = 1` and crossing equation
`S12 S_{bar 1 2} = crossingKernel`. -/
def MagnonSMatrixConsistencyPackage (data : MagnonSMatrixConsistencyData) : Prop :=
  data.scalarFactor12 * data.scalarFactor21 = 1 ∧
  data.scalarFactor12 * data.scalarFactorCrossed12 = data.crossingKernel

/-- Assumed magnon scalar-factor unitarity/crossing package. -/
theorem magnon_s_matrix_consistency_package
    (data : MagnonSMatrixConsistencyData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilitySMatrixConsistency
      (MagnonSMatrixConsistencyPackage data)) :
    MagnonSMatrixConsistencyPackage data := by
  exact h_phys

/-- Cusp-anomalous-dimension data in the BES/ABA framework. -/
structure CuspAnomalousDimensionData where
  interpolatingCoupling : ℝ
  besIntegralValue : ℝ
  cuspAnomalousDimension : ℝ

/-- BES/ABA cusp package:
`Gamma_cusp = 4 h^2 (1 + 4 h Int_BES)`. -/
def CuspAnomalousDimensionPackage (data : CuspAnomalousDimensionData) : Prop :=
  data.interpolatingCoupling ≥ 0 ∧
  data.cuspAnomalousDimension =
    4 * data.interpolatingCoupling ^ (2 : ℕ) *
      (1 + 4 * data.interpolatingCoupling * data.besIntegralValue)

/-- Assumed BES/ABA cusp-anomalous-dimension package. -/
theorem cusp_anomalous_dimension_package
    (data : CuspAnomalousDimensionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityCuspBesEquation
      (CuspAnomalousDimensionPackage data)) :
    CuspAnomalousDimensionPackage data := by
  exact h_phys

/-- Strong-coupling asymptotic data for the cusp anomalous dimension. -/
structure CuspStrongCouplingData where
  interpolatingCoupling : ℝ
  cuspAnomalousDimension : ℝ
  subleadingRemainder : ℝ

/-- Strong-coupling cusp package:
`Gamma_cusp = 2 h - (3 log 2)/(2 pi) + O(1/h)`,
represented with an explicit remainder term. -/
def CuspStrongCouplingPackage (data : CuspStrongCouplingData) : Prop :=
  data.interpolatingCoupling > 0 ∧
  data.cuspAnomalousDimension =
    2 * data.interpolatingCoupling -
      (3 * Real.log 2) / (2 * Real.pi) + data.subleadingRemainder

/-- Assumed strong-coupling cusp-anomalous-dimension asymptotic package. -/
theorem cusp_strong_coupling_package
    (data : CuspStrongCouplingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityCuspStrongCoupling
      (CuspStrongCouplingPackage data)) :
    CuspStrongCouplingPackage data := by
  exact h_phys

/-- Bethe-Yang data for factorized nested scattering on a periodic chain. -/
structure BetheYangSystemData where
  chainLength : ℕ
  levelICount : ℕ
  momentum : Fin levelICount → ℝ
  levelIScatteringFactor : Fin levelICount → Fin levelICount → ℂ
  levelIILevelIIIFactor : Fin levelICount → ℂ
  transferEigenvalue : Fin levelICount → ℂ

/-- Bethe-Yang package:
`e^{i p_k L}` matches factorized level-I and nested level-II/III scattering factors. -/
def BetheYangSystemPackage (data : BetheYangSystemData) : Prop :=
  data.chainLength > 0 ∧
  ∀ k : Fin data.levelICount,
    data.transferEigenvalue k =
        Complex.exp (Complex.I * (data.momentum k : ℂ) * (data.chainLength : ℂ)) ∧
      data.transferEigenvalue k =
        (Finset.prod (Finset.univ.erase k) (fun j => data.levelIScatteringFactor j k)) *
          data.levelIILevelIIIFactor k

/-- Assumed nested Bethe-Yang factorization package. -/
theorem bethe_yang_system_package
    (data : BetheYangSystemData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityBetheYangSystem
      (BetheYangSystemPackage data)) :
    BetheYangSystemPackage data := by
  exact h_phys

/-- Bound-state magnon data. -/
structure BoundStateDispersionData where
  boundCharge : ℕ
  momentum : ℝ
  interpolatingCoupling : ℝ
  boundStateEnergy : ℝ

/-- Bound-state dispersion package:
for a `Q`-particle, `E = sqrt(Q^2 + 16 h(lambda)^2 sin^2(p/2))`. -/
def BoundStateDispersionPackage (data : BoundStateDispersionData) : Prop :=
  data.boundCharge > 0 ∧
  data.interpolatingCoupling ≥ 0 ∧
  data.boundStateEnergy =
    Real.sqrt
      ((data.boundCharge : ℝ) ^ (2 : ℕ) +
        16 * data.interpolatingCoupling ^ (2 : ℕ) *
          Real.sin (data.momentum / 2) ^ (2 : ℕ))

/-- Assumed bound-state magnon dispersion package. -/
theorem bound_state_dispersion_package
    (data : BoundStateDispersionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS5IntegrabilityBoundStateDispersion
      (BoundStateDispersionPackage data)) :
    BoundStateDispersionPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
