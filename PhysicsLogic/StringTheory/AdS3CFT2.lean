import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Internal compact space choice for the D1-D5 system. -/
inductive D1D5InternalSpace where
  | t4
  | k3
  deriving DecidableEq, Repr

/-- D1/D5 charge and instanton-number data. -/
structure D1D5InstantonChargeData where
  q1 : ℕ
  q5 : ℕ
  instantonNumber : ℕ
  internalSpace : D1D5InternalSpace

/-- Instanton-number/charge map:
`n = Q1` for `T^4`, `n = Q1 + Q5` for K3. -/
def D1D5InstantonChargeMap (data : D1D5InstantonChargeData) : Prop :=
  data.q1 > 0 ∧
  data.q5 > 0 ∧
  match data.internalSpace with
  | .t4 => data.instantonNumber = data.q1
  | .k3 => data.instantonNumber = data.q1 + data.q5

/-- Assumed D1/D5 instanton-number mapping for `T^4` and K3 compactifications. -/
theorem d1_d5_instanton_charge_map
    (data : D1D5InstantonChargeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5InstantonChargeMap
      (D1D5InstantonChargeMap data)) :
    D1D5InstantonChargeMap data := by
  exact h_phys

/-- Low-energy branch-structure data for the 2D `(4,4)` D1-D5 gauge theory. -/
structure D1D5BranchStructureData where
  fiDeformationScale : ℝ
  coulombBranchLifted : Bool
  higgsBranchTag : String
  adhmTag : String

/-- Branch-structure package:
FI deformation lifts the Coulomb branch and Higgs branch matches ADHM data. -/
def D1D5BranchStructurePackage (data : D1D5BranchStructureData) : Prop :=
  data.higgsBranchTag = "Higgs branch from D-term quotient" ∧
  data.adhmTag = "ADHM instanton moduli space" ∧
  (data.fiDeformationScale > 0 → data.coulombBranchLifted = true)

/-- Assumed D1-D5 branch-structure package with FI-induced lifting of Coulomb branch. -/
theorem d1_d5_branch_structure_package
    (data : D1D5BranchStructureData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5BranchStructure
      (D1D5BranchStructurePackage data)) :
    D1D5BranchStructurePackage data := by
  exact h_phys

/-- Dimension data for the D1-D5 Higgs-branch instanton moduli space. -/
structure D1D5InstantonModuliDimensionData where
  q1 : ℕ
  q5 : ℕ
  internalSpace : D1D5InternalSpace
  moduliDimension : ℕ

/-- Instanton-moduli dimension package:
`dim = 4 Q1 Q5` for `T^4`, `dim = 4 (Q1 Q5 + 1)` for K3. -/
def D1D5InstantonModuliDimensionPackage
    (data : D1D5InstantonModuliDimensionData) : Prop :=
  data.q1 > 0 ∧
  data.q5 > 0 ∧
  match data.internalSpace with
  | .t4 => data.moduliDimension = 4 * data.q1 * data.q5
  | .k3 => data.moduliDimension = 4 * (data.q1 * data.q5 + 1)

/-- Assumed D1-D5 instanton-moduli dimension relation. -/
theorem d1_d5_instanton_moduli_dimension_package
    (data : D1D5InstantonModuliDimensionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5InstantonModuliDimension
      (D1D5InstantonModuliDimensionPackage data)) :
    D1D5InstantonModuliDimensionPackage data := by
  exact h_phys

/-- Near-horizon geometric parameter data for the D1-D5 black-brane system. -/
structure D1D5NearHorizonData where
  stringCoupling : ℝ
  alphaPrime : ℝ
  m4Volume : ℝ
  q1 : ℕ
  q5 : ℕ
  r1Sq : ℝ
  r5Sq : ℝ
  geometryTag : String
  fluxTag : String

/-- D1-D5 near-horizon package:
`R1^2 = g Q1 α' (2π sqrt(α'))^4 / V4`, `R5^2 = g Q5 α'`, and
near-horizon geometry `AdS3 x S3 x M4`. -/
def D1D5NearHorizonPackage (data : D1D5NearHorizonData) : Prop :=
  data.stringCoupling > 0 ∧
  data.alphaPrime > 0 ∧
  data.m4Volume > 0 ∧
  data.q1 > 0 ∧
  data.q5 > 0 ∧
  data.r1Sq =
    data.stringCoupling * (data.q1 : ℝ) * data.alphaPrime *
      ((2 * Real.pi * Real.sqrt data.alphaPrime) ^ (4 : ℕ) / data.m4Volume) ∧
  data.r5Sq = data.stringCoupling * (data.q5 : ℝ) * data.alphaPrime ∧
  data.geometryTag = "AdS_3 x S^3 x M_4" ∧
  data.fluxTag = "F3 and dual F7 flux quantized by (Q5,Q1)"

/-- Assumed D1-D5 near-horizon/decoupling package. -/
theorem d1_d5_near_horizon_package
    (data : D1D5NearHorizonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5NearHorizonGeometry
      (D1D5NearHorizonPackage data)) :
    D1D5NearHorizonPackage data := by
  exact h_phys

/-- Brown-Henneaux central-charge data for the D1-D5 AdS3 dual pair. -/
structure D1D5CentralChargeData where
  q1 : ℕ
  q5 : ℕ
  centralCharge : ℝ

/-- Central-charge package:
`c = 6 Q1 Q5`. -/
def D1D5CentralChargePackage (data : D1D5CentralChargeData) : Prop :=
  data.q1 > 0 ∧
  data.q5 > 0 ∧
  data.centralCharge = 6 * (data.q1 : ℝ) * (data.q5 : ℝ)

/-- Assumed Brown-Henneaux/D1-D5 central-charge relation. -/
theorem d1_d5_central_charge_package
    (data : D1D5CentralChargeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5CentralCharge
      (D1D5CentralChargePackage data)) :
    D1D5CentralChargePackage data := by
  exact h_phys

/-- Conformal-manifold/U-duality data for D1-D5 CFT moduli. -/
structure D1D5ConformalManifoldData where
  q1 : ℕ
  q5 : ℕ
  gcdCharge : ℕ
  invariantK : ℕ
  tau : ℂ
  tauTilde : ℂ
  moduliSpaceTag : String
  dualityGroupTag : String

/-- Conformal-manifold/U-duality package:
`Q1 Q5 = k (gcd(Q1,Q5))^2`, attractor `τ~ = (Q1/Q5) τ`,
and moduli-space/coset tags. -/
def D1D5ConformalManifoldPackage (data : D1D5ConformalManifoldData) : Prop :=
  data.q1 > 0 ∧
  data.q5 > 0 ∧
  data.gcdCharge = Nat.gcd data.q1 data.q5 ∧
  data.invariantK * data.gcdCharge ^ (2 : ℕ) = data.q1 * data.q5 ∧
  data.tauTilde = ((data.q1 : ℂ) / (data.q5 : ℂ)) * data.tau ∧
  data.moduliSpaceTag = "H_{Q1,Q5}\\SO(5,4)/(SO(5)xSO(4))" ∧
  data.dualityGroupTag = "Gamma0(k1k5) subgroup action on tau"

/-- Assumed D1-D5 conformal-manifold/U-duality package. -/
theorem d1_d5_conformal_manifold_package
    (data : D1D5ConformalManifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5ConformalManifoldUduality
      (D1D5ConformalManifoldPackage data)) :
    D1D5ConformalManifoldPackage data := by
  exact h_phys

/-- Symmetric-product orbifold locus data in the D1-D5 conformal manifold. -/
structure D1D5SymmetricOrbifoldData where
  q1 : ℕ
  q5 : ℕ
  fiDeformationScale : ℝ
  orbifoldTag : String
  parityLocusTag : String
  coulombBranchLifted : Bool

/-- Symmetric-orbifold package:
`Sym^(Q1 Q5)(T^4)` locus and FI deformation lifting of the Coulomb branch. -/
def D1D5SymmetricOrbifoldPackage (data : D1D5SymmetricOrbifoldData) : Prop :=
  data.q1 > 0 ∧
  data.q5 > 0 ∧
  data.orbifoldTag = "Sym^(Q1 Q5)(T^4)" ∧
  data.parityLocusTag = "Re(tau)=1/2 orbifold-symmetric locus" ∧
  (data.fiDeformationScale > 0 → data.coulombBranchLifted = true)

/-- Assumed symmetric-product orbifold/FI-lift package for D1-D5 CFT. -/
theorem d1_d5_symmetric_orbifold_package
    (data : D1D5SymmetricOrbifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3D1D5SymmetricOrbifoldLocus
      (D1D5SymmetricOrbifoldPackage data)) :
    D1D5SymmetricOrbifoldPackage data := by
  exact h_phys

/-- Bosonic AdS3 WZW parameter data. -/
structure AdS3BosonicWZWData where
  radius : ℝ
  alphaPrime : ℝ
  levelK : ℝ

/-- Bosonic AdS3 WZW level/radius relation:
`k = R^2/α'`. -/
def AdS3BosonicWZWLevelRadiusRelation (data : AdS3BosonicWZWData) : Prop :=
  data.radius > 0 ∧
  data.alphaPrime > 0 ∧
  data.levelK = data.radius ^ (2 : ℕ) / data.alphaPrime

/-- Assumed bosonic AdS3 WZW level/radius relation. -/
theorem ads3_bosonic_wzw_level_radius_relation
    (data : AdS3BosonicWZWData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3BosonicWzwLevelRadius
      (AdS3BosonicWZWLevelRadiusRelation data)) :
    AdS3BosonicWZWLevelRadiusRelation data := by
  exact h_phys

/-- Bosonic `SL(2,R)` spectral-flow data. -/
structure AdS3BosonicSpectralFlowData where
  levelK : ℝ
  flowW : ℤ
  j3Mode : ℤ → ℝ
  virasoroMode : ℤ → ℝ
  flowedJ3Mode : ℤ → ℝ
  flowedVirasoroMode : ℤ → ℝ

/-- Spectral-flow automorphism package:
`J_n^3 -> J_n^3 - (k/2) w δ_{n,0}`,
`L_n -> L_n + w J_n^3 - (k/4) w^2 δ_{n,0}`. -/
def AdS3BosonicSpectralFlowPackage (data : AdS3BosonicSpectralFlowData) : Prop :=
  data.levelK > 2 ∧
  (∀ n : ℤ,
    data.flowedJ3Mode n =
      data.j3Mode n -
        (data.levelK / 2) * (data.flowW : ℝ) * (if n = 0 then 1 else 0)) ∧
  (∀ n : ℤ,
    data.flowedVirasoroMode n =
      data.virasoroMode n + (data.flowW : ℝ) * data.j3Mode n -
        (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : ℕ) * (if n = 0 then 1 else 0))

/-- Assumed bosonic AdS3 spectral-flow automorphism package. -/
theorem ads3_bosonic_spectral_flow_package
    (data : AdS3BosonicSpectralFlowData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3BosonicSpectralFlow
      (AdS3BosonicSpectralFlowPackage data)) :
    AdS3BosonicSpectralFlowPackage data := by
  exact h_phys

/-- AdS3 bosonic-string representation-space data. -/
structure AdS3BosonicPhysicalSpectrumData where
  levelK : ℝ
  jDiscrete : ℝ
  jContinuousRealPart : ℝ
  continuousParameter : ℝ
  discreteTag : String
  continuousTag : String

/-- Allowed representation package:
discrete `1/2 < j < (k-1)/2`, continuous `j = 1/2 + i s`,
with spectral-flowed sectors included. -/
def AdS3BosonicPhysicalSpectrumPackage
    (data : AdS3BosonicPhysicalSpectrumData) : Prop :=
  data.levelK > 2 ∧
  (1 : ℝ) / 2 < data.jDiscrete ∧
  data.jDiscrete < (data.levelK - 1) / 2 ∧
  data.jContinuousRealPart = (1 : ℝ) / 2 ∧
  data.continuousParameter ≥ 0 ∧
  data.discreteTag = "D_j^(±,w) with j in (1/2,(k-1)/2)" ∧
  data.continuousTag = "C_(1/2+is)^(alpha,w)"

/-- Assumed bosonic AdS3 physical-spectrum representation package. -/
theorem ads3_bosonic_physical_spectrum_package
    (data : AdS3BosonicPhysicalSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3BosonicPhysicalSpectrum
      (AdS3BosonicPhysicalSpectrumPackage data)) :
    AdS3BosonicPhysicalSpectrumPackage data := by
  exact h_phys

/-- Bosonic AdS3 string mass-shell/spacetime-energy data. -/
structure AdS3BosonicMassShellData where
  levelK : ℝ
  spinJ : ℝ
  mQuantum : ℝ
  flowW : ℤ
  currentDescendantLevel : ℝ
  virasoroDescendantLevel : ℝ
  internalWeight : ℝ
  j0Three : ℝ

/-- Bosonic AdS3 mass-shell package:
`-j(j-1)/(k-2) - w m - k w^2/4 + N + l + h - 1 = 0`,
`J_0^3 = m + k w/2`. -/
def AdS3BosonicMassShellPackage (data : AdS3BosonicMassShellData) : Prop :=
  data.levelK > 2 ∧
  data.currentDescendantLevel ≥ 0 ∧
  data.virasoroDescendantLevel ≥ 0 ∧
  data.j0Three = data.mQuantum + (data.levelK / 2) * (data.flowW : ℝ) ∧
  -(data.spinJ * (data.spinJ - 1)) / (data.levelK - 2) -
      (data.flowW : ℝ) * data.mQuantum -
      (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : ℕ) +
      data.currentDescendantLevel + data.virasoroDescendantLevel + data.internalWeight - 1 = 0

/-- Assumed bosonic AdS3 mass-shell/energy package. -/
theorem ads3_bosonic_mass_shell_package
    (data : AdS3BosonicMassShellData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3BosonicMassShell
      (AdS3BosonicMassShellPackage data)) :
    AdS3BosonicMassShellPackage data := by
  exact h_phys

/-- Purely `(NS,NS)` AdS3xS3xM4 superstring background data. -/
structure AdS3NSNSSuperstringBackgroundData where
  levelK : ℝ
  radius : ℝ
  alphaPrime : ℝ
  matterCentralCharge : ℝ
  worldsheetTag : String

/-- NSNS superstring worldsheet package:
`R^2 = k α'`, worldsheet SCFT
`hatSL(2)_k x hatSU(2)_k x M4`, and `c=15`. -/
def AdS3NSNSSuperstringBackgroundPackage
    (data : AdS3NSNSSuperstringBackgroundData) : Prop :=
  data.levelK > 0 ∧
  data.radius > 0 ∧
  data.alphaPrime > 0 ∧
  data.radius ^ (2 : ℕ) = data.levelK * data.alphaPrime ∧
  data.worldsheetTag = "hatSL(2)_k x hatSU(2)_k x M_4" ∧
  data.matterCentralCharge = 15

/-- Assumed purely-NSNS AdS3 superstring worldsheet package. -/
theorem ads3_nsns_superstring_background_package
    (data : AdS3NSNSSuperstringBackgroundData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3NsnsSuperstringWorldsheet
      (AdS3NSNSSuperstringBackgroundPackage data)) :
    AdS3NSNSSuperstringBackgroundPackage data := by
  exact h_phys

/-- `(NS,NS)` AdS3 superstring mass-shell/BPS data. -/
structure AdS3NSNSSuperstringMassShellData where
  levelK : ℝ
  spinJ : ℝ
  mQuantum : ℝ
  flowW : ℤ
  adsDescendantLevel : ℝ
  suDescendantLevel : ℝ
  internalWeight : ℝ
  suSpin : ℝ
  j0Three : ℝ

/-- NSNS mass-shell package in the AdS3 sector:
`-j(j-1)/k - w m - k w^2/4 + N + N' + h_int = 1/2`,
`J_0^3 = m + k w/2`, and BPS lower bound `J_0^3 >= j' + h_int`. -/
def AdS3NSNSSuperstringMassShellPackage
    (data : AdS3NSNSSuperstringMassShellData) : Prop :=
  data.levelK > 0 ∧
  data.adsDescendantLevel ≥ 0 ∧
  data.suDescendantLevel ≥ 0 ∧
  data.internalWeight ≥ 0 ∧
  data.j0Three = data.mQuantum + (data.levelK / 2) * (data.flowW : ℝ) ∧
  -(data.spinJ * (data.spinJ - 1)) / data.levelK -
      (data.flowW : ℝ) * data.mQuantum -
      (data.levelK / 4) * (data.flowW : ℝ) ^ (2 : ℕ) +
      data.adsDescendantLevel + data.suDescendantLevel + data.internalWeight = (1 : ℝ) / 2 ∧
  data.j0Three ≥ data.suSpin + data.internalWeight

/-- Assumed NSNS AdS3 superstring mass-shell/BPS package. -/
theorem ads3_nsns_superstring_mass_shell_package
    (data : AdS3NSNSSuperstringMassShellData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3NsnsSuperstringMassShell
      (AdS3NSNSSuperstringMassShellPackage data)) :
    AdS3NSNSSuperstringMassShellPackage data := by
  exact h_phys

/-- Mixed `(NS,NS)`/`(R,R)` flux parameterization data in AdS3xS3xM4. -/
structure AdS3MixedFluxData where
  stringCoupling : ℝ
  alphaPrime : ℝ
  nsFluxK5 : ℕ
  rrFluxQ5 : ℕ
  radius : ℝ
  mu : ℝ

/-- Mixed-flux package:
`R^2 = α' sqrt(K5^2 + g_B^2 Q5^2)`,
`mu = g_B Q5 / K5`. -/
def AdS3MixedFluxPackage (data : AdS3MixedFluxData) : Prop :=
  data.stringCoupling > 0 ∧
  data.alphaPrime > 0 ∧
  data.nsFluxK5 > 0 ∧
  data.radius > 0 ∧
  data.radius ^ (2 : ℕ) =
    data.alphaPrime *
      Real.sqrt
        ((data.nsFluxK5 : ℝ) ^ (2 : ℕ) +
          (data.stringCoupling * (data.rrFluxQ5 : ℝ)) ^ (2 : ℕ)) ∧
  data.mu = data.stringCoupling * (data.rrFluxQ5 : ℝ) / (data.nsFluxK5 : ℝ)

/-- Assumed AdS3 mixed-flux parameterization package. -/
theorem ads3_mixed_flux_package
    (data : AdS3MixedFluxData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxParameterization
      (AdS3MixedFluxPackage data)) :
    AdS3MixedFluxPackage data := by
  exact h_phys

/-- Circular pulsating-string energy-shift data at small mixed-flux parameter `mu`. -/
structure AdS3MixedFluxPulsatingData where
  n : ℝ
  k : ℝ
  mu : ℝ
  delta : ℝ

/-- Semi-classical pulsating-string small-`mu` expansion package:
`Delta = -2n + 2sqrt(nk) + mu^2 * (...)` up to order `mu^2`. -/
def AdS3MixedFluxPulsatingPackage (data : AdS3MixedFluxPulsatingData) : Prop :=
  data.n > 0 ∧
  data.k > 0 ∧
  data.mu ≥ 0 ∧
  data.delta =
    -2 * data.n + 2 * Real.sqrt (data.n * data.k) +
      data.mu ^ (2 : ℕ) *
        (Real.sqrt (data.n * data.k) / 2 +
          (2 * data.n * data.k - 3 * data.n * Real.sqrt (data.n * data.k)) /
            (2 * (2 * Real.sqrt data.n - Real.sqrt data.k) ^ (2 : ℕ)))

/-- Assumed small-`mu` mixed-flux correction package for circular pulsating strings. -/
theorem ads3_mixed_flux_pulsating_package
    (data : AdS3MixedFluxPulsatingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxPulsatingShift
      (AdS3MixedFluxPulsatingPackage data)) :
    AdS3MixedFluxPulsatingPackage data := by
  exact h_phys

/-- RR-deformation SFT recursion data in mixed-flux AdS3xS3xM4 backgrounds. -/
structure AdS3MixedFluxSftRrDeformationData where
  mu : ℝ
  levelK : ℝ
  firstOrderRrVertexUsed : Bool
  projectedTwoStringBracketVanishesAtFiniteK : Bool
  secondOrderFieldSetToZero : Bool
  secondOrderCorrectionUsesSiegelResolvent : Bool
  secondOrderEquationCoefficient : ℝ
  largeKNormalizationMatchingUsed : Bool

/-- Mixed-flux RR-deformation SFT package:
`Q_B W^(2) = -(1/2) P^+[W^(1)⊗W^(1)]`, finite-`k` vanishing of projected
two-string bracket, and resulting order-`mu^2` Siegel-resolvent correction. -/
def AdS3MixedFluxSftRrDeformationPackage
    (data : AdS3MixedFluxSftRrDeformationData) : Prop :=
  data.mu >= 0 ∧
  data.levelK > 0 ∧
  data.firstOrderRrVertexUsed = true ∧
  data.projectedTwoStringBracketVanishesAtFiniteK = true ∧
  data.secondOrderFieldSetToZero = true ∧
  data.secondOrderCorrectionUsesSiegelResolvent = true ∧
  data.secondOrderEquationCoefficient = (-(1 / 2 : ℝ)) ∧
  data.largeKNormalizationMatchingUsed = true

/-- Assumed mixed-flux RR-deformation SFT package. -/
theorem ads3_mixed_flux_sft_rr_deformation_package
    (data : AdS3MixedFluxSftRrDeformationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxSftRrDeformation
      (AdS3MixedFluxSftRrDeformationPackage data)) :
    AdS3MixedFluxSftRrDeformationPackage data := by
  exact h_phys

/-- RR-deformation mass-shift data from four-string amplitudes in mixed-flux AdS3. -/
structure AdS3MixedFluxMassShiftFromFourPointData where
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
`delta m^2|_{mu^2} = mu^2 A_(0,4) / alpha'`, with no-zero-weight intermediate
states in the relevant nested brackets. -/
def AdS3MixedFluxMassShiftFromFourPointPackage
    (data : AdS3MixedFluxMassShiftFromFourPointData) : Prop :=
  data.mu >= 0 ∧
  data.alphaPrime > 0 ∧
  data.noZeroWeightInWOneBracket = true ∧
  data.noZeroWeightInNestedBracket = true ∧
  data.scalingDimensionMu =
    data.scalingDimensionZero - (data.alphaPrime / 2) * data.massSquaredShift ∧
  data.massSquaredShift =
    data.mu ^ (2 : Nat) * data.fourPointAmplitude / data.alphaPrime

/-- Assumed mixed-flux RR-deformation mass-shift package from four-point amplitudes. -/
theorem ads3_mixed_flux_mass_shift_from_four_point_package
    (data : AdS3MixedFluxMassShiftFromFourPointData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxMassShiftFromFourPoint
      (AdS3MixedFluxMassShiftFromFourPointPackage data)) :
    AdS3MixedFluxMassShiftFromFourPointPackage data := by
  exact h_phys

/-- Finite-`k` WZW four-point-reduction data for mixed-flux AdS3 RR-deformation shifts. -/
structure AdS3MixedFluxFiniteKWzwFourPointReductionData where
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

/-- Finite-`k` mixed-flux WZW reduction package:
the RR-deformation mass-shift equation reduces to bosonic
`SL(2)_{k+2}`/`SU(2)_{k-2}` four-point functions involving a pair of
fundamental primaries and a pair of generic primaries, with large-`k`
(`n/k` fixed) agreement with semiclassical pulsating-string shifts. -/
def AdS3MixedFluxFiniteKWzwFourPointReductionPackage
    (data : AdS3MixedFluxFiniteKWzwFourPointReductionData) : Prop :=
  data.levelK > 2 ∧
  data.mu >= 0 ∧
  data.slBosonicLevel = data.levelK + 2 ∧
  data.suBosonicLevel = data.levelK - 2 ∧
  data.usesSlFundamentalPair = true ∧
  data.usesSuFundamentalPair = true ∧
  data.usesSlGenericPair = true ∧
  data.usesSuGenericPair = true ∧
  data.reductionToSlFourPointFunctions = true ∧
  data.reductionToSuFourPointFunctions = true ∧
  data.largeKFiniteNOverKAgreementWithSemiclassical = true

/-- Assumed finite-`k` WZW four-point-reduction package for mixed-flux AdS3. -/
theorem ads3_mixed_flux_finite_k_wzw_four_point_reduction_package
    (data : AdS3MixedFluxFiniteKWzwFourPointReductionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxFiniteKWzwFourPointReduction
      (AdS3MixedFluxFiniteKWzwFourPointReductionPackage data)) :
    AdS3MixedFluxFiniteKWzwFourPointReductionPackage data := by
  exact h_phys

/-- Finite-`k` WZW OPE-constant normalization data for mixed-flux AdS3 RR deformation. -/
structure AdS3MixedFluxWzwOpeStructureConstantData where
  levelK : ℝ
  cSuHalfHalfOne : ℝ
  cSlMinusHalfMinusHalfMinusOne : ℝ
  suIdentityOpeCoefficient : ℝ
  slIdentityOpeCoefficient : ℝ
  cSuLargeKAsymptoticValue : ℝ
  cSlLargeKAsymptoticValue : ℝ

/-- Finite-`k` WZW OPE-constant package:
identity coefficients normalized to `1`,
`C^sl_{-1/2,-1/2,-1} = (4/3)/C^su_{1/2,1/2,1}`,
and shared large-`k` asymptotic value `2/sqrt(3)`. -/
def AdS3MixedFluxWzwOpeStructureConstantPackage
    (data : AdS3MixedFluxWzwOpeStructureConstantData) : Prop :=
  data.levelK > 3 ∧
  data.suIdentityOpeCoefficient = 1 ∧
  data.slIdentityOpeCoefficient = 1 ∧
  data.cSuHalfHalfOne > 0 ∧
  data.cSlMinusHalfMinusHalfMinusOne > 0 ∧
  data.cSlMinusHalfMinusHalfMinusOne = (4 / 3 : ℝ) / data.cSuHalfHalfOne ∧
  data.cSuLargeKAsymptoticValue = 2 / Real.sqrt 3 ∧
  data.cSlLargeKAsymptoticValue = 2 / Real.sqrt 3

/-- Assumed finite-`k` WZW OPE-constant package for mixed-flux AdS3 RR deformation. -/
theorem ads3_mixed_flux_wzw_ope_structure_constant_package
    (data : AdS3MixedFluxWzwOpeStructureConstantData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxWzwOpeStructureConstants
      (AdS3MixedFluxWzwOpeStructureConstantPackage data)) :
    AdS3MixedFluxWzwOpeStructureConstantPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
