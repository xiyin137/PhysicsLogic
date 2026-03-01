import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Tree-level superstring data in the PCO contour formulation. -/
structure TreeLevelSuperstringPcoData where
  externalCount : ℕ
  nsPuncturesHolomorphic : ℕ
  ramondPairsHolomorphic : ℕ
  nsPuncturesAntiholomorphic : ℕ
  ramondPairsAntiholomorphic : ℕ
  holomorphicPcoCount : ℤ
  antiholomorphicPcoCount : ℤ
  normalizationPhase : ℂ
  contourIntegral : ℂ
  amplitude : ℂ

/-- Tree-level PCO package:
`d_o = n_NS + n_R/2 - 2` in each chiral sector and
`A_0 = i^(n-3) ∫_{S_{0,n}} \widetilde Ω`. -/
def TreeLevelSuperstringPcoPackage (data : TreeLevelSuperstringPcoData) : Prop :=
  data.holomorphicPcoCount =
    (data.nsPuncturesHolomorphic : ℤ) + (data.ramondPairsHolomorphic : ℤ) - 2 ∧
  data.antiholomorphicPcoCount =
    (data.nsPuncturesAntiholomorphic : ℤ) + (data.ramondPairsAntiholomorphic : ℤ) - 2 ∧
  data.normalizationPhase = Complex.I ^ (data.externalCount - 3) ∧
  data.amplitude = data.normalizationPhase * data.contourIntegral

/-- Assumed tree-level PCO-counting/amplitude package from Section 8.1. -/
theorem tree_level_superstring_pco_package
    (data : TreeLevelSuperstringPcoData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitTreeLevelPcoAmplitude
      (TreeLevelSuperstringPcoPackage data)) :
    TreeLevelSuperstringPcoPackage data := by
  exact h_phys

/-- Picture-raising and integrated-vertex conversion data for NS punctures. -/
structure NsnsPictureRaisingData where
  pcoCollisionLimit : ℂ
  localPictureRaisedVertex : ℂ
  integratedVertexAfterBGhosts : ℂ
  matterSuperdescendant : ℂ
  pcoCollisionRegular : Bool

/-- NS picture-raising package:
collision limit exists and `b_{-1}\tilde b_{-1} V^{(0,0)} = (1/4) G_{-1/2}\tilde G_{-1/2} V^m`. -/
def NsnsPictureRaisingPackage (data : NsnsPictureRaisingData) : Prop :=
  data.pcoCollisionRegular = true ∧
  data.localPictureRaisedVertex = data.pcoCollisionLimit ∧
  data.integratedVertexAfterBGhosts = (1 / 4 : ℂ) * data.matterSuperdescendant

/-- Assumed NS picture-raising package from Section 8.1. -/
theorem nsns_picture_raising_package
    (data : NsnsPictureRaisingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitNsnsPictureRaising
      (NsnsPictureRaisingPackage data)) :
    NsnsPictureRaisingPackage data := by
  exact h_phys

/-- Tree-level three-point NSNS/supergravity matching data. -/
structure NsnsThreePointSupergravityData where
  stringCoupling : ℝ
  gravitationalCoupling : ℝ
  worldsheetThreePointAmplitude : ℂ
  einsteinHilbertVertex : ℂ
  excludesR2R3AtTree : Bool

/-- Three-point NSNS package:
`κ = (π/2) g_s`, worldsheet three-point amplitude matches Einstein-Hilbert kinematics,
and no independent tree-level `R^2`/`R^3` correction survives on shell. -/
def NsnsThreePointSupergravityPackage
    (data : NsnsThreePointSupergravityData) : Prop :=
  data.stringCoupling > 0 ∧
  data.gravitationalCoupling = (Real.pi / 2) * data.stringCoupling ∧
  data.worldsheetThreePointAmplitude = data.einsteinHilbertVertex ∧
  data.excludesR2R3AtTree = true

/-- Assumed NSNS three-point supergravity-matching package from Section 8.1. -/
theorem nsns_three_point_supergravity_package
    (data : NsnsThreePointSupergravityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitNsnsThreePointSupergravity
      (NsnsThreePointSupergravityPackage data)) :
    NsnsThreePointSupergravityPackage data := by
  exact h_phys

/-- Tree-level four-point NSNS amplitude data. -/
structure NsnsFourPointTreeData where
  alphaPrime : ℝ
  stringCoupling : ℝ
  mandelstamS : ℝ
  mandelstamT : ℝ
  mandelstamU : ℝ
  nsKinematicTensor : ℂ
  gammaKernel : ℂ
  reducedAmplitude : ℂ

/-- Four-point NSNS tree package:
`s+t+u=0` for massless external states and
`A_0 ~ (-π^2 g_s^2 α'^3 / 16) K_NS * Γ-ratio`. -/
def NsnsFourPointTreePackage (data : NsnsFourPointTreeData) : Prop :=
  data.alphaPrime > 0 ∧
  data.stringCoupling > 0 ∧
  data.mandelstamS + data.mandelstamT + data.mandelstamU = 0 ∧
  data.reducedAmplitude =
    (((-(Real.pi ^ (2 : ℕ)) * data.stringCoupling ^ (2 : ℕ) *
        data.alphaPrime ^ (3 : ℕ) / 16 : ℝ) : ℂ) *
      data.nsKinematicTensor * data.gammaKernel)

/-- Assumed NSNS four-point tree kernel package from Section 8.1. -/
theorem nsns_four_point_tree_package
    (data : NsnsFourPointTreeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitNsnsFourPointTreeKernel
      (NsnsFourPointTreePackage data)) :
    NsnsFourPointTreePackage data := by
  exact h_phys

/-- Low-energy expansion data for the four-point gamma kernel. -/
structure FourPointLowEnergyExpansionData where
  alphaPrime : ℝ
  mandelstamS : ℝ
  mandelstamT : ℝ
  mandelstamU : ℝ
  zeta3Coefficient : ℝ
  gammaKernelLeadingPole : ℝ
  gammaKernelConstantTerm : ℝ
  oneLoopThresholdNonanalytic : Bool

/-- Low-energy expansion package:
leading supergravity pole term and the tree-level `ζ(3) α'^3 R^4` constant piece. -/
def FourPointLowEnergyExpansionPackage
    (data : FourPointLowEnergyExpansionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.mandelstamS + data.mandelstamT + data.mandelstamU = 0 ∧
  data.gammaKernelLeadingPole =
    -64 /
      (data.alphaPrime ^ (3 : ℕ) *
        data.mandelstamS * data.mandelstamT * data.mandelstamU) ∧
  data.gammaKernelConstantTerm = -2 * data.zeta3Coefficient ∧
  data.oneLoopThresholdNonanalytic = true

/-- Assumed low-energy gamma-kernel expansion package from Section 8.1/8.5. -/
theorem four_point_low_energy_expansion_package
    (data : FourPointLowEnergyExpansionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitFourPointLowEnergyExpansion
      (FourPointLowEnergyExpansionPackage data)) :
    FourPointLowEnergyExpansionPackage data := by
  exact h_phys

/-- Tree-level four-point RR amplitude data. -/
structure RrFourPointTreeData where
  alphaPrime : ℝ
  stringCoupling : ℝ
  mandelstamS : ℝ
  mandelstamT : ℝ
  mandelstamU : ℝ
  rrKinematicTensor : ℂ
  gammaKernel : ℂ
  reducedAmplitude : ℂ
  sphereFourRamondNeedsNoPco : Bool

/-- Four-point RR tree package:
for four Ramond punctures on the sphere no PCO insertion is needed, and
`A_0 ~ (-π^2 α' g_s^2) K_R * Γ-ratio`. -/
def RrFourPointTreePackage (data : RrFourPointTreeData) : Prop :=
  data.alphaPrime > 0 ∧
  data.stringCoupling > 0 ∧
  data.mandelstamS + data.mandelstamT + data.mandelstamU = 0 ∧
  data.sphereFourRamondNeedsNoPco = true ∧
  data.reducedAmplitude =
    (((-(Real.pi ^ (2 : ℕ)) * data.alphaPrime * data.stringCoupling ^ (2 : ℕ) : ℝ) : ℂ) *
      data.rrKinematicTensor * data.gammaKernel)

/-- Assumed RR four-point tree kernel package from Section 8.1. -/
theorem rr_four_point_tree_package
    (data : RrFourPointTreeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitRrFourPointTreeKernel
      (RrFourPointTreePackage data)) :
    RrFourPointTreePackage data := by
  exact h_phys

/-- Genus-one NSNS spin-structure and contour data. -/
structure OneLoopNsnsSpinStructureData where
  externalCount : ℕ
  contourDimension : ℤ
  spinStructurePrefactor : ℂ
  contourIntegral : ℂ
  oneLoopAmplitude : ℂ
  handlesZTwoRedundancy : Bool
  oddOddUsesSeparatedPco : Bool

/-- Genus-one NSNS contour package:
`dim S_{1,n,ε} = 2n`, amplitude prefactor `(i^n)/4`, plus the torus `Z_2` puncture
redundancy and odd-spin PCO-separation prescription. -/
def OneLoopNsnsSpinStructurePackage
    (data : OneLoopNsnsSpinStructureData) : Prop :=
  data.contourDimension = 2 * (data.externalCount : ℤ) ∧
  data.spinStructurePrefactor = (Complex.I ^ data.externalCount) / 4 ∧
  data.oneLoopAmplitude = data.spinStructurePrefactor * data.contourIntegral ∧
  data.handlesZTwoRedundancy = true ∧
  data.oddOddUsesSeparatedPco = true

/-- Assumed one-loop NSNS spin-structure contour package from Section 8.2. -/
theorem one_loop_nsns_spin_structure_package
    (data : OneLoopNsnsSpinStructureData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitOneLoopNsnsSpinStructure
      (OneLoopNsnsSpinStructurePackage data)) :
    OneLoopNsnsSpinStructurePackage data := by
  exact h_phys

/-- Vanishing data for low-multiplicity genus-one NSNS amplitudes. -/
structure OneLoopNsnsLowMultiplicityVanishingData where
  externalCount : ℕ
  jacobiIdentitiesUsed : Bool
  transversalityUsed : Bool
  oneLoopAmplitude : ℂ

/-- Low-multiplicity one-loop NSNS package:
for `n ≤ 3`, Jacobi-theta identities and transversality imply vanishing amplitude. -/
def OneLoopNsnsLowMultiplicityVanishingPackage
    (data : OneLoopNsnsLowMultiplicityVanishingData) : Prop :=
  data.externalCount ≤ 3 →
    data.jacobiIdentitiesUsed = true ∧
    data.transversalityUsed = true ∧
    data.oneLoopAmplitude = 0

/-- Assumed low-multiplicity one-loop NSNS vanishing package from Section 8.2. -/
theorem one_loop_nsns_low_multiplicity_vanishing_package
    (data : OneLoopNsnsLowMultiplicityVanishingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitOneLoopNsnsVanishingLowMultiplicity
      (OneLoopNsnsLowMultiplicityVanishingPackage data)) :
    OneLoopNsnsLowMultiplicityVanishingPackage data := by
  exact h_phys

/-- One-loop four-point NSNS data near the leading low-energy term. -/
structure OneLoopNsnsFourPointData where
  stringCoupling : ℝ
  alphaPrime : ℝ
  nsKinematicTensor : ℂ
  leadingModularIntegral : ℝ
  reducedAmplitude : ℂ

/-- One-loop NSNS four-point package:
leading modular integral gives `π/6`, and the prefactor scales as
`g_s^4 /(2^10 π^2 α')`. -/
def OneLoopNsnsFourPointPackage (data : OneLoopNsnsFourPointData) : Prop :=
  data.stringCoupling > 0 ∧
  data.alphaPrime > 0 ∧
  data.leadingModularIntegral = Real.pi / 6 ∧
  data.reducedAmplitude =
    ((((data.stringCoupling ^ (4 : ℕ)) /
        ((2 : ℝ) ^ (10 : ℕ) * Real.pi ^ (2 : ℕ) * data.alphaPrime) *
        data.leadingModularIntegral : ℝ) : ℂ) * data.nsKinematicTensor)

/-- Assumed one-loop NSNS four-point leading package from Section 8.2. -/
theorem one_loop_nsns_four_point_package
    (data : OneLoopNsnsFourPointData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitOneLoopNsnsFourPointLeading
      (OneLoopNsnsFourPointPackage data)) :
    OneLoopNsnsFourPointPackage data := by
  exact h_phys

/-- One-loop four-point RR data. -/
structure OneLoopRrFourPointData where
  stringCoupling : ℝ
  alphaPrime : ℝ
  rrKinematicTensor : ℂ
  bosonicIntegral : ℂ
  reducedAmplitude : ℂ
  ramondThetaIdentityUsed : Bool

/-- One-loop RR four-point package:
spin-structure sums simplify by Ramond theta identities and produce
the expected RR tensor structure times the bosonic torus integral. -/
def OneLoopRrFourPointPackage (data : OneLoopRrFourPointData) : Prop :=
  data.stringCoupling > 0 ∧
  data.alphaPrime > 0 ∧
  data.ramondThetaIdentityUsed = true ∧
  data.reducedAmplitude =
    (((data.stringCoupling ^ (4 : ℕ) * data.alphaPrime ^ (2 : ℕ) /
        (2 : ℝ) ^ (8 : ℕ) : ℝ) : ℂ) *
      data.rrKinematicTensor * data.bosonicIntegral)

/-- Assumed one-loop RR four-point package from Section 8.3. -/
theorem one_loop_rr_four_point_package
    (data : OneLoopRrFourPointData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitOneLoopRrFourPoint
      (OneLoopRrFourPointPackage data)) :
    OneLoopRrFourPointPackage data := by
  exact h_phys

/-- Higher-genus ghost-correlator data for `(b_λ,c_{1-λ})` and `βγ` systems. -/
structure HigherGenusGhostCorrelatorData where
  genus : ℕ
  twiceLambdaMinusOne : ℤ
  bInsertions : ℤ
  cInsertions : ℤ
  anomalyDifference : ℤ
  bcCorrelator : ℂ
  partitionThetaPrimeFormFactor : ℂ
  betaGammaDeltaCorrelator : ℂ
  thetaDenominator : ℂ

/-- Higher-genus ghost package:
ghost-number anomaly `n-m=(2λ-1)(h-1)`, factorized `bc` correlator structure,
and inverse theta-denominator structure for `⟨δ(β)δ(γ)⟩` with spurious loci. -/
def HigherGenusGhostCorrelatorPackage
    (data : HigherGenusGhostCorrelatorData) : Prop :=
  data.anomalyDifference = data.bInsertions - data.cInsertions ∧
  data.anomalyDifference =
    data.twiceLambdaMinusOne * ((data.genus : ℤ) - 1) ∧
  data.bcCorrelator = data.partitionThetaPrimeFormFactor ∧
  data.thetaDenominator ≠ 0 ∧
  data.betaGammaDeltaCorrelator = 1 / data.thetaDenominator

/-- Assumed higher-genus ghost-correlator package from Section 8.4. -/
theorem higher_genus_ghost_correlator_package
    (data : HigherGenusGhostCorrelatorData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitHigherGenusGhostCorrelators
      (HigherGenusGhostCorrelatorPackage data)) :
    HigherGenusGhostCorrelatorPackage data := by
  exact h_phys

/-- Higher-loop vacuum-amplitude data in the PCO contour formalism. -/
structure HigherLoopVacuumVanishingData where
  genus : ℕ
  holomorphicPcos : ℤ
  antiholomorphicPcos : ℤ
  correctedIntegrandBoundaryContribution : ℂ
  boundaryIntegral : ℂ
  vacuumAmplitude : ℂ
  boundaryIsVerticalSlitsOnly : Bool
  xiPeriodIntegralZero : Bool
  supersymmetryWardIdentityUsed : Bool

/-- Higher-loop vacuum package:
for genus `h≥2`, `2h-2` PCOs per chirality, contour reduction to vertical slits,
and supersymmetry/BRST argument leading to vanishing vacuum amplitude. -/
def HigherLoopVacuumVanishingPackage
    (data : HigherLoopVacuumVanishingData) : Prop :=
  data.genus ≥ 2 ∧
  data.holomorphicPcos = 2 * (data.genus : ℤ) - 2 ∧
  data.antiholomorphicPcos = 2 * (data.genus : ℤ) - 2 ∧
  data.boundaryIntegral = data.correctedIntegrandBoundaryContribution ∧
  data.vacuumAmplitude = data.boundaryIntegral ∧
  data.boundaryIsVerticalSlitsOnly = true ∧
  data.xiPeriodIntegralZero = true ∧
  data.supersymmetryWardIdentityUsed = true ∧
  data.vacuumAmplitude = 0

/-- Assumed higher-loop vacuum-vanishing package from Section 8.5. -/
theorem higher_loop_vacuum_vanishing_package
    (data : HigherLoopVacuumVanishingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitHigherLoopVacuumVanishing
      (HigherLoopVacuumVanishingPackage data)) :
    HigherLoopVacuumVanishingPackage data := by
  exact h_phys

/-- Full four-supergraviton coupling-function data across perturbative orders. -/
structure FourGravitonCouplingFunctionData where
  alphaPrime : ℝ
  stringCoupling : ℝ
  mandelstamS : ℝ
  mandelstamT : ℝ
  mandelstamU : ℝ
  nsKinematicTensor : ℂ
  couplingFunction : ℝ
  fullAmplitude : ℂ
  oneLoopAZeroShift : ℝ
  higherLoopAZeroCorrectionAbsent : Bool

/-- Full four-supergraviton package:
`A_4 = const * K_NS * f(s,t;g_s)`, with the perturbative `α'^0` one-loop shift and
absence of further perturbative `α'^0` corrections. -/
def FourGravitonCouplingFunctionPackage
    (data : FourGravitonCouplingFunctionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.stringCoupling > 0 ∧
  data.mandelstamS + data.mandelstamT + data.mandelstamU = 0 ∧
  data.fullAmplitude =
    (((Real.pi ^ (2 : ℕ) * data.stringCoupling ^ (2 : ℕ) *
        data.alphaPrime ^ (3 : ℕ) / 16 * data.couplingFunction : ℝ) : ℂ) *
      data.nsKinematicTensor) ∧
  data.oneLoopAZeroShift =
    data.stringCoupling ^ (2 : ℕ) /
      (3 * (2 : ℝ) ^ (7 : ℕ) * Real.pi ^ (3 : ℕ) * data.alphaPrime ^ (4 : ℕ)) ∧
  data.higherLoopAZeroCorrectionAbsent = true

/-- Assumed full four-supergraviton coupling-function package from Section 8.5. -/
theorem four_graviton_coupling_function_package
    (data : FourGravitonCouplingFunctionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitFourGravitonCouplingFunction
      (FourGravitonCouplingFunctionPackage data)) :
    FourGravitonCouplingFunctionPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
