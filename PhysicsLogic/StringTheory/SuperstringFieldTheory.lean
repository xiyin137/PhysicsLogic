import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- NS/R closed-superstring-field-space data, including auxiliary Ramond picture assignments. -/
structure SuperSftFieldSpaceData where
  brstNilpotent : Bool
  totalCentralChargeZero : Bool
  b0MinusAndL0MinusConstraints : Bool
  chiralGsoProjected : Bool
  auxiliaryRamondPictureMinusThreeHalfIncluded : Bool

/-- Super-SFT field-space package:
`H_0` constraints with GSO projection and auxiliary `-3/2` Ramond picture sector. -/
def SuperSftFieldSpacePackage (data : SuperSftFieldSpaceData) : Prop :=
  data.brstNilpotent = true ∧
  data.totalCentralChargeZero = true ∧
  data.b0MinusAndL0MinusConstraints = true ∧
  data.chiralGsoProjected = true ∧
  data.auxiliaryRamondPictureMinusThreeHalfIncluded = true

/-- Assumed NS/R super-SFT field-space package from Section 10.1. -/
theorem super_sft_field_space_package
    (data : SuperSftFieldSpaceData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftFieldSpaceNsrAuxiliary
      (SuperSftFieldSpacePackage data)) :
    SuperSftFieldSpacePackage data := by
  exact h_phys

/-- Off-shell superstring-amplitude chain data on `Q-hat_{h,n}`. -/
structure SuperSftOffShellAmplitudeData where
  genus : ℕ
  punctures : ℕ
  chainDimension : ℤ
  holomorphicPcoCount : ℤ
  antiholomorphicPcoCount : ℤ
  nsPuncturesHolomorphic : ℕ
  ramondPairsHolomorphic : ℕ
  nsPuncturesAntiholomorphic : ℕ
  ramondPairsAntiholomorphic : ℕ
  normalization : ℂ
  contourIntegral : ℂ
  offShellAmplitude : ℂ
  verticalBoundaryOnly : Bool
  coversAllSpinStructures : Bool

/-- Off-shell super-SFT amplitude package:
`dim S = 6h-6+2n`, NS/R-dependent PCO counting, and vertical-slit chain boundary data. -/
def SuperSftOffShellAmplitudePackage
    (data : SuperSftOffShellAmplitudeData) : Prop :=
  data.chainDimension = 6 * (data.genus : ℤ) - 6 + 2 * (data.punctures : ℤ) ∧
  data.holomorphicPcoCount =
    2 * (data.genus : ℤ) - 2 +
      (data.nsPuncturesHolomorphic : ℤ) + (data.ramondPairsHolomorphic : ℤ) ∧
  data.antiholomorphicPcoCount =
    2 * (data.genus : ℤ) - 2 +
      (data.nsPuncturesAntiholomorphic : ℤ) + (data.ramondPairsAntiholomorphic : ℤ) ∧
  data.offShellAmplitude = data.normalization * data.contourIntegral ∧
  data.verticalBoundaryOnly = true ∧
  data.coversAllSpinStructures = true

/-- Assumed off-shell super-SFT chain package from Section 10.1. -/
theorem super_sft_off_shell_amplitude_package
    (data : SuperSftOffShellAmplitudeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftOffShellAmplitudeChain
      (SuperSftOffShellAmplitudePackage data)) :
    SuperSftOffShellAmplitudePackage data := by
  exact h_phys

/-- Degeneration/plumbing compatibility data for super-SFT chains with NS/R punctures. -/
structure SuperSftPlumbingCompatibilityData where
  nsPlumbingPreservesPcoCount : Bool
  ramondPlumbingAddsAveragePco : Bool
  degenerationCompatibilityHolds : Bool
  spuriousSingularityAbsentInDegenerationLimit : Bool

/-- Super-SFT plumbing compatibility package:
Ramond plumbing adds averaged PCO insertions while preserving degeneration compatibility. -/
def SuperSftPlumbingCompatibilityPackage
    (data : SuperSftPlumbingCompatibilityData) : Prop :=
  data.nsPlumbingPreservesPcoCount = true ∧
  data.ramondPlumbingAddsAveragePco = true ∧
  data.degenerationCompatibilityHolds = true ∧
  data.spuriousSingularityAbsentInDegenerationLimit = true

/-- Assumed Ramond plumbing/PCO compatibility package from Section 10.1. -/
theorem super_sft_plumbing_compatibility_package
    (data : SuperSftPlumbingCompatibilityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftRamondPlumbingPcoCompatibility
      (SuperSftPlumbingCompatibilityPackage data)) :
    SuperSftPlumbingCompatibilityPackage data := by
  exact h_phys

/-- 1PI effective-action data with picture-adjusted propagator. -/
structure SuperSftOnePiData where
  pictureAdjustingOperatorActsBySector : Bool
  siegelPropagatorHasPictureAdjustment : Bool
  onePiActionMatchesFeynmanExpansion : Bool
  legendreTransformRelationHolds : Bool

/-- Super-SFT 1PI package:
`(b_0^+ b_0^- / L_0^+) G` propagator and equivalent 1PI/Legendre formulations. -/
def SuperSftOnePiPackage (data : SuperSftOnePiData) : Prop :=
  data.pictureAdjustingOperatorActsBySector = true ∧
  data.siegelPropagatorHasPictureAdjustment = true ∧
  data.onePiActionMatchesFeynmanExpansion = true ∧
  data.legendreTransformRelationHolds = true

/-- Assumed 1PI picture-adjusted propagator package from Section 10.2. -/
theorem super_sft_one_pi_package
    (data : SuperSftOnePiData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftOnePiPictureAdjustedPropagator
      (SuperSftOnePiPackage data)) :
    SuperSftOnePiPackage data := by
  exact h_phys

/-- Ramond picture-degeneracy control data in the super-SFT propagator sector. -/
structure SuperSftRamondDegeneracyControlData where
  infiniteBZeroTowerPresent : Bool
  pictureRaisingKillsAllButFiniteTower : Bool
  propagatorContributionRemainsFinite : Bool

/-- Ramond degeneracy-control package:
`X_0` maps only finitely many states in each degenerate `B_0^n` family to nonzero modes. -/
def SuperSftRamondDegeneracyControlPackage
    (data : SuperSftRamondDegeneracyControlData) : Prop :=
  data.infiniteBZeroTowerPresent = true ∧
  data.pictureRaisingKillsAllButFiniteTower = true ∧
  data.propagatorContributionRemainsFinite = true

/-- Assumed Ramond-tower regularization package from Section 10.2. -/
theorem super_sft_ramond_degeneracy_control_package
    (data : SuperSftRamondDegeneracyControlData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftRamondTowerRegularization
      (SuperSftRamondDegeneracyControlPackage data)) :
    SuperSftRamondDegeneracyControlPackage data := by
  exact h_phys

/-- BV quantum super-SFT data. -/
structure SuperSftBvQuantumData where
  bvSymplecticPairingCanonical : Bool
  geometricMasterEquationHolds : Bool
  quantumMasterEquationHolds : Bool
  ramondPlumbingIncludesPictureAdjustment : Bool

/-- BV quantum super-SFT package:
canonical BV pairing, geometric master equation, and quantum master equation with
Ramond-sector picture-adjustment insertions. -/
def SuperSftBvQuantumPackage (data : SuperSftBvQuantumData) : Prop :=
  data.bvSymplecticPairingCanonical = true ∧
  data.geometricMasterEquationHolds = true ∧
  data.quantumMasterEquationHolds = true ∧
  data.ramondPlumbingIncludesPictureAdjustment = true

/-- Assumed BV quantum-master package for closed super-SFT from Section 10.3. -/
theorem super_sft_bv_quantum_package
    (data : SuperSftBvQuantumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftBvQuantumMasterEquation
      (SuperSftBvQuantumPackage data)) :
    SuperSftBvQuantumPackage data := by
  exact h_phys

/-- RR kinetic-sector data in closed super-SFT. -/
structure SuperSftRrKineticData where
  stringCoupling : ℝ
  rrFieldStrengthUnconstrainedOffShell : Bool
  auxiliaryFieldsIncludedInKineticSector : Bool
  rrTwoPointFunctionMatchesSupergravityKinetics : Bool
  typeIibFiveFormSelfDualProjectionHandled : Bool

/-- RR kinetic package:
auxiliary-field kinetic structure yields the RR two-point function consistent with
supergravity kinetic terms (with type-IIB self-duality handling). -/
def SuperSftRrKineticPackage (data : SuperSftRrKineticData) : Prop :=
  data.stringCoupling > 0 ∧
  data.rrFieldStrengthUnconstrainedOffShell = true ∧
  data.auxiliaryFieldsIncludedInKineticSector = true ∧
  data.rrTwoPointFunctionMatchesSupergravityKinetics = true ∧
  data.typeIibFiveFormSelfDualProjectionHandled = true

/-- Assumed RR kinetic-term matching package from Section 10.4. -/
theorem super_sft_rr_kinetic_package
    (data : SuperSftRrKineticData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftRrKineticTermMatching
      (SuperSftRrKineticPackage data)) :
    SuperSftRrKineticPackage data := by
  exact h_phys

/-- Superstring field-equation data from the 1PI effective action. -/
structure SuperSftFieldEquationData where
  brstTerm : ℂ
  higherBracketTerm : ℂ
  equationResidual : ℂ
  bracketDefinedByAuxiliaryPairing : Bool
  infinitesimalGaugeRedundancyPresent : Bool

/-- Super-SFT field-equation package:
`Q_B Ψ + Σ (1/n!)[Ψ^n] = 0` with bracket defined by 1PI auxiliary pairing data. -/
def SuperSftFieldEquationPackage (data : SuperSftFieldEquationData) : Prop :=
  data.equationResidual = data.brstTerm + data.higherBracketTerm ∧
  data.equationResidual = 0 ∧
  data.bracketDefinedByAuxiliaryPairing = true ∧
  data.infinitesimalGaugeRedundancyPresent = true

/-- Assumed super-SFT field-equation/bracket package from Section 10.5. -/
theorem super_sft_field_equation_package
    (data : SuperSftFieldEquationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftFieldEquationBracketPackage
      (SuperSftFieldEquationPackage data)) :
    SuperSftFieldEquationPackage data := by
  exact h_phys

/-- Flat-frame superstring-bracket construction data with vertical-correction terms. -/
structure SuperSftFlatBracketData where
  twoStringBracketUsesPictureAdjuster : Bool
  threeStringBracketUsesVerticalCorrection : Bool
  lInfinityCompatibilityMaintained : Bool

/-- Flat superstring-bracket package:
`G`-adjusted 2-string bracket and vertically corrected 3-string bracket preserve
the expected homotopy-algebra compatibility. -/
def SuperSftFlatBracketPackage (data : SuperSftFlatBracketData) : Prop :=
  data.twoStringBracketUsesPictureAdjuster = true ∧
  data.threeStringBracketUsesVerticalCorrection = true ∧
  data.lInfinityCompatibilityMaintained = true

/-- Assumed flat-bracket vertical-correction package from Section 10.5. -/
theorem super_sft_flat_bracket_package
    (data : SuperSftFlatBracketData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftFlatBracketVerticalCorrection
      (SuperSftFlatBracketPackage data)) :
    SuperSftFlatBracketPackage data := by
  exact h_phys

/-- pp-wave massless super-SFT solution data. -/
structure SuperSftPpWaveSolutionData where
  deformationParameter : ℝ
  rrFiveFormFluxTurnedOn : Bool
  nsnsMetricBackreactionIncluded : Bool
  boostSymmetryTruncatesHigherMasslessBrackets : Bool
  solvesMasslessEquationAllOrders : Bool

/-- pp-wave super-SFT solution package:
RR-flux plus NSNS metric deformation solves the massless SFT equation to all orders
due to boost-charge selection on higher brackets. -/
def SuperSftPpWaveSolutionPackage (data : SuperSftPpWaveSolutionData) : Prop :=
  data.deformationParameter ≠ 0 ∧
  data.rrFiveFormFluxTurnedOn = true ∧
  data.nsnsMetricBackreactionIncluded = true ∧
  data.boostSymmetryTruncatesHigherMasslessBrackets = true ∧
  data.solvesMasslessEquationAllOrders = true

/-- Assumed pp-wave super-SFT solution package from Section 10.5. -/
theorem super_sft_pp_wave_solution_package
    (data : SuperSftPpWaveSolutionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperSftPpWaveSolutionPackage
      (SuperSftPpWaveSolutionPackage data)) :
    SuperSftPpWaveSolutionPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
