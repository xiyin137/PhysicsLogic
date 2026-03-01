import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- NSR-sector state-space and GSO decomposition data in general superstring backgrounds. -/
structure NsrSectorGsoData where
  totalMatterCentralChargeLeft : ℚ
  totalMatterCentralChargeRight : ℚ
  pictureNumberNS : ℚ
  pictureNumberR : ℚ
  hilbertSpaceDecompositionBySectors : Bool
  chiralGsoProjectionModularInvariant : Bool

/-- NSR/GSO package:
`c_m = c~_m = 15`, NS and R canonical pictures `-1` and `-1/2`,
and modular-invariant chiral GSO projection. -/
def NsrSectorGsoPackage (data : NsrSectorGsoData) : Prop :=
  data.totalMatterCentralChargeLeft = 15 ∧
  data.totalMatterCentralChargeRight = 15 ∧
  data.pictureNumberNS = -1 ∧
  data.pictureNumberR = (-1 / 2 : ℚ) ∧
  data.hilbertSpaceDecompositionBySectors = true ∧
  data.chiralGsoProjectionModularInvariant = true

/-- Assumed NSR/GSO sector package from Section 9.1. -/
theorem nsr_sector_gso_package
    (data : NsrSectorGsoData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundNsrHilbertGsoDecomposition
      (NsrSectorGsoPackage data)) :
    NsrSectorGsoPackage data := by
  exact h_phys

/-- NSNS worldsheet deformation data by integrated `(1,1)` superprimary insertions. -/
structure NsnsScftDeformationData where
  Configuration : Type
  actionFunctional : Configuration → ℂ
  deformedActionFunctional : Configuration → ℂ
  matterWeightLeft : ℚ
  matterWeightRight : ℚ
  preservesSuperconformalAtFirstOrder : Bool
  higherOrderCountertermsNeeded : Bool

/-- NSNS SCFT-deformation package:
deformation by integrated superfield descendant with matter weight `(1/2,1/2)`,
first-order superconformal preservation, and higher-order counterterm requirement. -/
def NsnsScftDeformationPackage (data : NsnsScftDeformationData) : Prop :=
  data.matterWeightLeft = (1 / 2 : ℚ) ∧
  data.matterWeightRight = (1 / 2 : ℚ) ∧
  data.preservesSuperconformalAtFirstOrder = true ∧
  data.higherOrderCountertermsNeeded = true

/-- Assumed NSNS SCFT deformation package from Section 9.1. -/
theorem nsns_scft_deformation_package
    (data : NsnsScftDeformationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundNsnsScftDeformation
      (NsnsScftDeformationPackage data)) :
    NsnsScftDeformationPackage data := by
  exact h_phys

/-- Supersymmetric NSNS sigma-model background data. -/
structure SupersymmetricNsnsNlsmData where
  Configuration : Type
  actionFunctional : Configuration → ℂ
  alphaPrime : ℝ
  hasMetricBackground : Bool
  hasBFieldBackground : Bool
  hasDilatonBackground : Bool
  hFieldIsExteriorDerivativeOfB : Bool
  worldsheet11Supersymmetry : Bool
  classicalWeylInvariance : Bool

/-- Supersymmetric NSNS sigma-model package:
worldsheet `(1,1)` supersymmetry, NSNS background fields `(G,B,Φ)`,
`H=dB`, and classical Weyl invariance. -/
def SupersymmetricNsnsNlsmPackage (data : SupersymmetricNsnsNlsmData) : Prop :=
  data.alphaPrime > 0 ∧
  data.hasMetricBackground = true ∧
  data.hasBFieldBackground = true ∧
  data.hasDilatonBackground = true ∧
  data.hFieldIsExteriorDerivativeOfB = true ∧
  data.worldsheet11Supersymmetry = true ∧
  data.classicalWeylInvariance = true

/-- Assumed supersymmetric NSNS NLSM package from Section 9.1. -/
theorem supersymmetric_nsns_nlsm_package
    (data : SupersymmetricNsnsNlsmData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundNsnsNlsmSuperspaceAction
      (SupersymmetricNsnsNlsmPackage data)) :
    SupersymmetricNsnsNlsmPackage data := by
  exact h_phys

/-- Tree-level massless NSNS spacetime effective-action data in string frame. -/
structure NsnsTreeEffectiveActionData where
  alphaPrime : ℝ
  einsteinTermCoefficient : ℚ
  hSquaredCoefficient : ℚ
  dilatonKineticCoefficient : ℚ
  dilatonExponentialWeight : ℤ
  noAlphaPrimeOrAlphaPrimeSqCorrections : Bool
  hasAlphaPrimeCubeCorrection : Bool

/-- Tree-level NSNS effective-action package:
`e^{-2Φ}(R - H^2/12 + 4(∂Φ)^2)` structure with expected correction pattern. -/
def NsnsTreeEffectiveActionPackage (data : NsnsTreeEffectiveActionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.einsteinTermCoefficient = 1 ∧
  data.hSquaredCoefficient = (-1 : ℚ) / 12 ∧
  data.dilatonKineticCoefficient = 4 ∧
  data.dilatonExponentialWeight = -2 ∧
  data.noAlphaPrimeOrAlphaPrimeSqCorrections = true ∧
  data.hasAlphaPrimeCubeCorrection = true

/-- Assumed NSNS tree-level effective-action package from Section 9.1. -/
theorem nsns_tree_effective_action_package
    (data : NsnsTreeEffectiveActionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundNsnsTreeEffectiveAction
      (NsnsTreeEffectiveActionPackage data)) :
    NsnsTreeEffectiveActionPackage data := by
  exact h_phys

/-- Calabi-Yau `(2,2)` superconformal NLSM data. -/
structure CalabiYauNlsmData where
  complexDimension : ℕ
  targetIsKahler : Bool
  kahlerMetricFromPotential : Bool
  has22SuperconformalSymmetry : Bool
  hasU1TimesU1RSymmetry : Bool
  rCurrentSplittingHolomorphicAntiholomorphic : Bool

/-- Calabi-Yau `(2,2)` package:
Kahler-target NLSM admits `(2,2)` superconformal structure and `U(1)×U(1)` R symmetry. -/
def CalabiYauNlsmPackage (data : CalabiYauNlsmData) : Prop :=
  data.complexDimension > 0 ∧
  data.targetIsKahler = true ∧
  data.kahlerMetricFromPotential = true ∧
  data.has22SuperconformalSymmetry = true ∧
  data.hasU1TimesU1RSymmetry = true ∧
  data.rCurrentSplittingHolomorphicAntiholomorphic = true

/-- Assumed Calabi-Yau `(2,2)` NLSM package from Section 9.2. -/
theorem calabi_yau_nlsm_package
    (data : CalabiYauNlsmData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundCalabiYau22Structure
      (CalabiYauNlsmPackage data)) :
    CalabiYauNlsmPackage data := by
  exact h_phys

/-- Calabi-Yau Ricci-flat/top-form data. -/
structure CalabiYauRicciFlatData where
  ricciFlatCondition : Bool
  logDetMetricLocalForm : Bool
  nowhereVanishingHolomorphicTopForm : Bool
  firstChernClassVanishing : Bool
  yauExistenceUniquenessInKahlerClass : Bool
  suHolonomyCovariantlyConstantSpinors : Bool

/-- Calabi-Yau Ricci-flat package:
Ricci-flat Kahler condition, holomorphic top form, `c1=0`, and Yau/holonomy consequences. -/
def CalabiYauRicciFlatPackage (data : CalabiYauRicciFlatData) : Prop :=
  data.ricciFlatCondition = true ∧
  data.logDetMetricLocalForm = true ∧
  data.nowhereVanishingHolomorphicTopForm = true ∧
  data.firstChernClassVanishing = true ∧
  data.yauExistenceUniquenessInKahlerClass = true ∧
  data.suHolonomyCovariantlyConstantSpinors = true

/-- Assumed Calabi-Yau Ricci-flat/top-form package from Section 9.2. -/
theorem calabi_yau_ricci_flat_package
    (data : CalabiYauRicciFlatData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundCalabiYauRicciFlatTopForm
      (CalabiYauRicciFlatPackage data)) :
    CalabiYauRicciFlatPackage data := by
  exact h_phys

/-- Flat-`B` worldsheet-instanton phase data in Calabi-Yau sigma models. -/
structure CalabiYauInstantonBFieldData where
  hFieldStrengthVanishes : Bool
  bFieldCouplingTopological : Bool
  affectsPerturbativeAlphaPrimeExpansion : Bool
  modifiesWorldsheetInstantonPhases : Bool

/-- Calabi-Yau flat-`B` package:
`H=0` makes the `B` coupling topological; perturbative `α'` dynamics unchanged
while non-perturbative worldsheet-instanton phases shift. -/
def CalabiYauInstantonBFieldPackage
    (data : CalabiYauInstantonBFieldData) : Prop :=
  data.hFieldStrengthVanishes = true ∧
  data.bFieldCouplingTopological = true ∧
  data.affectsPerturbativeAlphaPrimeExpansion = false ∧
  data.modifiesWorldsheetInstantonPhases = true

/-- Assumed Calabi-Yau flat-`B`/instanton-phase package from Section 9.2. -/
theorem calabi_yau_instanton_b_field_package
    (data : CalabiYauInstantonBFieldData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundCalabiYauInstantonBFieldPhase
      (CalabiYauInstantonBFieldPackage data)) :
    CalabiYauInstantonBFieldPackage data := by
  exact h_phys

/-- Green-Schwarz flat-background action and symmetry data. -/
structure GreenSchwarzFlatActionData where
  Configuration : Type
  actionFunctional : Configuration → ℂ
  decomposesAsSOnePlusSTwo : Bool
  spacetimeSupersymmetryInvariant : Bool
  kappaSymmetryInvariant : Bool
  kappaProjectsHalfFermions : Bool

/-- Green-Schwarz flat-background package:
`S = S1 + S2`, spacetime supersymmetry, and kappa symmetry removing half fermions. -/
def GreenSchwarzFlatActionPackage (data : GreenSchwarzFlatActionData) : Prop :=
  data.decomposesAsSOnePlusSTwo = true ∧
  data.spacetimeSupersymmetryInvariant = true ∧
  data.kappaSymmetryInvariant = true ∧
  data.kappaProjectsHalfFermions = true

/-- Assumed Green-Schwarz flat-action/kappa package from Section 9.3. -/
theorem green_schwarz_flat_action_package
    (data : GreenSchwarzFlatActionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundGreenSchwarzKappaSymmetry
      (GreenSchwarzFlatActionPackage data)) :
    GreenSchwarzFlatActionPackage data := by
  exact h_phys

/-- Light-cone gauge-fixed Green-Schwarz spectrum data. -/
structure GreenSchwarzLightConeGaugeData where
  kappaGaugeGammaPlusThetaZero : Bool
  lightConeGaugeFixed : Bool
  freeTransverseBosonCount : ℕ
  freeLeftMovingFermionCount : ℕ
  freeRightMovingFermionCount : ℕ

/-- Light-cone Green-Schwarz package:
in kappa/light-cone gauge the action reduces to free transverse fields with 8+8 fermions. -/
def GreenSchwarzLightConeGaugePackage
    (data : GreenSchwarzLightConeGaugeData) : Prop :=
  data.kappaGaugeGammaPlusThetaZero = true ∧
  data.lightConeGaugeFixed = true ∧
  data.freeTransverseBosonCount = 8 ∧
  data.freeLeftMovingFermionCount = 8 ∧
  data.freeRightMovingFermionCount = 8

/-- Assumed Green-Schwarz light-cone gauge package from Section 9.3. -/
theorem green_schwarz_light_cone_gauge_package
    (data : GreenSchwarzLightConeGaugeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundLightConeGaugeSpectrum
      (GreenSchwarzLightConeGaugePackage data)) :
    GreenSchwarzLightConeGaugePackage data := by
  exact h_phys

/-- Green-Schwarz superspace background-constraint data in general massless backgrounds. -/
structure GreenSchwarzSuperspaceConstraintData where
  superspaceCoordinatesInclude1032 : Bool
  supermetricFromVielbein : Bool
  superBFieldStrengthDefined : Bool
  torsionConstraintsSatisfied : Bool
  hFieldConstraintsSatisfied : Bool
  kappaVariationCancelsInAction : Bool
  describesOnShellTypeIISupergravityBackground : Bool

/-- Green-Schwarz superspace package:
super-vielbein metric relation, torsion/`H` constraint set, and resulting kappa invariance
for on-shell type-II supergravity backgrounds. -/
def GreenSchwarzSuperspaceConstraintPackage
    (data : GreenSchwarzSuperspaceConstraintData) : Prop :=
  data.superspaceCoordinatesInclude1032 = true ∧
  data.supermetricFromVielbein = true ∧
  data.superBFieldStrengthDefined = true ∧
  data.torsionConstraintsSatisfied = true ∧
  data.hFieldConstraintsSatisfied = true ∧
  data.kappaVariationCancelsInAction = true ∧
  data.describesOnShellTypeIISupergravityBackground = true

/-- Assumed Green-Schwarz superspace-constraint package from Section 9.4. -/
theorem green_schwarz_superspace_constraint_package
    (data : GreenSchwarzSuperspaceConstraintData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperBackgroundSuperspaceTorsionHConstraints
      (GreenSchwarzSuperspaceConstraintPackage data)) :
    GreenSchwarzSuperspaceConstraintPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
