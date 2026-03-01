import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- NS5 with transverse-circle T-duality to Taub-NUT/orbifold data. -/
structure Ns5TaubNutDualityData where
  ns5Count : Nat
  transverseCircleRadius : Real
  stringLengthSquared : Real
  smearedHarmonicProfileUsed : Bool
  buscherDualityAlongTransverseCircleUsed : Bool
  taubNutMetricWithMonopoleConnectionUsed : Bool
  decompactificationLimitGivesC2Quotient : Bool
  normalizableMarginalDeformationsMatchBranePositions : Bool

/-- Section 19.1 package:
NS5 transverse-circle background, Buscher duality to Taub-NUT, and orbifold limit. -/
def Ns5TaubNutDualityPackage (data : Ns5TaubNutDualityData) : Prop :=
  data.ns5Count > 0 /\
  data.transverseCircleRadius > 0 /\
  data.stringLengthSquared > 0 /\
  data.smearedHarmonicProfileUsed = true /\
  data.buscherDualityAlongTransverseCircleUsed = true /\
  data.taubNutMetricWithMonopoleConnectionUsed = true /\
  data.decompactificationLimitGivesC2Quotient = true /\
  data.normalizableMarginalDeformationsMatchBranePositions = true

/-- Assumed Section 19.1 NS5/Taub-NUT duality package. -/
theorem ns5_taub_nut_duality_package
    (data : Ns5TaubNutDualityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSingularityNs5TaubNutTDuality
      (Ns5TaubNutDualityPackage data)) :
    Ns5TaubNutDualityPackage data := by
  exact h_phys

/-- `C^2/Z_k` orbifold twisted-sector and exactly marginal deformation data. -/
structure OrbifoldTwistMarginalData where
  orbifoldOrder : Nat
  freeFieldOrbifoldConstructionUsed : Bool
  nFourSuperconformalCurrentsSurviveProjection : Bool
  twistedSectorGroundWeightFormulaUsed : Bool
  twistedChiralPrimariesConstructed : Bool
  marginalDescendantsFromNFourSuperchargesUsed : Bool
  exactMarginalityFromBpsSelectionRulesUsed : Bool

/-- Section 19.2.1 package:
twisted-sector chiral primaries and exactly marginal `(4,4)` preserving deformations. -/
def OrbifoldTwistMarginalPackage (data : OrbifoldTwistMarginalData) : Prop :=
  data.orbifoldOrder > 1 /\
  data.freeFieldOrbifoldConstructionUsed = true /\
  data.nFourSuperconformalCurrentsSurviveProjection = true /\
  data.twistedSectorGroundWeightFormulaUsed = true /\
  data.twistedChiralPrimariesConstructed = true /\
  data.marginalDescendantsFromNFourSuperchargesUsed = true /\
  data.exactMarginalityFromBpsSelectionRulesUsed = true

/-- Assumed Section 19.2.1 orbifold twist/marginal package. -/
theorem orbifold_twist_marginal_package
    (data : OrbifoldTwistMarginalData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSingularityOrbifoldNFourTwistMarginal
      (OrbifoldTwistMarginalPackage data)) :
    OrbifoldTwistMarginalPackage data := by
  exact h_phys

/-- `C^2/Z_k` conformal-manifold geometry data. -/
structure OrbifoldConformalManifoldData where
  orbifoldOrder : Nat
  exactlyMarginalDimensionFormulaUsed : Bool
  zamolodchikovMetricDefinitionUsed : Bool
  kTwoAleMetricAndBFieldPeriodDictionaryUsed : Bool
  singularAndRegularFixedPointsDistinguished : Bool
  ns5RelativeModuliQuotientByPermutationUsed : Bool

/-- Section 19.2.2 package:
orbifold conformal manifold geometry and `k=2` ALE/B-field parameterization. -/
def OrbifoldConformalManifoldPackage
    (data : OrbifoldConformalManifoldData) : Prop :=
  data.orbifoldOrder > 1 /\
  data.exactlyMarginalDimensionFormulaUsed = true /\
  data.zamolodchikovMetricDefinitionUsed = true /\
  data.kTwoAleMetricAndBFieldPeriodDictionaryUsed = true /\
  data.singularAndRegularFixedPointsDistinguished = true /\
  data.ns5RelativeModuliQuotientByPermutationUsed = true

/-- Assumed Section 19.2.2 orbifold conformal-manifold package. -/
theorem orbifold_conformal_manifold_package
    (data : OrbifoldConformalManifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSingularityOrbifoldConformalManifoldSingularPoints
      (OrbifoldConformalManifoldPackage data)) :
    OrbifoldConformalManifoldPackage data := by
  exact h_phys

/-- Massless wrapped-brane and gauge-enhancement data near orbifold singular points. -/
structure OrbifoldWrappedBraneGaugeEnhancementData where
  typeIIAStringCoupling : Real
  wrappedD2BpsMassFormulaUsed : Bool
  wrappedD2MassVanishesAtSingularPoint : Bool
  sixDimensionalAbelianToSUkEnhancementUsed : Bool
  wrappedD2IdentifiedWithWBoson : Bool

/-- Section 19.2.3 package:
wrapped D2 BPS states and non-abelian gauge enhancement at singular CFT points. -/
def OrbifoldWrappedBraneGaugeEnhancementPackage
    (data : OrbifoldWrappedBraneGaugeEnhancementData) : Prop :=
  data.typeIIAStringCoupling > 0 /\
  data.wrappedD2BpsMassFormulaUsed = true /\
  data.wrappedD2MassVanishesAtSingularPoint = true /\
  data.sixDimensionalAbelianToSUkEnhancementUsed = true /\
  data.wrappedD2IdentifiedWithWBoson = true

/-- Assumed Section 19.2.3 singular-orbifold wrapped-brane package. -/
theorem orbifold_wrapped_brane_gauge_enhancement_package
    (data : OrbifoldWrappedBraneGaugeEnhancementData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSingularityOrbifoldWrappedDbraneGaugeEnhancement
      (OrbifoldWrappedBraneGaugeEnhancementPackage data)) :
    OrbifoldWrappedBraneGaugeEnhancementPackage data := by
  exact h_phys

/-- D-branes in orbifold boundary-state/fractional-brane data. -/
structure OrbifoldFractionalBraneData where
  orbifoldOrder : Nat
  defectLineEndpointConstructionUsed : Bool
  orbifoldBoundaryStatePhaseSumConstructionUsed : Bool
  openSpectrumFromOrbifoldEigenvalueSectorsUsed : Bool
  fractionalDzeroBranesLocalizedAtFixedPoint : Bool
  fractionalMassOneOverKOfBulkDzero : Bool
  aleDeformationMapsFractionalDzeroToWrappedDtwo : Bool

/-- Section 19.3 package:
orbifold boundary-state construction and fractional-brane interpretation. -/
def OrbifoldFractionalBranePackage (data : OrbifoldFractionalBraneData) : Prop :=
  data.orbifoldOrder > 1 /\
  data.defectLineEndpointConstructionUsed = true /\
  data.orbifoldBoundaryStatePhaseSumConstructionUsed = true /\
  data.openSpectrumFromOrbifoldEigenvalueSectorsUsed = true /\
  data.fractionalDzeroBranesLocalizedAtFixedPoint = true /\
  data.fractionalMassOneOverKOfBulkDzero = true /\
  data.aleDeformationMapsFractionalDzeroToWrappedDtwo = true

/-- Assumed Section 19.3 orbifold D-brane package. -/
theorem orbifold_fractional_brane_package
    (data : OrbifoldFractionalBraneData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSingularityOrbifoldFractionalBraneBoundaryState
      (OrbifoldFractionalBranePackage data)) :
    OrbifoldFractionalBranePackage data := by
  exact h_phys

/-- DSLST double-scaling background and exact coset realization data. -/
structure DslstDoubleScalingData where
  ns5Count : Nat
  asymptoticStringCoupling : Real
  ringRadiusScale : Real
  doubleScalingLimitRhoZeroWithFixedRescaledCouplingUsed : Bool
  tDualCigarTimesBellWithZkQuotientUsed : Bool
  exactSl2TimesSu2CosetQuotientDescriptionUsed : Bool

/-- Section 19.4 package:
double-scaling NS5 limit and exact `((SL(2,R)/U(1)) x (SU(2)/U(1)))/Z_k` background. -/
def DslstDoubleScalingPackage (data : DslstDoubleScalingData) : Prop :=
  data.ns5Count > 0 /\
  data.asymptoticStringCoupling > 0 /\
  data.ringRadiusScale > 0 /\
  data.doubleScalingLimitRhoZeroWithFixedRescaledCouplingUsed = true /\
  data.tDualCigarTimesBellWithZkQuotientUsed = true /\
  data.exactSl2TimesSu2CosetQuotientDescriptionUsed = true

/-- Assumed Section 19.4 DSLST double-scaling/coset package. -/
theorem dslst_double_scaling_package
    (data : DslstDoubleScalingData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDslstDoubleScalingCosetBackground
      (DslstDoubleScalingPackage data)) :
    DslstDoubleScalingPackage data := by
  exact h_phys

/-- `N=2` supersymmetric `SU(2)_k/U(1)` coset data in DSLST. -/
structure DslstSu2CosetData where
  levelK : Nat
  su2CosetCentralChargeFormulaUsed : Bool
  nTwoSupercurrentAndRCurrentConstructionUsed : Bool
  bosonizedParafermionIdentificationUsed : Bool
  spectralFlowAndFieldIdentificationRulesUsed : Bool
  modularInvariantSelectionRulesUsed : Bool
  emergentZkSymmetryFromStrongCouplingUsed : Bool

/-- Section 19.4.1 package:
`N=2` `SU(2)_k/U(1)` coset structure, spectrum constraints, and `Z_k` action. -/
def DslstSu2CosetPackage (data : DslstSu2CosetData) : Prop :=
  data.levelK > 1 /\
  data.su2CosetCentralChargeFormulaUsed = true /\
  data.nTwoSupercurrentAndRCurrentConstructionUsed = true /\
  data.bosonizedParafermionIdentificationUsed = true /\
  data.spectralFlowAndFieldIdentificationRulesUsed = true /\
  data.modularInvariantSelectionRulesUsed = true /\
  data.emergentZkSymmetryFromStrongCouplingUsed = true

/-- Assumed Section 19.4.1 `SU(2)_k/U(1)` coset package. -/
theorem dslst_su2_coset_package
    (data : DslstSu2CosetData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDslstSu2CosetNTwoStructure
      (DslstSu2CosetPackage data)) :
    DslstSu2CosetPackage data := by
  exact h_phys

/-- `N=2` supersymmetric `SL(2,R)_k/U(1)` coset data in DSLST. -/
structure DslstSl2CosetData where
  levelK : Nat
  sl2CosetCentralChargeFormulaUsed : Bool
  continuousAndDiscreteSeriesSpectrumUsed : Bool
  windingIntegralityConstraintUsed : Bool
  asymptoticCigarReflectionRelationUsed : Bool
  spectralFlowConstraintsForCigarSpectrumUsed : Bool
  exactCigarSigmaModelDictionaryUsed : Bool

/-- Section 19.4.2 package:
`N=2` `SL(2,R)_k/U(1)` cigar spectrum and winding/spectral-flow constraints. -/
def DslstSl2CosetPackage (data : DslstSl2CosetData) : Prop :=
  data.levelK > 0 /\
  data.sl2CosetCentralChargeFormulaUsed = true /\
  data.continuousAndDiscreteSeriesSpectrumUsed = true /\
  data.windingIntegralityConstraintUsed = true /\
  data.asymptoticCigarReflectionRelationUsed = true /\
  data.spectralFlowConstraintsForCigarSpectrumUsed = true /\
  data.exactCigarSigmaModelDictionaryUsed = true

/-- Assumed Section 19.4.2 `SL(2,R)_k/U(1)` coset package. -/
theorem dslst_sl2_coset_package
    (data : DslstSl2CosetData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDslstSl2CosetCigarSpectrum
      (DslstSl2CosetPackage data)) :
    DslstSl2CosetPackage data := by
  exact h_phys

/-- Mirror relation between cigar coset and `N=2` Liouville data. -/
structure DslstLiouvilleMirrorData where
  levelK : Nat
  asymptoticLinearDilatonPlusCircleSystemUsed : Bool
  nTwoScaWithBackgroundChargeUsed : Bool
  liouvilleInteractionFromChiralPrimaryDeformationUsed : Bool
  superspaceLiouvilleActionUsed : Bool
  cigarLiouvilleMirrorEquivalenceUsed : Bool

/-- Section 19.4.3 package:
mirror relation between cigar coset and `N=2` Liouville theory. -/
def DslstLiouvilleMirrorPackage (data : DslstLiouvilleMirrorData) : Prop :=
  data.levelK > 0 /\
  data.asymptoticLinearDilatonPlusCircleSystemUsed = true /\
  data.nTwoScaWithBackgroundChargeUsed = true /\
  data.liouvilleInteractionFromChiralPrimaryDeformationUsed = true /\
  data.superspaceLiouvilleActionUsed = true /\
  data.cigarLiouvilleMirrorEquivalenceUsed = true

/-- Assumed Section 19.4.3 cigar/Liouville mirror package. -/
theorem dslst_liouville_mirror_package
    (data : DslstLiouvilleMirrorData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDslstCigarLiouvilleMirrorDuality
      (DslstLiouvilleMirrorPackage data)) :
    DslstLiouvilleMirrorPackage data := by
  exact h_phys

/-- DSLST physical-state spectrum and six-dimensional interpretation data. -/
structure DslstMasslessSpectrumData where
  levelK : Nat
  zkOrbifoldProjectionConstraintsUsed : Bool
  gsoConstraintsFromIntegralRChargesUsed : Bool
  masslessNsNsScalarQuantumNumbersUsed : Bool
  masslessRrQuantumNumbersUsed : Bool
  sixDimensionalRelativeNs5ModuliInterpretationUsed : Bool
  littleStringLimitAtVanishingSeparationUsed : Bool

/-- Section 19.4.4 package:
DSLST massless states and six-dimensional NS5-brane effective interpretation. -/
def DslstMasslessSpectrumPackage (data : DslstMasslessSpectrumData) : Prop :=
  data.levelK > 1 /\
  data.zkOrbifoldProjectionConstraintsUsed = true /\
  data.gsoConstraintsFromIntegralRChargesUsed = true /\
  data.masslessNsNsScalarQuantumNumbersUsed = true /\
  data.masslessRrQuantumNumbersUsed = true /\
  data.sixDimensionalRelativeNs5ModuliInterpretationUsed = true /\
  data.littleStringLimitAtVanishingSeparationUsed = true

/-- Assumed Section 19.4.4 DSLST massless-spectrum package. -/
theorem dslst_massless_spectrum_package
    (data : DslstMasslessSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDslstMasslessSpectrumSixDInterpretation
      (DslstMasslessSpectrumPackage data)) :
    DslstMasslessSpectrumPackage data := by
  exact h_phys

/-- Conifold geometry data for singular, deformed, and resolved phases. -/
structure ConifoldGeometryData where
  deformationParameterAbs : Real
  resolutionParameter : Real
  conifoldEquationAndTOneOneMetricUsed : Bool
  holomorphicDeterminantConstraintDescriptionUsed : Bool
  deformedConifoldRicciFlatMetricUsed : Bool
  minimalThreeSphereAtTipUsed : Bool
  resolvedConifoldRicciFlatMetricUsed : Bool
  flopTransitionExchangingTwoSpheresUsed : Bool

/-- Section 19.5.1 package:
conifold geometry and its deformed/resolved Ricci-flat branches. -/
def ConifoldGeometryPackage (data : ConifoldGeometryData) : Prop :=
  data.deformationParameterAbs > 0 /\
  data.resolutionParameter > 0 /\
  data.conifoldEquationAndTOneOneMetricUsed = true /\
  data.holomorphicDeterminantConstraintDescriptionUsed = true /\
  data.deformedConifoldRicciFlatMetricUsed = true /\
  data.minimalThreeSphereAtTipUsed = true /\
  data.resolvedConifoldRicciFlatMetricUsed = true /\
  data.flopTransitionExchangingTwoSpheresUsed = true

/-- Assumed Section 19.5.1 conifold geometry package. -/
theorem conifold_geometry_package
    (data : ConifoldGeometryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConifoldGeometryDeformedResolvedMetrics
      (ConifoldGeometryPackage data)) :
    ConifoldGeometryPackage data := by
  exact h_phys

/-- Type-IIB conifold transition data with wrapped D3-hypermultiplet resolution. -/
structure ConifoldTypeIibTransitionData where
  complexStructurePeriod : Complex
  wrappedD3Mass : Real
  holomorphicThreeFormPeriodsUsed : Bool
  specialKahlerMetricFromPeriodsUsed : Bool
  logarithmicMetricBehaviorNearConifoldPointUsed : Bool
  wrappedD3HypermultipletBecomesMasslessAtVanishingPeriod : Bool
  wilsonianVectorPlusChargedHyperDescriptionUsed : Bool
  oneLoopHyperContributionReproducesLogPrepotentialTerm : Bool
  coulombAndHiggsBranchesMapToDeformedAndResolvedPhases : Bool

/-- Section 19.5.2 package:
type-IIB conifold EFT with vector/hypermultiplet transition description. -/
def ConifoldTypeIibTransitionPackage
    (data : ConifoldTypeIibTransitionData) : Prop :=
  data.wrappedD3Mass ≥ 0 /\
  data.holomorphicThreeFormPeriodsUsed = true /\
  data.specialKahlerMetricFromPeriodsUsed = true /\
  data.logarithmicMetricBehaviorNearConifoldPointUsed = true /\
  data.wrappedD3HypermultipletBecomesMasslessAtVanishingPeriod = true /\
  data.wilsonianVectorPlusChargedHyperDescriptionUsed = true /\
  data.oneLoopHyperContributionReproducesLogPrepotentialTerm = true /\
  data.coulombAndHiggsBranchesMapToDeformedAndResolvedPhases = true

/-- Assumed Section 19.5.2 type-IIB conifold transition package. -/
theorem conifold_type_iib_transition_package
    (data : ConifoldTypeIibTransitionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConifoldTypeIibTransitionWrappedD3Hypermultiplet
      (ConifoldTypeIibTransitionPackage data)) :
    ConifoldTypeIibTransitionPackage data := by
  exact h_phys

/-- Type-IIA conifold transition data with complexified Kahler modulus and wrapped D2 states. -/
structure ConifoldTypeIiaTransitionData where
  complexifiedKahlerModulus : Complex
  wrappedD2Mass : Real
  harmonicOneOneModeForKahlerVariationUsed : Bool
  complexifiedKahlerPeriodDefinitionUsed : Bool
  perturbativeCubicPrepotentialFromPecceiQuinnSymmetryUsed : Bool
  worldsheetInstantonsBreakContinuousShiftToIntegerLattice : Bool
  wrappedD2D0TowerRealizationUsed : Bool
  oneLoopHypermultipletShiftMatchesLogSingularity : Bool

/-- Section 19.5.3 package:
type-IIA conifold EFT and wrapped D2/D0 non-perturbative structure. -/
def ConifoldTypeIiaTransitionPackage
    (data : ConifoldTypeIiaTransitionData) : Prop :=
  data.wrappedD2Mass ≥ 0 /\
  data.harmonicOneOneModeForKahlerVariationUsed = true /\
  data.complexifiedKahlerPeriodDefinitionUsed = true /\
  data.perturbativeCubicPrepotentialFromPecceiQuinnSymmetryUsed = true /\
  data.worldsheetInstantonsBreakContinuousShiftToIntegerLattice = true /\
  data.wrappedD2D0TowerRealizationUsed = true /\
  data.oneLoopHypermultipletShiftMatchesLogSingularity = true

/-- Assumed Section 19.5.3 type-IIA conifold transition package. -/
theorem conifold_type_iia_transition_package
    (data : ConifoldTypeIiaTransitionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConifoldTypeIiaTransitionWrappedD2Hypermultiplet
      (ConifoldTypeIiaTransitionPackage data)) :
    ConifoldTypeIiaTransitionPackage data := by
  exact h_phys

/-- Worldsheet-instanton data for the resolved-conifold prepotential. -/
structure ConifoldWorldsheetInstantonData where
  windingNumber : Nat
  complexifiedKahlerModulus : Complex
  instantonAction : Complex
  holomorphicMapsToExceptionalSphereUsed : Bool
  rationalMapModuliSpaceWithNonzeroResultantUsed : Bool
  topologicalTwistLocalizationUsed : Bool
  fermionZeroModeCountingAndCurvatureInsertionUsed : Bool
  degreeKContributionWeightExpTwoPiIKtUsed : Bool
  instantonCoefficientAkEqualsInverseKCube : Bool

/-- Section 19.5.4 package:
worldsheet-instanton expansion of conifold Yukawa coupling/prepotential. -/
def ConifoldWorldsheetInstantonPackage
    (data : ConifoldWorldsheetInstantonData) : Prop :=
  data.windingNumber > 0 /\
  data.instantonAction =
    -2 * Real.pi * Complex.I * (data.windingNumber : Complex) *
      data.complexifiedKahlerModulus /\
  data.holomorphicMapsToExceptionalSphereUsed = true /\
  data.rationalMapModuliSpaceWithNonzeroResultantUsed = true /\
  data.topologicalTwistLocalizationUsed = true /\
  data.fermionZeroModeCountingAndCurvatureInsertionUsed = true /\
  data.degreeKContributionWeightExpTwoPiIKtUsed = true /\
  data.instantonCoefficientAkEqualsInverseKCube = true

/-- Assumed Section 19.5.4 conifold worldsheet-instanton package. -/
theorem conifold_worldsheet_instanton_package
    (data : ConifoldWorldsheetInstantonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConifoldWorldsheetInstantonExpansion
      (ConifoldWorldsheetInstantonPackage data)) :
    ConifoldWorldsheetInstantonPackage data := by
  exact h_phys

/-- Singular-conifold CFT data from GLSM and effective Liouville limit. -/
structure ConifoldSingularCftData where
  fiParameter : Real
  glsmChargeAssignmentTwoPositiveTwoNegativeUsed : Bool
  twoSmallResolutionsByFiSignUsed : Bool
  dualTwistedSuperpotentialDescriptionUsed : Bool
  conifoldPointRunawayDirectionAndExtraLightModesUsed : Bool
  nTwoLiouvilleInfraredDescriptionAtKOneUsed : Bool

/-- Section 19.5.5 package:
singular conifold CFT from GLSM and its Liouville effective limit. -/
def ConifoldSingularCftPackage (data : ConifoldSingularCftData) : Prop :=
  data.glsmChargeAssignmentTwoPositiveTwoNegativeUsed = true /\
  data.twoSmallResolutionsByFiSignUsed = true /\
  data.dualTwistedSuperpotentialDescriptionUsed = true /\
  data.conifoldPointRunawayDirectionAndExtraLightModesUsed = true /\
  data.nTwoLiouvilleInfraredDescriptionAtKOneUsed = true

/-- Assumed Section 19.5.5 singular-conifold CFT package. -/
theorem conifold_singular_cft_package
    (data : ConifoldSingularCftData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConifoldSingularCftGlsmLiouvilleLimit
      (ConifoldSingularCftPackage data)) :
    ConifoldSingularCftPackage data := by
  exact h_phys

/-- M-theory orbifold-singularity data from the `C^2/Z_k` locus. -/
structure MTheoryOrbifoldSingularityData where
  orbifoldOrder : Nat
  elevenDimensionalPlanckMass : Real
  sevenDimensionalGaugeCoupling : Real
  mTheoryLimitOfCoincidentD6BranesUsed : Bool
  localizedSevenDimensionalSUkGaugeSectorUsed : Bool
  gaugeCouplingIndependentOfMTheoryCircleRadiusUsed : Bool
  instantonStringToM2IdentificationUsed : Bool
  m2TensionMatchesInstantonActionUsed : Bool

/-- Section 19.6.1 package:
M-theory `C^2/Z_k` singularity and localized 7D gauge-sector dictionary. -/
def MTheoryOrbifoldSingularityPackage
    (data : MTheoryOrbifoldSingularityData) : Prop :=
  data.orbifoldOrder > 1 /\
  data.elevenDimensionalPlanckMass > 0 /\
  data.sevenDimensionalGaugeCoupling > 0 /\
  data.mTheoryLimitOfCoincidentD6BranesUsed = true /\
  data.localizedSevenDimensionalSUkGaugeSectorUsed = true /\
  data.gaugeCouplingIndependentOfMTheoryCircleRadiusUsed = true /\
  data.instantonStringToM2IdentificationUsed = true /\
  data.m2TensionMatchesInstantonActionUsed = true

/-- Assumed Section 19.6.1 M-theory orbifold-singularity package. -/
theorem m_theory_orbifold_singularity_package
    (data : MTheoryOrbifoldSingularityData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringMTheoryOrbifoldSingularityGaugeSector
      (MTheoryOrbifoldSingularityPackage data)) :
    MTheoryOrbifoldSingularityPackage data := by
  exact h_phys

/-- `G_2` cone smoothing data and three-branch geometric transition structure. -/
structure MTheoryGTwoConeData where
  coneScale : Real
  cThreePeriodAngle : Real
  gTwoHolonomyFromCovariantlyConstantSpinorUsed : Bool
  associativeAndCoassociativeClosedFormsUsed : Bool
  coneOverS3TimesS3QuotientGeometryUsed : Bool
  trialityPermutationSymmetryOnThreeCyclesUsed : Bool
  threeSmoothBranchesByFillingDistinctCyclesUsed : Bool
  complexModulusCombinesVolumeAndCThreePeriodUsed : Bool
  m2InstantonActionAsMinusTwoPiITUsed : Bool

/-- Section 19.6.2 package:
`G_2` cone geometry, triality-related smooth branches, and complex modulus data. -/
def MTheoryGTwoConePackage (data : MTheoryGTwoConeData) : Prop :=
  data.coneScale > 0 /\
  data.gTwoHolonomyFromCovariantlyConstantSpinorUsed = true /\
  data.associativeAndCoassociativeClosedFormsUsed = true /\
  data.coneOverS3TimesS3QuotientGeometryUsed = true /\
  data.trialityPermutationSymmetryOnThreeCyclesUsed = true /\
  data.threeSmoothBranchesByFillingDistinctCyclesUsed = true /\
  data.complexModulusCombinesVolumeAndCThreePeriodUsed = true /\
  data.m2InstantonActionAsMinusTwoPiITUsed = true

/-- Assumed Section 19.6.2 `G_2` cone/branch package. -/
theorem m_theory_g_two_cone_package
    (data : MTheoryGTwoConeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringMTheoryGTwoConeBranchesAssociativeCycles
      (MTheoryGTwoConePackage data)) :
    MTheoryGTwoConePackage data := by
  exact h_phys

/-- Quantum moduli-space data for asymptotically conical M-theory vacua. -/
structure MTheoryQuantumModuliData where
  eta1 : Complex
  eta2 : Complex
  eta3 : Complex
  asymptoticMetricAndCThreePeriodsDefineEtaUsed : Bool
  anomalyShiftedPhaseConstraintUsed : Bool
  trialityInvarianceConstraintsUsed : Bool
  quantumCurveEquationUsed : Bool
  smoothConnectionOfThreeSemiclassicalBranchesUsed : Bool

/-- Section 19.6.3 package:
triality-compatible quantum moduli curve for asymptotically conical vacua. -/
def MTheoryQuantumModuliPackage (data : MTheoryQuantumModuliData) : Prop :=
  data.eta1 * data.eta2 * data.eta3 = (-1 : Complex) /\
  data.eta2 * (1 - data.eta3) = (1 : Complex) /\
  data.asymptoticMetricAndCThreePeriodsDefineEtaUsed = true /\
  data.anomalyShiftedPhaseConstraintUsed = true /\
  data.trialityInvarianceConstraintsUsed = true /\
  data.quantumCurveEquationUsed = true /\
  data.smoothConnectionOfThreeSemiclassicalBranchesUsed = true

/-- Assumed Section 19.6.3 M-theory quantum-moduli-curve package. -/
theorem m_theory_quantum_moduli_package
    (data : MTheoryQuantumModuliData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringMTheoryQuantumModuliCurveTrialityInvariant
      (MTheoryQuantumModuliPackage data)) :
    MTheoryQuantumModuliPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
