import PhysicsLogic.Assumptions
import PhysicsLogic.StringTheory.EffectiveString
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Bosonic D-brane boundary-condition data. -/
structure BosonicDbraneBoundaryData where
  spacetimeDimension : Nat
  braneSpatialDimension : Nat
  conformalStressTensorBoundaryCondition : Bool
  ghostBoundaryConditionsPreserveBrst : Bool
  neumannDirichletSplitImplemented : Bool
  doublingTrickAnalyticContinuation : Bool
  worldsheetDiffeomorphismInvariantBoundary : Bool

/-- Bosonic D-brane boundary package:
conformal/BRST-preserving boundary conditions with ND split and doubling-trick
realization in a bosonic Weyl-anomaly-canceling background. -/
def BosonicDbraneBoundaryPackage (data : BosonicDbraneBoundaryData) : Prop :=
  BosonicWeylAnomalyCancellation data.spacetimeDimension /\
  data.braneSpatialDimension < data.spacetimeDimension /\
  data.conformalStressTensorBoundaryCondition = true /\
  data.ghostBoundaryConditionsPreserveBrst = true /\
  data.neumannDirichletSplitImplemented = true /\
  data.doublingTrickAnalyticContinuation = true /\
  data.worldsheetDiffeomorphismInvariantBoundary = true

/-- Assumed bosonic D-brane boundary-condition package from Section 12.1. -/
theorem bosonic_dbrane_boundary_package
    (data : BosonicDbraneBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneBosonicBoundaryConditions
      (BosonicDbraneBoundaryPackage data)) :
    BosonicDbraneBoundaryPackage data := by
  exact h_phys

/-- Bosonic D-brane boundary-state data. -/
structure BosonicDbraneBoundaryStateData where
  boundaryStateExists : Bool
  oscillatorGluingConditionsSatisfied : Bool
  ghostGluingConditionsSatisfied : Bool
  cylinderOpenClosedDualityFixesNormalization : Bool
  momentumZeroModeLocalizationOnTransversePosition : Bool

/-- Bosonic D-brane boundary-state package:
boundary-state gluing conditions and normalization fixed by cylinder
open/closed channel duality. -/
def BosonicDbraneBoundaryStatePackage
    (data : BosonicDbraneBoundaryStateData) : Prop :=
  data.boundaryStateExists = true /\
  data.oscillatorGluingConditionsSatisfied = true /\
  data.ghostGluingConditionsSatisfied = true /\
  data.cylinderOpenClosedDualityFixesNormalization = true /\
  data.momentumZeroModeLocalizationOnTransversePosition = true

/-- Assumed bosonic D-brane boundary-state package from Section 12.1. -/
theorem bosonic_dbrane_boundary_state_package
    (data : BosonicDbraneBoundaryStateData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneBosonicBoundaryStateNormalization
      (BosonicDbraneBoundaryStatePackage data)) :
    BosonicDbraneBoundaryStatePackage data := by
  exact h_phys

/-- Open-bosonic-string spectrum data on a D-brane. -/
structure OpenBosonicDbraneSpectrumData where
  alphaPrime : Real
  momentumParallelSq : Real
  oscillatorLevel : Nat
  massShellResidual : Real
  siegelConstraintUsed : Bool
  brstCohomologyUsed : Bool
  levelZeroTachyonPresent : Bool
  levelOneVectorAndScalarsPresent : Bool
  levelOneGaugeRedundancyPresent : Bool

/-- Open bosonic D-brane spectrum package:
mass-shell relation `alpha' k_parallel^2 + N - 1 = 0`, tachyon at level zero,
and massless vector/scalar multiplet data at level one. -/
def OpenBosonicDbraneSpectrumPackage
    (data : OpenBosonicDbraneSpectrumData) : Prop :=
  data.alphaPrime > 0 /\
  data.massShellResidual =
    data.alphaPrime * data.momentumParallelSq + (data.oscillatorLevel : Real) - 1 /\
  data.massShellResidual = 0 /\
  data.siegelConstraintUsed = true /\
  data.brstCohomologyUsed = true /\
  data.levelZeroTachyonPresent = true /\
  data.levelOneVectorAndScalarsPresent = true /\
  data.levelOneGaugeRedundancyPresent = true

/-- Assumed open-bosonic D-brane spectrum package from Section 12.1.1. -/
theorem open_bosonic_dbrane_spectrum_package
    (data : OpenBosonicDbraneSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneOpenBosonicSpectrum
      (OpenBosonicDbraneSpectrumPackage data)) :
    OpenBosonicDbraneSpectrumPackage data := by
  exact h_phys

/-- Boundary-marginal open-string deformation data on a D-brane worldvolume. -/
structure DbraneWorldvolumeDeformationData where
  gaugeBoundaryCouplingPresent : Bool
  transverseScalarBoundaryCouplingPresent : Bool
  linearizedBoundaryMarginalityConstraintsUsed : Bool
  constantScalarBackgroundShiftsBranePosition : Bool
  openStringEndpointCarriesOppositeCharges : Bool

/-- D-brane worldvolume deformation package:
massless open-string modes induce gauge/scalar boundary deformations, with
constant transverse scalar profile shifting D-brane position. -/
def DbraneWorldvolumeDeformationPackage
    (data : DbraneWorldvolumeDeformationData) : Prop :=
  data.gaugeBoundaryCouplingPresent = true /\
  data.transverseScalarBoundaryCouplingPresent = true /\
  data.linearizedBoundaryMarginalityConstraintsUsed = true /\
  data.constantScalarBackgroundShiftsBranePosition = true /\
  data.openStringEndpointCarriesOppositeCharges = true

/-- Assumed D-brane worldvolume deformation package from Section 12.1.2. -/
theorem dbrane_worldvolume_deformation_package
    (data : DbraneWorldvolumeDeformationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneBoundaryMarginalDeformations
      (DbraneWorldvolumeDeformationPackage data)) :
    DbraneWorldvolumeDeformationPackage data := by
  exact h_phys

/-- Chan-Paton and gauge-enhancement data for multiple D-branes. -/
structure DbraneChanPatonData where
  stackSize : Nat
  alphaPrime : Real
  transverseSeparation : Real
  wBosonMass : Real
  chanPatonMatrixFactorization : Bool
  stretchedStringsCarryBifundamentalCharges : Bool
  coincidentLimitEnhancesGaugeGroupToUStackSize : Bool

/-- Chan-Paton package:
`H_(B^n,B^n) ~ H_(B,B) tensor Mat(n)` and W-boson mass
`m = |Delta x|/(2 pi alpha')` with `U(n)` enhancement at coincidence. -/
def DbraneChanPatonPackage (data : DbraneChanPatonData) : Prop :=
  data.stackSize > 0 /\
  data.alphaPrime > 0 /\
  data.wBosonMass = |data.transverseSeparation| / (2 * Real.pi * data.alphaPrime) /\
  data.chanPatonMatrixFactorization = true /\
  data.stretchedStringsCarryBifundamentalCharges = true /\
  data.coincidentLimitEnhancesGaugeGroupToUStackSize = true

/-- Assumed Chan-Paton/gauge-enhancement package from Section 12.1.3. -/
theorem dbrane_chan_paton_package
    (data : DbraneChanPatonData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneChanPatonGaugeEnhancement
      (DbraneChanPatonPackage data)) :
    DbraneChanPatonPackage data := by
  exact h_phys

/-- BPS type-II D-brane boundary-condition and supersymmetry data. -/
structure TypeIIBpsDbraneBoundaryData where
  braneSpatialDimension : Nat
  superconformalBoundaryConditionsSatisfied : Bool
  worldsheetFermionGluingSatisfied : Bool
  ramondSpinFieldBoundaryConditionChosen : Bool
  iiaOrIibParityConstraintSatisfied : Bool
  preservesHalfSpacetimeSupercharges : Bool

/-- Type-II BPS D-brane boundary package:
superconformal gluing plus Ramond-sector boundary conditions preserving half of
spacetime supersymmetry. -/
def TypeIIBpsDbraneBoundaryPackage
    (data : TypeIIBpsDbraneBoundaryData) : Prop :=
  data.braneSpatialDimension < 10 /\
  data.superconformalBoundaryConditionsSatisfied = true /\
  data.worldsheetFermionGluingSatisfied = true /\
  data.ramondSpinFieldBoundaryConditionChosen = true /\
  data.iiaOrIibParityConstraintSatisfied = true /\
  data.preservesHalfSpacetimeSupercharges = true

/-- Assumed type-II BPS D-brane boundary/supersymmetry package from Section 12.2. -/
theorem type_ii_bps_dbrane_boundary_package
    (data : TypeIIBpsDbraneBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneTypeIIBpsBoundarySupersymmetry
      (TypeIIBpsDbraneBoundaryPackage data)) :
    TypeIIBpsDbraneBoundaryPackage data := by
  exact h_phys

/-- Open-superstring spectrum data on a BPS type-II D-brane. -/
structure OpenSuperstringDbraneSpectrumData where
  alphaPrime : Real
  momentumParallelSq : Real
  oscillatorWeight : Nat
  massShellResidual : Real
  nsMasslessVectorAndTransverseScalarsPresent : Bool
  rMasslessGoldstinoMultipletPresent : Bool
  gsoProjectionRemovesNsTachyon : Bool
  brstAndSiegelConstraintsUsed : Bool

/-- Open superstring D-brane spectrum package:
mass shell `alpha' k^2 + N = 0` with GSO projection removing the NS tachyon and
producing massless NS/R worldvolume multiplets. -/
def OpenSuperstringDbraneSpectrumPackage
    (data : OpenSuperstringDbraneSpectrumData) : Prop :=
  data.alphaPrime > 0 /\
  data.massShellResidual =
    data.alphaPrime * data.momentumParallelSq + (data.oscillatorWeight : Real) /\
  data.massShellResidual = 0 /\
  data.nsMasslessVectorAndTransverseScalarsPresent = true /\
  data.rMasslessGoldstinoMultipletPresent = true /\
  data.gsoProjectionRemovesNsTachyon = true /\
  data.brstAndSiegelConstraintsUsed = true

/-- Assumed open-superstring D-brane spectrum package from Section 12.2.1. -/
theorem open_superstring_dbrane_spectrum_package
    (data : OpenSuperstringDbraneSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneOpenSuperstringSpectrum
      (OpenSuperstringDbraneSpectrumPackage data)) :
    OpenSuperstringDbraneSpectrumPackage data := by
  exact h_phys

/-- Boundary-state and RR-charge data for BPS type-II D-branes. -/
structure BpsDbraneBoundaryStateRrData where
  nsnsBoundaryStateComponentPresent : Bool
  rrBoundaryStateComponentPresent : Bool
  spinStructureAverageImposesGso : Bool
  rrChargeNonzeroForBpsDbrane : Bool
  antiDbraneFlipsRrChargeSign : Bool
  cylinderModularCrossingRelationsSatisfied : Bool

/-- BPS boundary-state RR package:
BPS D-branes carry NSNS and RR boundary-state components, satisfy modular
crossing consistency, and source RR gauge potentials with orientation sign. -/
def BpsDbraneBoundaryStateRrPackage
    (data : BpsDbraneBoundaryStateRrData) : Prop :=
  data.nsnsBoundaryStateComponentPresent = true /\
  data.rrBoundaryStateComponentPresent = true /\
  data.spinStructureAverageImposesGso = true /\
  data.rrChargeNonzeroForBpsDbrane = true /\
  data.antiDbraneFlipsRrChargeSign = true /\
  data.cylinderModularCrossingRelationsSatisfied = true

/-- Assumed BPS boundary-state/RR-charge package from Section 12.2.2. -/
theorem bps_dbrane_boundary_state_rr_package
    (data : BpsDbraneBoundaryStateRrData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneBpsBoundaryStateRrCharge
      (BpsDbraneBoundaryStateRrPackage data)) :
    BpsDbraneBoundaryStateRrPackage data := by
  exact h_phys

/-- Non-BPS D-brane construction data from brane-antibrane sectors. -/
structure NonBpsDbraneConstructionData where
  oppositeGsoProjectionInBraneAntibraneSector : Bool
  braneAntibraneOpenStringTachyonPresent : Bool
  projectedNonBpsBoundaryStatePureNsns : Bool
  nonBpsDbraneRrChargeVanishes : Bool
  allSpacetimeSupersymmetriesBroken : Bool
  openStringTachyonSignalsClassicalInstability : Bool

/-- Non-BPS D-brane package:
brane-antibrane projection yields non-BPS D-branes with no RR charge, full SUSY
breaking, and open-string tachyon instability. -/
def NonBpsDbraneConstructionPackage
    (data : NonBpsDbraneConstructionData) : Prop :=
  data.oppositeGsoProjectionInBraneAntibraneSector = true /\
  data.braneAntibraneOpenStringTachyonPresent = true /\
  data.projectedNonBpsBoundaryStatePureNsns = true /\
  data.nonBpsDbraneRrChargeVanishes = true /\
  data.allSpacetimeSupersymmetriesBroken = true /\
  data.openStringTachyonSignalsClassicalInstability = true

/-- Assumed non-BPS D-brane construction package from Section 12.3. -/
theorem non_bps_dbrane_construction_package
    (data : NonBpsDbraneConstructionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneNonBpsConstruction
      (NonBpsDbraneConstructionPackage data)) :
    NonBpsDbraneConstructionPackage data := by
  exact h_phys

/-- Intersecting D-brane spectrum and supersymmetry data. -/
structure IntersectingDbraneNdData where
  alphaPrime : Real
  ndDirectionCount : Nat
  nsIntersectionMassSq : Real
  rIntersectionFermionsMassless : Bool
  ndCongruentZeroModFourPreservesQuarterBps : Bool
  ndCongruentTwoModFourBreaksSupersymmetry : Bool

/-- Intersecting D-brane ND package:
`m_NS^2 = ((d_ND/8)-1/2)/alpha'` with massless R fermions at intersections, and
SUSY determined by `d_ND mod 4`. -/
def IntersectingDbraneNdPackage (data : IntersectingDbraneNdData) : Prop :=
  data.alphaPrime > 0 /\
  data.ndDirectionCount % 2 = 0 /\
  data.nsIntersectionMassSq =
    ((data.ndDirectionCount : Real) / 8 - (1 / 2 : Real)) / data.alphaPrime /\
  data.rIntersectionFermionsMassless = true /\
  data.ndCongruentZeroModFourPreservesQuarterBps = true /\
  data.ndCongruentTwoModFourBreaksSupersymmetry = true

/-- Assumed intersecting D-brane ND-spectrum package from Section 12.4.1. -/
theorem intersecting_dbrane_nd_package
    (data : IntersectingDbraneNdData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneIntersectingNdSpectrum
      (IntersectingDbraneNdPackage data)) :
    IntersectingDbraneNdPackage data := by
  exact h_phys

/-- D-branes-at-angles data for low-lying open-string modes and BPS condition. -/
structure DbranesAtAnglesData where
  alphaPrime : Real
  thetaOne : Real
  thetaTwo : Real
  d1d1PrimeLowestNsMassSq : Real
  d2d2PrimeModeOneMassSq : Real
  d2d2PrimeModeTwoMassSq : Real
  equalAnglesImpliesNoTachyon : Bool
  equalAnglesImpliesQuarterBps : Bool

/-- D-branes-at-angles package:
for D1-D1' the lowest NS mode has `m^2 = -theta/(2 pi alpha')`; for D2-D2'
the two low NS modes have masses proportional to `theta_1-theta_2`, and
`theta_1 = theta_2` gives tachyon-free quarter-BPS configuration. -/
def DbranesAtAnglesPackage (data : DbranesAtAnglesData) : Prop :=
  data.alphaPrime > 0 /\
  0 < data.thetaOne /\ data.thetaOne < Real.pi /\
  0 < data.thetaTwo /\ data.thetaTwo < Real.pi /\
  data.d1d1PrimeLowestNsMassSq =
    -data.thetaOne / (2 * Real.pi * data.alphaPrime) /\
  data.d2d2PrimeModeOneMassSq =
    (data.thetaOne - data.thetaTwo) / (2 * Real.pi * data.alphaPrime) /\
  data.d2d2PrimeModeTwoMassSq =
    (data.thetaTwo - data.thetaOne) / (2 * Real.pi * data.alphaPrime) /\
  data.equalAnglesImpliesNoTachyon = true /\
  data.equalAnglesImpliesQuarterBps = true

/-- Assumed D-branes-at-angles package from Section 12.4.2. -/
theorem dbranes_at_angles_package
    (data : DbranesAtAnglesData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringDbraneAtAnglesStabilityBpsCondition
      (DbranesAtAnglesPackage data)) :
    DbranesAtAnglesPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
