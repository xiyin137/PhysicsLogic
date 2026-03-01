import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Super-Polyakov gauge-fixed data package in the superconformal gauge.
This abstracts the equations around `S[g, chi, X, psi]`, local worldsheet SUSY,
super-Weyl symmetry, and the free `(X, psi)` CFT reduction. -/
structure SuperPolyakovGaugeData where
  localSusyVariation : ℂ
  superWeylVariation : ℂ
  conformalGaugeAction : ℂ
  freeMatterAction : ℂ
  spacetimeDimension : ℕ
  matterCentralCharge : ℚ

/-- Super-Polyakov package:
local SUSY and super-Weyl invariance hold, conformal gauge reduces to free fields,
and the matter central charge obeys `c_m = (3/2) D`. -/
def SuperPolyakovGaugePackage (data : SuperPolyakovGaugeData) : Prop :=
  data.localSusyVariation = 0 ∧
  data.superWeylVariation = 0 ∧
  data.conformalGaugeAction = data.freeMatterAction ∧
  data.matterCentralCharge = (3 / 2 : ℚ) * (data.spacetimeDimension : ℚ)

/-- Assumed super-Polyakov gauge package from Section 6.1. -/
theorem super_polyakov_gauge_package
    (data : SuperPolyakovGaugeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringPolyakovGaugePackage
      (SuperPolyakovGaugePackage data)) :
    SuperPolyakovGaugePackage data := by
  exact h_phys

/-- Superconformal-ghost data for the `(bc)(beta gamma)` system. -/
structure SuperconformalGhostData where
  betaGammaAction : ℂ
  flatGaugeAction : ℂ
  betaGammaOpeSign : ℤ
  bcCentralCharge : ℤ
  betaGammaCentralCharge : ℤ
  totalGhostCentralCharge : ℤ
  ghostSupercurrent : ℂ

/-- Ghost-system package:
flat-gauge action reduction, `beta(z) gamma(0) ~ -1/z`, and total ghost
central charge `c_gh = -15`. -/
def SuperconformalGhostPackage (data : SuperconformalGhostData) : Prop :=
  data.betaGammaAction = data.flatGaugeAction ∧
  data.betaGammaOpeSign = -1 ∧
  data.bcCentralCharge = -26 ∧
  data.betaGammaCentralCharge = 11 ∧
  data.totalGhostCentralCharge = data.bcCentralCharge + data.betaGammaCentralCharge ∧
  data.totalGhostCentralCharge = -15

/-- Assumed superconformal-ghost package from Section 6.2. -/
theorem superconformal_ghost_package
    (data : SuperconformalGhostData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringGhostSystemPackage
      (SuperconformalGhostPackage data)) :
    SuperconformalGhostPackage data := by
  exact h_phys

/-- Picture-number and ghost-state data in the `(phi, eta, xi)` description. -/
structure PictureNumberData where
  genus : ℕ
  ghostChargeViolation : ℤ
  nsCanonicalPicture : ℤ
  ramondCanonicalPicture : ℚ
  etaZeroConstraint : Bool

/-- Picture-number package:
`eta_0`-constraint for `H'[A]`, anomaly `Delta q = 2g-2`,
and canonical NS/R pictures `-1` and `-1/2`. -/
def PictureNumberPackage (data : PictureNumberData) : Prop :=
  data.etaZeroConstraint = true ∧
  data.ghostChargeViolation = 2 * (data.genus : ℤ) - 2 ∧
  data.nsCanonicalPicture = -1 ∧
  data.ramondCanonicalPicture = (-1 / 2 : ℚ)

/-- Assumed picture-number/ghost-state package from Section 6.3. -/
theorem picture_number_package
    (data : PictureNumberData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringPictureNumberPackage
      (PictureNumberPackage data)) :
    PictureNumberPackage data := by
  exact h_phys

/-- Type-II choices for chiral GSO projection. -/
inductive TypeIIVariant where
  | iia
  | iib

/-- Chiral GSO projection data for holomorphic/anti-holomorphic sectors. -/
structure TypeIIGsoProjectionData where
  holomorphicGso : Bool
  antiholomorphicGso : Bool
  antiholomorphicGsoPrime : Bool

/-- Type-II GSO package:
IIA uses `(-)^F = (-)^F'~ = 1`, IIB uses `(-)^F = (-)^F~ = 1`. -/
def TypeIIGsoProjectionPackage
    (variant : TypeIIVariant) (data : TypeIIGsoProjectionData) : Prop :=
  data.holomorphicGso = true ∧
    match variant with
    | .iia => data.antiholomorphicGsoPrime = true
    | .iib => data.antiholomorphicGso = true

/-- Assumed type-II GSO projection package from Section 6.4. -/
theorem type_ii_gso_projection_package
    (variant : TypeIIVariant)
    (data : TypeIIGsoProjectionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringTypeIIGsoProjection
      (TypeIIGsoProjectionPackage variant data)) :
    TypeIIGsoProjectionPackage variant data := by
  exact h_phys

/-- BRST superfield/current and mode-algebra data. -/
structure SuperBRSTCurrentData where
  superfieldRules : Bool
  currentRules : Bool
  oscillatorRules : Bool

/-- BRST package:
superfield transformations, BRST current expressions, and mode relations
(`{Q_B,b_n}=L_n`, `[Q_B,beta_r]=-(1/2)G_r`). -/
def SuperBRSTCurrentPackage (data : SuperBRSTCurrentData) : Prop :=
  data.superfieldRules = true ∧
  data.currentRules = true ∧
  data.oscillatorRules = true

/-- Assumed BRST current package from Section 6.5. -/
theorem super_brst_current_package
    (data : SuperBRSTCurrentData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringBrstCurrentPackage
      (SuperBRSTCurrentPackage data)) :
    SuperBRSTCurrentPackage data := by
  exact h_phys

/-- Abstract BRST complex used for superstring cohomology interfaces. -/
structure SuperBRSTComplex where
  State : Type
  zero : State
  Q : State → State

/-- Nilpotency interface for `Q_B`. -/
def SuperBRSTNilpotent (C : SuperBRSTComplex) : Prop :=
  ∀ ψ : C.State, C.Q (C.Q ψ) = C.zero

/-- Critical-dimension nilpotency condition:
for `D = 10`, the BRST charge is nilpotent. -/
def SuperBRSTNilpotentInCriticalDimension
    (dimension : ℕ) (C : SuperBRSTComplex) : Prop :=
  dimension = 10 → SuperBRSTNilpotent C

/-- Assumed BRST nilpotency in the critical superstring dimension. -/
theorem super_brst_nilpotency_critical
    (dimension : ℕ)
    (C : SuperBRSTComplex)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringBrstNilpotencyCritical
      (SuperBRSTNilpotentInCriticalDimension dimension C)) :
    SuperBRSTNilpotentInCriticalDimension dimension C := by
  exact h_phys

/-- Siegel constraints for superstring states, including Ramond `beta_0` conditions. -/
structure SuperstringSiegelConstraintData where
  b0Left : ℂ
  b0Right : ℂ
  beta0Left : ℂ
  beta0Right : ℂ
  inRamondLeft : Bool
  inRamondRight : Bool

/-- Superstring Siegel package:
`b_0 = b~_0 = 0`, and `beta_0` constraints in Ramond sectors. -/
def SuperstringSiegelConstraintPackage
    (data : SuperstringSiegelConstraintData) : Prop :=
  data.b0Left = 0 ∧
  data.b0Right = 0 ∧
  (if data.inRamondLeft then data.beta0Left = 0 else True) ∧
  (if data.inRamondRight then data.beta0Right = 0 else True)

/-- Assumed superstring Siegel-constraint package from Section 6.6. -/
theorem superstring_siegel_constraint_package
    (data : SuperstringSiegelConstraintData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringSiegelConstraintPackage
      (SuperstringSiegelConstraintPackage data)) :
    SuperstringSiegelConstraintPackage data := by
  exact h_phys

/-- BRST closed/exact state predicates in the superstring complex. -/
def SuperBRSTClosed (C : SuperBRSTComplex) (ψ : C.State) : Prop :=
  C.Q ψ = C.zero

def SuperBRSTExact (C : SuperBRSTComplex) (ψ : C.State) : Prop :=
  ∃ χ : C.State, C.Q χ = ψ

/-- Physical-state data for superstring BRST cohomology. -/
structure SuperstringPhysicalStateData where
  complex : SuperBRSTComplex
  isPhysical : complex.State → Prop
  satisfiesSiegel : complex.State → Prop

/-- Physical-state package:
physical states are BRST cohomology classes with Siegel constraints. -/
def SuperstringPhysicalCohomologyPackage
    (data : SuperstringPhysicalStateData) : Prop :=
  ∀ ψ : data.complex.State,
    data.isPhysical ψ ↔
      (SuperBRSTClosed data.complex ψ ∧
        ¬ SuperBRSTExact data.complex ψ ∧
        data.satisfiesSiegel ψ)

/-- Assumed BRST-cohomology characterization of physical superstring states. -/
theorem superstring_physical_cohomology_package
    (data : SuperstringPhysicalStateData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringPhysicalCohomologyPackage
      (SuperstringPhysicalCohomologyPackage data)) :
    SuperstringPhysicalCohomologyPackage data := by
  exact h_phys

/-- OCQ representative data in NS and R sectors. -/
structure SuperstringOcqRepresentativeData where
  nsMatterWeight : ℚ
  nsRepresentativeAgreement : Bool
  ramondHighestWeightConstraints : Bool
  ramondRepresentativeAgreement : Bool

/-- OCQ representative package:
NS representatives `c e^{-phi} V` with `h(V)=1/2`,
and R representatives `c e^{-phi/2} S` with super-Virasoro highest-weight data. -/
def SuperstringOcqRepresentativePackage
    (data : SuperstringOcqRepresentativeData) : Prop :=
  data.nsMatterWeight = (1 / 2 : ℚ) ∧
  data.nsRepresentativeAgreement = true ∧
  data.ramondHighestWeightConstraints = true ∧
  data.ramondRepresentativeAgreement = true

/-- Assumed OCQ representative package for superstring BRST cohomology. -/
theorem superstring_ocq_representative_package
    (data : SuperstringOcqRepresentativeData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringOcqRepresentativePackage
      (SuperstringOcqRepresentativePackage data)) :
    SuperstringOcqRepresentativePackage data := by
  exact h_phys

/-- Superstring mass-shell data after GSO projection. -/
structure SuperstringMassSpectrumData where
  alphaPrime : ℝ
  massSq : ℝ
  leftLevel : ℕ
  rightLevel : ℕ

/-- Mass-spectrum package:
`L_0 = L~_0 = 0`, level matching, and `m^2 = 4N/alpha'` with integer `N >= 0`. -/
def SuperstringMassSpectrumPackage
    (data : SuperstringMassSpectrumData) : Prop :=
  data.alphaPrime > 0 ∧
  data.leftLevel = data.rightLevel ∧
  data.massSq = (4 / data.alphaPrime) * (data.leftLevel : ℝ)

/-- Assumed superstring mass-spectrum package from Section 6.6.2. -/
theorem superstring_mass_spectrum_package
    (data : SuperstringMassSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringMassSpectrumPackage
      (SuperstringMassSpectrumPackage data)) :
    SuperstringMassSpectrumPackage data := by
  exact h_phys

/-- Massless `(NS,NS)` data. -/
structure MasslessNSNSData where
  momentumSq : ℝ
  leftTransversality : Bool
  rightTransversality : Bool

def MasslessNSNSPackage (data : MasslessNSNSData) : Prop :=
  data.momentumSq = 0 ∧
  data.leftTransversality = true ∧
  data.rightTransversality = true

/-- Massless `(R,R)` data. -/
structure MasslessRRData where
  momentumSq : ℝ
  leftDiracConstraint : Bool
  rightDiracConstraint : Bool

def MasslessRRPackage (data : MasslessRRData) : Prop :=
  data.momentumSq = 0 ∧
  data.leftDiracConstraint = true ∧
  data.rightDiracConstraint = true

/-- Massless `(R,NS)` and `(NS,R)` fermionic-sector data. -/
structure MasslessFermionicData where
  momentumSq : ℝ
  transversalityAndDirac : Bool
  gaugeRedundancy : Bool

def MasslessFermionicPackage (data : MasslessFermionicData) : Prop :=
  data.momentumSq = 0 ∧
  data.transversalityAndDirac = true ∧
  data.gaugeRedundancy = true

/-- Combined massless-spectrum package for type-II superstrings. -/
structure SuperstringMasslessSectorData where
  nsns : MasslessNSNSData
  rr : MasslessRRData
  fermionic : MasslessFermionicData

def SuperstringMasslessSectorPackage
    (data : SuperstringMasslessSectorData) : Prop :=
  MasslessNSNSPackage data.nsns ∧
  MasslessRRPackage data.rr ∧
  MasslessFermionicPackage data.fermionic

/-- Assumed massless-sector package from Section 6.6.2. -/
theorem superstring_massless_sector_package
    (data : SuperstringMasslessSectorData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringMasslessSectorPackage
      (SuperstringMasslessSectorPackage data)) :
    SuperstringMasslessSectorPackage data := by
  exact h_phys

/-- Spacetime-supersymmetry current/algebra data from worldsheet construction. -/
structure SpacetimeSupersymmetryAlgebraData where
  alphaPrime : ℝ
  leftAnticommutator : ℂ
  rightAnticommutator : ℂ
  gammaMomentumContraction : ℂ
  leftRightAnticommutator : ℂ

/-- Spacetime-supersymmetry package (up to picture-raising):
`{Q,Q} = (sqrt(alpha')/4) Gamma.P`, same for right movers, and
left-right supercharges anticommute. -/
def SpacetimeSupersymmetryAlgebraPackage
    (data : SpacetimeSupersymmetryAlgebraData) : Prop :=
  data.alphaPrime > 0 ∧
  data.leftAnticommutator =
    (Real.sqrt data.alphaPrime / 4 : ℂ) * data.gammaMomentumContraction ∧
  data.rightAnticommutator =
    (Real.sqrt data.alphaPrime / 4 : ℂ) * data.gammaMomentumContraction ∧
  data.leftRightAnticommutator = 0

/-- Assumed spacetime-supersymmetry algebra package from Section 6.6.3. -/
theorem spacetime_supersymmetry_algebra_package
    (data : SpacetimeSupersymmetryAlgebraData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringSpacetimeSusyAlgebra
      (SpacetimeSupersymmetryAlgebraPackage data)) :
    SpacetimeSupersymmetryAlgebraPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
