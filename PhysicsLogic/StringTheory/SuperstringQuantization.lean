import PhysicsLogic.Assumptions
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Claim type used for unresolved physics statements in this module. -/
abbrev SuperstringQuantizationClaim := Prop

/-- Endomorphisms of a complex state space. -/
abbrev Endomorphism (State : Type*) [AddCommGroup State] [Module ℂ State] := Module.End ℂ State

/-- Operator commutator on endomorphisms. -/
def opComm {State : Type*} [AddCommGroup State] [Module ℂ State]
    (A B : Endomorphism State) : Endomorphism State :=
  A * B - B * A

/-- Super-Polyakov gauge-fixed data package in the superconformal gauge.
This abstracts the equations around `S[g, chi, X, psi]`, local worldsheet SUSY,
super-Weyl symmetry, and the free `(X, psi)` CFT reduction. -/
structure SuperPolyakovGaugeData (WorldsheetConfig : Type*) where
  localSusyVariationCancels : SuperstringQuantizationClaim
  superWeylVariationCancels : SuperstringQuantizationClaim
  conformalGaugeAction : WorldsheetConfig → ComplexActionValue
  freeMatterAction : WorldsheetConfig → ComplexActionValue
  spacetimeDimension : ℕ
  matterCentralCharge : ℚ

/-- Super-Polyakov package:
local SUSY and super-Weyl invariance hold, conformal gauge reduces to free fields,
and the matter central charge obeys `c_m = (3/2) D`. -/
def SuperPolyakovGaugePackage {WorldsheetConfig : Type*}
    (data : SuperPolyakovGaugeData WorldsheetConfig) : Prop :=
  data.localSusyVariationCancels ∧
  data.superWeylVariationCancels ∧
  (∀ cfg : WorldsheetConfig, data.conformalGaugeAction cfg = data.freeMatterAction cfg) ∧
  data.matterCentralCharge = (3 / 2 : ℚ) * (data.spacetimeDimension : ℚ)

/-- Assumed super-Polyakov gauge package from Section 6.1. -/
theorem super_polyakov_gauge_package
    {WorldsheetConfig : Type*}
    (data : SuperPolyakovGaugeData WorldsheetConfig)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringPolyakovGaugePackage
      (SuperPolyakovGaugePackage data)) :
    SuperPolyakovGaugePackage data := by
  exact h_phys

/-- Superconformal-ghost data for the `(bc)(beta gamma)` system. -/
structure SuperconformalGhostData (GhostConfig : Type*) where
  betaGammaAction : GhostConfig → ComplexActionValue
  flatGaugeAction : GhostConfig → ComplexActionValue
  betaGammaOpeSign : ℤ
  bcCentralCharge : ℤ
  betaGammaCentralCharge : ℤ
  totalGhostCentralCharge : ℤ
  ghostSupercurrentExists : SuperstringQuantizationClaim

/-- Ghost-system package:
flat-gauge action reduction, `beta(z) gamma(0) ~ -1/z`, and total ghost
central charge `c_gh = -15`. -/
def SuperconformalGhostPackage {GhostConfig : Type*}
    (data : SuperconformalGhostData GhostConfig) : Prop :=
  (∀ cfg : GhostConfig, data.betaGammaAction cfg = data.flatGaugeAction cfg) ∧
  data.betaGammaOpeSign = -1 ∧
  data.bcCentralCharge = -26 ∧
  data.betaGammaCentralCharge = 11 ∧
  data.totalGhostCentralCharge = data.bcCentralCharge + data.betaGammaCentralCharge ∧
  data.totalGhostCentralCharge = -15

/-- Assumed superconformal-ghost package from Section 6.2. -/
theorem superconformal_ghost_package
    {GhostConfig : Type*}
    (data : SuperconformalGhostData GhostConfig)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringGhostSystemPackage
      (SuperconformalGhostPackage data)) :
    SuperconformalGhostPackage data := by
  exact h_phys

/-- Picture-number and ghost-state data in the `(phi, eta, xi)` description. -/
structure PictureNumberData (GhostState : Type*) where
  genus : ℕ
  ghostChargeViolation : ℤ
  nsCanonicalPicture : ℤ
  ramondCanonicalPicture : ℚ
  etaZeroMode : GhostState → GhostState
  selectedState : GhostState
  zeroState : GhostState

/-- Picture-number package:
`eta_0`-constraint for `H'[A]`, anomaly `Delta q = 2g-2`,
and canonical NS/R pictures `-1` and `-1/2`. -/
def PictureNumberPackage {GhostState : Type*} (data : PictureNumberData GhostState) : Prop :=
  data.etaZeroMode data.selectedState = data.zeroState ∧
  data.ghostChargeViolation = 2 * (data.genus : ℤ) - 2 ∧
  data.nsCanonicalPicture = -1 ∧
  data.ramondCanonicalPicture = (-1 / 2 : ℚ)

/-- Assumed picture-number/ghost-state package from Section 6.3. -/
theorem picture_number_package
    {GhostState : Type*}
    (data : PictureNumberData GhostState)
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
  holomorphicPhase : ℤ
  antiholomorphicPhase : ℤ
  antiholomorphicPrimePhase : ℤ

/-- Type-II GSO package:
IIA uses `(-)^F = (-)^F'~ = 1`, IIB uses `(-)^F = (-)^F~ = 1`. -/
def TypeIIGsoProjectionPackage
    (variant : TypeIIVariant) (data : TypeIIGsoProjectionData) : Prop :=
  data.holomorphicPhase = 1 ∧
    match variant with
    | .iia => data.antiholomorphicPrimePhase = 1
    | .iib => data.antiholomorphicPhase = 1

/-- Assumed type-II GSO projection package from Section 6.4. -/
theorem type_ii_gso_projection_package
    (variant : TypeIIVariant)
    (data : TypeIIGsoProjectionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringTypeIIGsoProjection
      (TypeIIGsoProjectionPackage variant data)) :
    TypeIIGsoProjectionPackage variant data := by
  exact h_phys

/-- BRST current and mode-algebra data on a state space. -/
structure SuperBRSTCurrentData (State : Type*) [AddCommGroup State] [Module ℂ State] where
  brstCharge : Endomorphism State
  bMode : ℤ → Endomorphism State
  betaMode : ℚ → Endomorphism State
  virasoroMode : ℤ → Endomorphism State
  supercurrentMode : ℚ → Endomorphism State

/-- BRST package:
superfield transformations, BRST current expressions, and mode relations
(`{Q_B,b_n}=L_n`, `[Q_B,beta_r]=-(1/2)G_r`). -/
def SuperBRSTCurrentPackage {State : Type*} [AddCommGroup State] [Module ℂ State]
    (data : SuperBRSTCurrentData State) : Prop :=
  (∀ n : ℤ, opComm data.brstCharge (data.bMode n) = data.virasoroMode n) ∧
  (∀ r : ℚ,
    opComm data.brstCharge (data.betaMode r) = (-(1 / 2 : ℂ)) • data.supercurrentMode r)

/-- Assumed BRST current package from Section 6.5. -/
theorem super_brst_current_package
    {State : Type*} [AddCommGroup State] [Module ℂ State]
    (data : SuperBRSTCurrentData State)
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

/-- Siegel-constraint data for a candidate physical state, including Ramond
`beta_0` conditions. The zero-mode objects are operators on state space rather
than scalar values. -/
structure SuperstringSiegelConstraintData (State : Type*) where
  b0Left : State → State
  b0Right : State → State
  beta0Left : State → State
  beta0Right : State → State
  state : State
  zeroState : State
  inRamondLeftSector : SuperstringQuantizationClaim
  inRamondRightSector : SuperstringQuantizationClaim

/-- Superstring Siegel package:
`b_0 = b~_0 = 0`, and `beta_0` constraints in Ramond sectors. -/
def SuperstringSiegelConstraintPackage {State : Type*}
    (data : SuperstringSiegelConstraintData State) : Prop :=
  data.b0Left data.state = data.zeroState ∧
  data.b0Right data.state = data.zeroState ∧
  (data.inRamondLeftSector → data.beta0Left data.state = data.zeroState) ∧
  (data.inRamondRightSector → data.beta0Right data.state = data.zeroState)

/-- Assumed superstring Siegel-constraint package from Section 6.6. -/
theorem superstring_siegel_constraint_package
    {State : Type*}
    (data : SuperstringSiegelConstraintData State)
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
  nsRepresentativePicture : ℚ
  ramondRepresentativePicture : ℚ
  ramondHighestWeightSatisfiedUpTo : ℕ

/-- OCQ representative package:
NS representatives `c e^{-phi} V` with `h(V)=1/2`,
and R representatives `c e^{-phi/2} S` with super-Virasoro highest-weight data. -/
def SuperstringOcqRepresentativePackage
    (data : SuperstringOcqRepresentativeData) : Prop :=
  data.nsMatterWeight = (1 / 2 : ℚ) ∧
  data.nsRepresentativePicture = -1 ∧
  data.ramondRepresentativePicture = (-1 / 2 : ℚ) ∧
  data.ramondHighestWeightSatisfiedUpTo > 0

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
  alphaPrime : StringSlope
  massSq : MassSquaredScale
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
structure MasslessNSNSData (TransversalityResidual : Type*)
    [Zero TransversalityResidual] where
  momentumSq : MomentumSquaredScale
  leftTransversalityResidual : TransversalityResidual
  rightTransversalityResidual : TransversalityResidual

def MasslessNSNSPackage {TransversalityResidual : Type*}
    [Zero TransversalityResidual]
    (data : MasslessNSNSData TransversalityResidual) : Prop :=
  data.momentumSq = 0 ∧
  data.leftTransversalityResidual = 0 ∧
  data.rightTransversalityResidual = 0

/-- Massless `(R,R)` data. -/
structure MasslessRRData (DiracResidual : Type*) [Zero DiracResidual] where
  momentumSq : MomentumSquaredScale
  leftDiracResidual : DiracResidual
  rightDiracResidual : DiracResidual

def MasslessRRPackage {DiracResidual : Type*} [Zero DiracResidual]
    (data : MasslessRRData DiracResidual) : Prop :=
  data.momentumSq = 0 ∧
  data.leftDiracResidual = 0 ∧
  data.rightDiracResidual = 0

/-- Massless `(R,NS)` and `(NS,R)` fermionic-sector data. -/
structure MasslessFermionicData (ConstraintResidual : Type*)
    [Zero ConstraintResidual] where
  momentumSq : MomentumSquaredScale
  transversalityAndDiracResidual : ConstraintResidual
  gaugeRedundancyResidual : ConstraintResidual

def MasslessFermionicPackage {ConstraintResidual : Type*}
    [Zero ConstraintResidual]
    (data : MasslessFermionicData ConstraintResidual) : Prop :=
  data.momentumSq = 0 ∧
  data.transversalityAndDiracResidual = 0 ∧
  data.gaugeRedundancyResidual = 0

/-- Combined massless-spectrum package for type-II superstrings. -/
structure SuperstringMasslessSectorData
    (TransversalityResidual DiracResidual ConstraintResidual : Type*)
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual] where
  nsns : MasslessNSNSData TransversalityResidual
  rr : MasslessRRData DiracResidual
  fermionic : MasslessFermionicData ConstraintResidual

def SuperstringMasslessSectorPackage
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringMasslessSectorData
      TransversalityResidual DiracResidual ConstraintResidual) : Prop :=
  MasslessNSNSPackage data.nsns ∧
  MasslessRRPackage data.rr ∧
  MasslessFermionicPackage data.fermionic

/-- Assumed massless-sector package from Section 6.6.2. -/
theorem superstring_massless_sector_package
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringMasslessSectorData
      TransversalityResidual DiracResidual ConstraintResidual)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringMasslessSectorPackage
      (SuperstringMasslessSectorPackage data)) :
    SuperstringMasslessSectorPackage data := by
  exact h_phys

/-- Compatibility data tying the level-zero mass formula to the massless sectors. -/
structure SuperstringLevelZeroMasslessCompatibilityData
    (TransversalityResidual DiracResidual ConstraintResidual : Type*)
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual] where
  spectrum : SuperstringMassSpectrumData
  massless : SuperstringMasslessSectorData
    TransversalityResidual DiracResidual ConstraintResidual

/-- Level-zero/massless compatibility package:
the mass formula, massless-sector constraints, and level-zero identification
are imposed simultaneously so all sectors share the same on-shell `p^2=0`. -/
def SuperstringLevelZeroMasslessCompatibilityPackage
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringLevelZeroMasslessCompatibilityData
      TransversalityResidual DiracResidual ConstraintResidual) : Prop :=
  SuperstringMassSpectrumPackage data.spectrum ∧
  SuperstringMasslessSectorPackage data.massless ∧
  data.spectrum.leftLevel = 0 ∧
  data.spectrum.rightLevel = 0 ∧
  data.massless.nsns.momentumSq = data.spectrum.massSq ∧
  data.massless.rr.momentumSq = data.spectrum.massSq ∧
  data.massless.fermionic.momentumSq = data.spectrum.massSq

/-- In the level-zero sector, the superstring mass formula enforces `m^2 = 0`. -/
theorem superstring_level_zero_implies_mass_sq_zero
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringLevelZeroMasslessCompatibilityData
      TransversalityResidual DiracResidual ConstraintResidual)
    (h_pkg : SuperstringLevelZeroMasslessCompatibilityPackage data) :
    data.spectrum.massSq = 0 := by
  rcases h_pkg with ⟨_, h_massless, _, _, h_nsns_link, _, _⟩
  rcases h_massless with ⟨h_nsns_pkg, _, _⟩
  calc
    data.spectrum.massSq = data.massless.nsns.momentumSq := h_nsns_link.symm
    _ = 0 := h_nsns_pkg.1

/-- Massless-sector momentum squares agree with level-zero mass formula:
all NSNS/RR/fermionic sectors satisfy `p^2 = 0` consistently. -/
theorem superstring_level_zero_massless_shell_consistency
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringLevelZeroMasslessCompatibilityData
      TransversalityResidual DiracResidual ConstraintResidual)
    (h_pkg : SuperstringLevelZeroMasslessCompatibilityPackage data) :
    data.spectrum.massSq = 0 ∧
    data.massless.nsns.momentumSq = 0 ∧
    data.massless.rr.momentumSq = 0 ∧
    data.massless.fermionic.momentumSq = 0 := by
  have h_mass_zero : data.spectrum.massSq = 0 :=
    superstring_level_zero_implies_mass_sq_zero data h_pkg
  rcases h_pkg with ⟨_, h_massless, _, _, h_nsns_link, h_rr_link, h_ferm_link⟩
  rcases h_massless with ⟨h_nsns_pkg, h_rr_pkg, h_ferm_pkg⟩
  rcases h_nsns_pkg with ⟨h_nsns_zero, _, _⟩
  rcases h_rr_pkg with ⟨h_rr_zero, _, _⟩
  rcases h_ferm_pkg with ⟨h_ferm_zero, _, _⟩
  have h_nsns_zero_from_link : data.massless.nsns.momentumSq = 0 := by
    calc
      data.massless.nsns.momentumSq = data.spectrum.massSq := h_nsns_link
      _ = 0 := h_mass_zero
  have h_rr_zero_from_link : data.massless.rr.momentumSq = 0 := by
    calc
      data.massless.rr.momentumSq = data.spectrum.massSq := h_rr_link
      _ = 0 := h_mass_zero
  have h_ferm_zero_from_link : data.massless.fermionic.momentumSq = 0 := by
    calc
      data.massless.fermionic.momentumSq = data.spectrum.massSq := h_ferm_link
      _ = 0 := h_mass_zero
  exact ⟨h_mass_zero, h_nsns_zero_from_link, h_rr_zero_from_link, h_ferm_zero_from_link⟩

/-- Quantization consistency package combining critical BRST nilpotency
with level-zero/massless shell compatibility. -/
structure SuperstringQuantizationConsistencyData
    (TransversalityResidual DiracResidual ConstraintResidual : Type*)
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual] where
  spacetimeDimension : ℕ
  brstComplex : SuperBRSTComplex
  levelZeroCompatibility : SuperstringLevelZeroMasslessCompatibilityData
    TransversalityResidual DiracResidual ConstraintResidual

/-- Critical-dimension quantization package:
BRST nilpotency in `D=10` together with level-zero/massless shell consistency. -/
def SuperstringQuantizationConsistencyPackage
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringQuantizationConsistencyData
      TransversalityResidual DiracResidual ConstraintResidual) : Prop :=
  data.spacetimeDimension = 10 ∧
  SuperBRSTNilpotentInCriticalDimension data.spacetimeDimension data.brstComplex ∧
  SuperstringLevelZeroMasslessCompatibilityPackage data.levelZeroCompatibility

/-- Consequence of the quantization-consistency package:
BRST nilpotency and shared on-shell massless constraints. -/
theorem superstring_quantization_consistency_consequences
    {TransversalityResidual DiracResidual ConstraintResidual : Type*}
    [Zero TransversalityResidual]
    [Zero DiracResidual]
    [Zero ConstraintResidual]
    (data : SuperstringQuantizationConsistencyData
      TransversalityResidual DiracResidual ConstraintResidual)
    (h_pkg : SuperstringQuantizationConsistencyPackage data) :
    SuperBRSTNilpotent data.brstComplex ∧
    data.levelZeroCompatibility.spectrum.massSq = 0 ∧
    data.levelZeroCompatibility.massless.nsns.momentumSq = 0 ∧
    data.levelZeroCompatibility.massless.rr.momentumSq = 0 ∧
    data.levelZeroCompatibility.massless.fermionic.momentumSq = 0 := by
  rcases h_pkg with ⟨h_dim, h_brst_critical, h_level_pkg⟩
  have h_brst_nil : SuperBRSTNilpotent data.brstComplex := by
    exact h_brst_critical h_dim
  have h_shell :=
    superstring_level_zero_massless_shell_consistency data.levelZeroCompatibility h_level_pkg
  rcases h_shell with ⟨h_mass, h_nsns, h_rr, h_ferm⟩
  exact ⟨h_brst_nil, h_mass, h_nsns, h_rr, h_ferm⟩

/-- Spacetime-supersymmetry current/algebra data from worldsheet construction. -/
structure SpacetimeSupersymmetryAlgebraData
    (State : Type*) [AddCommGroup State] [Module ℂ State] where
  alphaPrime : StringSlope
  leftAnticommutator : Endomorphism State
  rightAnticommutator : Endomorphism State
  gammaMomentumContraction : Endomorphism State
  leftRightAnticommutator : Endomorphism State

/-- Spacetime-supersymmetry package (up to picture-raising):
`{Q,Q} = (sqrt(alpha')/4) Gamma.P`, same for right movers, and
left-right supercharges anticommute. -/
def SpacetimeSupersymmetryAlgebraPackage
    {State : Type*} [AddCommGroup State] [Module ℂ State]
    (data : SpacetimeSupersymmetryAlgebraData State) : Prop :=
  data.alphaPrime > 0 ∧
  data.leftAnticommutator =
    (Real.sqrt data.alphaPrime / 4 : ℂ) • data.gammaMomentumContraction ∧
  data.rightAnticommutator =
    (Real.sqrt data.alphaPrime / 4 : ℂ) • data.gammaMomentumContraction ∧
  data.leftRightAnticommutator = 0

/-- Assumed spacetime-supersymmetry algebra package from Section 6.6.3. -/
theorem spacetime_supersymmetry_algebra_package
    {State : Type*} [AddCommGroup State] [Module ℂ State]
    (data : SpacetimeSupersymmetryAlgebraData State)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperstringSpacetimeSusyAlgebra
      (SpacetimeSupersymmetryAlgebraPackage data)) :
    SpacetimeSupersymmetryAlgebraPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
