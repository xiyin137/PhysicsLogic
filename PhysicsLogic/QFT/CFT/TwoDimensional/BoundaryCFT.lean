import PhysicsLogic.Assumptions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.QFT.CFT.TwoDimensional

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Boundary spin-structure sign choice in fermionic boundary conditions. -/
inductive BoundarySpinStructure where
  | plus
  | minus
deriving DecidableEq, Repr

/-- NS-sector identification with/without diagonal GSO projection. -/
inductive IsingBoundarySector where
  | nsGsoProjected
  | nsUnprojected
deriving DecidableEq, Repr

/-- Data for conformal boundary conditions in a 2D CFT. -/
structure BoundaryConformalData where
  centralChargeLeft : ℝ
  centralChargeRight : ℝ
  boundaryStressMismatch : ℝ

/-- Conformal boundary-condition package:
`T = T̃` on the boundary and `c = c̃`. -/
def BoundaryConformalInvariance (data : BoundaryConformalData) : Prop :=
  data.boundaryStressMismatch = 0 ∧
  data.centralChargeLeft = data.centralChargeRight

/-- Assumed conformal boundary-condition package from Appendix P. -/
theorem boundary_conformal_invariance
    (data : BoundaryConformalData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryConformalInvariance
      (BoundaryConformalInvariance data)) :
    BoundaryConformalInvariance data := by
  exact h_phys

/-- Kinematic data for boundary two-point and three-point functions. -/
structure BoundaryCorrelatorData where
  weightA : ℝ
  weightB : ℝ
  weightC : ℝ
  twoPointExponent : ℝ
  threePointExponent12 : ℝ
  threePointExponent23 : ℝ
  threePointExponent13 : ℝ
  twoPointCoeffAB : ℂ
  twoPointCoeffBA : ℂ
  threePointCoeffABC : ℂ
  threePointCoeffBCA : ℂ
  threePointCoeffCAB : ℂ

/-- Boundary correlator-kinematics package from global conformal symmetry on the disc/UHP. -/
def BoundaryCorrelatorKinematics (data : BoundaryCorrelatorData) : Prop :=
  data.twoPointExponent = 2 * data.weightA ∧
  data.weightA = data.weightB ∧
  data.twoPointCoeffAB = data.twoPointCoeffBA ∧
  data.threePointExponent12 = data.weightA + data.weightB - data.weightC ∧
  data.threePointExponent23 = data.weightB + data.weightC - data.weightA ∧
  data.threePointExponent13 = data.weightA + data.weightC - data.weightB ∧
  data.threePointCoeffABC = data.threePointCoeffBCA ∧
  data.threePointCoeffBCA = data.threePointCoeffCAB

/-- Assumed boundary correlator kinematics from Appendix P. -/
theorem boundary_correlator_kinematics
    (data : BoundaryCorrelatorData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryCorrelatorKinematics
      (BoundaryCorrelatorKinematics data)) :
    BoundaryCorrelatorKinematics data := by
  exact h_phys

/-- Finite-rank boundary-state data (`|B⟩` expansion coefficients and gluing mismatch). -/
structure BoundaryStateData (rank : ℕ) where
  modeMismatch : ℤ → ℂ
  ishbCoeff : Fin rank → ℂ
  onePointCoeff : Fin rank → ℂ
  bulkTwoPoint : Fin rank → Fin rank → ℂ
  bulkBoundaryCoeff : Fin rank → ℂ

/-- Boundary-state gluing condition `(L_n - L̃_{-n})|B⟩ = 0`. -/
def BoundaryStateGluing {rank : ℕ} (data : BoundaryStateData rank) : Prop :=
  ∀ n : ℤ, data.modeMismatch n = 0

/-- Assumed Ishibashi/gluing condition package for boundary states from Appendix P. -/
theorem boundary_state_gluing
    {rank : ℕ}
    (data : BoundaryStateData rank)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryStateIshibashiGluing
      (BoundaryStateGluing data)) :
    BoundaryStateGluing data := by
  exact h_phys

/-- Bulk-boundary one-point relation `R_{i0} = D_{ij} U_B^j` (finite-rank interface). -/
def BulkBoundaryOnePointRelation {rank : ℕ} (data : BoundaryStateData rank) : Prop :=
  ∀ i : Fin rank,
    data.bulkBoundaryCoeff i =
      ∑ j : Fin rank, data.bulkTwoPoint i j * data.onePointCoeff j

/-- Assumed bulk-boundary one-point coefficient relation from Appendix P. -/
theorem bulk_boundary_one_point_relation
    {rank : ℕ}
    (data : BoundaryStateData rank)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryBulkBoundaryOnePoint
      (BulkBoundaryOnePointRelation data)) :
    BulkBoundaryOnePointRelation data := by
  exact h_phys

/-- Cylinder modular-duality data between closed-channel and strip-channel descriptions. -/
structure BoundaryCylinderDualityData where
  modulus : ℝ
  closedChannelAmplitude : ℂ
  openChannelTrace : ℂ

/-- Cylinder modular duality relation:
`⟨⟨B| e^{-π t (L_0+L̃_0-c/12)} |B'⟩ = Tr_{H_{BB'}} e^{-(2π/t)(L_0-c/24)}`. -/
def BoundaryCylinderModularDuality (data : BoundaryCylinderDualityData) : Prop :=
  data.modulus > 0 ∧
  data.closedChannelAmplitude = data.openChannelTrace

/-- Assumed cylinder modular-duality relation from Appendix P. -/
theorem boundary_cylinder_modular_duality
    (data : BoundaryCylinderDualityData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryCylinderModularDuality
      (BoundaryCylinderModularDuality data)) :
    BoundaryCylinderModularDuality data := by
  exact h_phys

/-- Chan-Paton enhancement data for boundary-condition sums. -/
structure ChanPatonBoundaryData where
  n : ℕ
  m : ℕ
  hbbDim : ℕ
  hBnmDim : ℕ
  matrixDim : ℕ
  matrixProductCoeff : Fin n → Fin m → Fin m → Fin n → ℂ

/-- Chan-Paton factorization and matrix-unit multiplication interface:
`H_{B^{⊕n},B^{⊕m}} ≃ H_{BB} ⊗ Mat(n,m)` and
`E_{ij} E_{kℓ} = δ_{jk} E_{iℓ}`. -/
def ChanPatonFactorization (data : ChanPatonBoundaryData) : Prop :=
  data.matrixDim = data.n * data.m ∧
  data.hBnmDim = data.hbbDim * data.matrixDim ∧
  (∀ i : Fin data.n, ∀ j k : Fin data.m, ∀ l : Fin data.n,
    data.matrixProductCoeff i j k l =
      if j = k then (if i = l then 1 else 0) else 0)

/-- Assumed Chan-Paton factorization/multiplication package from Appendix P. -/
theorem chan_paton_factorization
    (data : ChanPatonBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryChanPatonFactorization
      (ChanPatonFactorization data)) :
    ChanPatonFactorization data := by
  exact h_phys

/-- Free-boson (`X`) Neumann/Dirichlet boundary-condition data. -/
structure FreeBosonBoundaryData where
  alphaPrime : ℝ
  neumannDerivativeMismatch : ℝ
  dirichletDerivativeMismatch : ℝ
  boundaryXValue : ℝ
  dirichletPosition : ℝ
  neumannNorm : ℝ
  dirichletNorm : ℝ

/-- Free-boson Neumann/Dirichlet conformal boundary-condition package. -/
def FreeBosonNDBoundaryConditions (data : FreeBosonBoundaryData) : Prop :=
  data.alphaPrime > 0 ∧
  data.neumannDerivativeMismatch = 0 ∧
  data.dirichletDerivativeMismatch = 0 ∧
  data.boundaryXValue = data.dirichletPosition

/-- Assumed free-boson Neumann/Dirichlet boundary-condition package from Appendix P. -/
theorem free_boson_nd_boundary_conditions
    (data : FreeBosonBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryFreeBosonNdConditions
      (FreeBosonNDBoundaryConditions data)) :
    FreeBosonNDBoundaryConditions data := by
  exact h_phys

/-- Free-boson boundary-state normalization package.
The interface tracks the Appendix-P normalizations through squared magnitudes. -/
def FreeBosonBoundaryStateNormalization (data : FreeBosonBoundaryData) : Prop :=
  data.alphaPrime > 0 ∧
  data.neumannNorm ^ (2 : ℕ) =
    1 / (2 * Real.pi * Real.sqrt (2 * data.alphaPrime)) ∧
  data.dirichletNorm ^ (2 : ℕ) =
    Real.pi * Real.sqrt (2 * data.alphaPrime)

/-- Assumed free-boson boundary-state normalization relation from Appendix P. -/
theorem free_boson_boundary_state_normalization
    (data : FreeBosonBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryFreeBosonNormalization
      (FreeBosonBoundaryStateNormalization data)) :
    FreeBosonBoundaryStateNormalization data := by
  exact h_phys

/-- Free-fermion boundary-state data for Ising/diagonal-GSO boundary conditions. -/
structure FreeFermionBoundaryData where
  spinStructure : BoundarySpinStructure
  neumannBoundaryMismatch : ℂ
  dirichletBoundaryMismatch : ℂ
  n1 : ℝ
  n2 : ℝ
  n3 : ℝ
  hNNGroundDegeneracy : ℕ
  hDDGroundDegeneracy : ℕ
  sectorNN : IsingBoundarySector
  sectorDD : IsingBoundarySector

/-- Free-fermion Neumann/Dirichlet boundary equations from Appendix P. -/
def FreeFermionNDBoundaryConditions (data : FreeFermionBoundaryData) : Prop :=
  data.neumannBoundaryMismatch = 0 ∧
  data.dirichletBoundaryMismatch = 0

/-- Assumed free-fermion Neumann/Dirichlet boundary-condition package from Appendix P. -/
theorem free_fermion_nd_boundary_conditions
    (data : FreeFermionBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryFreeFermionNdConditions
      (FreeFermionNDBoundaryConditions data)) :
    FreeFermionNDBoundaryConditions data := by
  exact h_phys

/-- Free-fermion boundary-state coefficient package from Appendix P.
`N_1 = 1/sqrt(2)`, `N_2 = ±2^{-1/4}` (tracked by `N_2^4 = 1/2`), `N_3 = 1`. -/
def FreeFermionBoundaryStateCoefficients (data : FreeFermionBoundaryData) : Prop :=
  data.n1 = 1 / Real.sqrt 2 ∧
  data.n2 ^ (4 : ℕ) = 1 / 2 ∧
  data.n3 = 1

/-- Assumed free-fermion boundary-state coefficient package from Appendix P. -/
theorem free_fermion_boundary_state_coefficients
    (data : FreeFermionBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryFreeFermionCoefficients
      (FreeFermionBoundaryStateCoefficients data)) :
    FreeFermionBoundaryStateCoefficients data := by
  exact h_phys

/-- Ising-boundary-sector identification package (`NN` projected NS, `DD` unprojected NS). -/
def FreeFermionBoundarySectorIdentification (data : FreeFermionBoundaryData) : Prop :=
  data.hNNGroundDegeneracy = 1 ∧
  data.hDDGroundDegeneracy = 1 ∧
  data.sectorNN = IsingBoundarySector.nsGsoProjected ∧
  data.sectorDD = IsingBoundarySector.nsUnprojected

/-- Assumed Ising-boundary-sector identification from Appendix P. -/
theorem free_fermion_boundary_sector_identification
    (data : FreeFermionBoundaryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dBoundaryFreeFermionSectorIdentification
      (FreeFermionBoundarySectorIdentification data)) :
    FreeFermionBoundarySectorIdentification data := by
  exact h_phys

end PhysicsLogic.QFT.CFT.TwoDimensional
