-- ModularPhysics/Core/QFT/CFT/TwoDimensional/Examples.lean
import PhysicsLogic.QFT.CFT.TwoDimensional.ModularInvariance
import PhysicsLogic.QFT.CFT.TwoDimensional.Superconformal
import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.QFT.CFT.TwoDimensional

open CFT

set_option linter.unusedVariables false

/- ============= FREE BOSON ============= -/

/-- Integer Kronecker delta in mode-index form. -/
def kroneckerInt (k : ℤ) : ℂ := if k = 0 then 1 else 0

/-- Free-boson oscillator-mode algebra interface:
`[α_m, α_n] = m δ_{m+n,0}`, similarly for anti-holomorphic modes, and left/right commute. -/
structure FreeBosonModeAlgebra2D (ModeOp : Type*) where
  alpha : ℤ → ModeOp
  alphaBar : ℤ → ModeOp
  commutator : ModeOp → ModeOp → ℂ
  left_heisenberg : ∀ m n : ℤ,
    commutator (alpha m) (alpha n) = (m : ℂ) * kroneckerInt (m + n)
  right_heisenberg : ∀ m n : ℤ,
    commutator (alphaBar m) (alphaBar n) = (m : ℂ) * kroneckerInt (m + n)
  chiral_decoupling : ∀ m n : ℤ,
    commutator (alpha m) (alphaBar n) = 0

/-- Normal-ordered vertex-operator interface for the free boson. -/
structure NormalOrderedVertexOperators2D (VertexOp : Type*) where
  vertex : ℝ → VertexOp
  normalOrdered : VertexOp → Prop
  opeSingularExponent : ℝ → ℝ → ℝ
  all_vertex_normal_ordered : ∀ α : ℝ, normalOrdered (vertex α)
  ope_singular_exponent_formula : ∀ α β : ℝ,
    opeSingularExponent α β = α * β

/-- Free-boson correlator data on a genus-`h` Riemann surface:
Green-function/prime-form/period-matrix ingredients plus momentum conservation. -/
structure FreeBosonGenusHCorrelatorData (Point : Type*) where
  genus : ℕ
  insertionCount : ℕ
  momenta : Fin insertionCount → ℝ
  primeForm : Point → Point → ℂ
  periodMatrixEntry : Fin genus → Fin genus → ℂ
  correlator : (Fin insertionCount → Point) → ℂ
  momentumConservationHolds : Bool

/-- Free boson central charge is always c = 1 -/
def free_boson_central_charge : ℝ := 1

/-- Vertex operator conformal weight: h = α²/2 -/
noncomputable def vertex_operator_weight (α : ℝ) : ℝ := α^2 / 2

/-- Momentum-winding primary conformal weights -/
noncomputable def momentum_winding_weight (R : ℝ) (n m : ℤ) : ℝ × ℝ :=
  let h := ((n : ℝ)/R + m*R)^2 / 2
  let h_bar := ((n : ℝ)/R - m*R)^2 / 2
  (h, h_bar)

/-- Free boson CFT: the simplest 2D CFT
    Action: S = (1/4π) ∫ ∂φ ∂̄φ
    Central charge: c = 1
    Spectrum: continuous family of primaries with h = (n+αR)²/2 for n ∈ ℤ, α ∈ ℝ -/
structure FreeBosonCFT (H : Type _) where
  compactification_radius : ℝ
  radius_positive : compactification_radius > 0
  /-- Primary operators V_{n,m} labeled by momentum n and winding m -/
  primary : ℤ → ℤ → Primary2D H
  /-- Weights match momentum-winding formula -/
  primary_weights : ∀ (n m : ℤ),
    let (h_val, h_bar_val) := momentum_winding_weight compactification_radius n m
    (primary n m).h = h_val ∧ (primary n m).h_bar = h_bar_val

/-- T-duality map: exchange R ↔ 1/R -/
noncomputable def t_dual {H : Type _} (fb : FreeBosonCFT H)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.cftTDualWeightSymmetry
        (∀ (n m : ℤ),
          let (h_val, h_bar_val) := momentum_winding_weight (1 / fb.compactification_radius) n m
          (fb.primary m n).h = h_val ∧ (fb.primary m n).h_bar = h_bar_val)) :
    FreeBosonCFT H where
  compactification_radius := 1 / fb.compactification_radius
  radius_positive := by
    apply div_pos
    · norm_num
    · exact fb.radius_positive
  primary := fun n m => fb.primary m n  -- T-duality swaps momentum and winding
  primary_weights := by
    intro n m
    simpa using h_phys n m

/-- Self-dual radius where R = 1/R -/
def self_dual_radius : ℝ := 1

/- ============= FREE FERMION ============= -/

/-- Spin-structure parity (even/odd) for genus-`h` fermionic sectors. -/
inductive SpinStructureParity where
  | even
  | odd
deriving DecidableEq, Repr

/-- Free-fermion NS/R-sector data with sector-compatible mode indexing
and canonical Majorana central charge. -/
structure FreeFermionSectorData2D where
  sector : NSRSector
  modeIndexPredicate : ℚ → Prop
  modeIndexCompatibility : ∀ r : ℚ,
    modeIndexPredicate r ↔ sectorCompatible sector r
  fermionCentralCharge : ℝ
  canonicalCentralCharge : fermionCentralCharge = 1 / 2
  ramondSpinFieldWeight : ℝ
  ramondSpinFieldWeightFormula :
    sector = NSRSector.R → ramondSpinFieldWeight = 1 / 16

/-- Szego-kernel spin-structure interface for genus-dependent fermion propagators. -/
structure SzegoKernelSpinStructureData (Point : Type*) where
  genus : ℕ
  parity : SpinStructureParity
  szegoKernel : Point → Point → ℂ
  kernelAntisymmetry : ∀ x y : Point, szegoKernel x y = -szegoKernel y x
  hasFermionZeroMode : Bool
  zeroModeParityRule : (parity = SpinStructureParity.odd → hasFermionZeroMode = true) ∧
    (parity = SpinStructureParity.even → hasFermionZeroMode = false)

/-- Canonical free-field central-charge assignments from Appendix G:
one free boson has `c=1`, one Majorana free fermion has `c=1/2`. -/
structure FreeFieldCentralChargeAssignments where
  bosonCentralCharge : ℝ
  majoranaFermionCentralCharge : ℝ

/-- Package for the canonical Appendix-G free-field central charges. -/
def FreeFieldCentralChargeAssignmentsPackage
    (data : FreeFieldCentralChargeAssignments) : Prop :=
  data.bosonCentralCharge = 1 ∧
  data.majoranaFermionCentralCharge = 1 / 2

/-- One free boson + one Majorana fermion has total central charge `3/2`. -/
theorem free_boson_plus_majorana_total_c
    (data : FreeFieldCentralChargeAssignments)
    (h_data : FreeFieldCentralChargeAssignmentsPackage data) :
    data.bosonCentralCharge + data.majoranaFermionCentralCharge = 3 / 2 := by
  rcases h_data with ⟨h_b, h_f⟩
  calc
    data.bosonCentralCharge + data.majoranaFermionCentralCharge
        = 1 + (1 / 2 : ℝ) := by rw [h_b, h_f]
    _ = 3 / 2 := by ring

/- ============= ISING MODEL ============= -/

/-- Ising CFT: critical point of 2D Ising model
    Minimal model with m=3
    Central charge: c = 1/2
    Three primary fields: 𝟙 (h=0), ε (h=1/2), σ (h=1/16) -/
structure IsingCFT (H : Type _) where
  /-- The three primary operators -/
  identity : Primary2D H
  energy : Primary2D H
  spin : Primary2D H
  /-- Correct conformal weights -/
  identity_weight : identity.h = 0
  energy_weight : energy.h = 1/2
  spin_weight : spin.h = 1/16

/-- Ising central charge -/
noncomputable def ising_central_charge : ℝ := 1/2

/-- Identity operator weight -/
def ising_identity_weight : ℝ := 0

/-- Energy operator weight -/
noncomputable def ising_energy_weight : ℝ := 1/2

/-- Spin operator weight -/
noncomputable def ising_spin_weight : ℝ := 1/16

/-- Critical exponents computed from operator dimensions -/
def ising_critical_exponent_nu : ℝ := 1  -- from energy operator
noncomputable def ising_critical_exponent_beta : ℝ := 1/8  -- from spin operator
noncomputable def ising_critical_exponent_gamma : ℝ := 7/4  -- from σ²

/- ============= MINIMAL MODELS ============= -/

/-- Minimal model central charge formula -/
noncomputable def minimal_model_c (m : ℕ) : ℝ :=
  1 - 6 / (m * (m + 1))

/-- Primary field conformal weight formula -/
noncomputable def minimal_model_weight_formula (m r s : ℕ) : ℝ :=
  (((m + 1 : ℝ) * r - m * s)^2 - 1) / (4 * m * (m + 1))

/-- Virasoro minimal model M(m,m+1)
    Rational CFTs with c < 1 for m ≥ 3 -/
structure MinimalModel (H : Type _) where
  m : ℕ
  m_geq_3 : m ≥ 3
  /-- Primary operators φ_{r,s} for 1 ≤ s ≤ r < m -/
  primary : (r s : ℕ) → (1 ≤ r ∧ r < m) → (1 ≤ s ∧ s ≤ r) → Primary2D H
  /-- Weights match Kac table formula -/
  primary_weight : ∀ (r s : ℕ) (hr : 1 ≤ r ∧ r < m) (hs : 1 ≤ s ∧ s ≤ r),
    (primary r s hr hs).h = minimal_model_weight_formula m r s

/-- Ising model is minimal model with m=3 -/
noncomputable def ising_as_minimal_model_m : ℕ := 3

/-- Tricritical Ising: m=4, c=7/10 -/
noncomputable def tricritical_ising_m : ℕ := 4

/-- 3-state Potts: m=5, c=4/5 -/
noncomputable def three_state_potts_m : ℕ := 5

/- ============= LIOUVILLE THEORY ============= -/

/-- Background charge Q = b + 1/b -/
noncomputable def liouville_Q (b : ℝ) : ℝ :=
  b + 1/b

/-- Liouville central charge: c = 1 + 6Q² -/
noncomputable def liouville_c (b : ℝ) : ℝ :=
  let Q := liouville_Q b
  1 + 6 * Q^2

/-- Primary operator conformal weight: h = α(Q - α) -/
noncomputable def liouville_weight (b α : ℝ) : ℝ :=
  let Q := liouville_Q b
  α * (Q - α)

/-- Liouville CFT: non-rational CFT with continuous spectrum
    Parameterized by b > 0 (or equivalently central charge c > 1) -/
structure LiouvilleCFT (H : Type _) where
  b : ℝ
  b_positive : b > 0
  /-- Primary operators V_α parameterized by momentum α -/
  primary : ℝ → Primary2D H
  /-- Weights match Liouville formula -/
  primary_weight : ∀ (α : ℝ),
    (primary α).h = liouville_weight b α

/-- Duality transformation b ↔ 1/b leaves c invariant -/
noncomputable def liouville_dual_b (b : ℝ) (hb : b > 0) : ℝ := 1 / b

/-- DOZZ formula (Dorn-Otto-Zamolodchikov-Zamolodchikov):
    Structure constants for Liouville theory.
    This is the unique solution to crossing symmetry + conformal bootstrap for c > 1. -/
structure DOZZTheory where
  dozz_formula : ℝ → ℝ → ℝ → ℝ → ℂ  -- b, α₁, α₂, α₃ → C_{α₁α₂α₃}

/- ============= WZW MODELS ============= -/

/-- WZW model: current algebra CFT based on Lie group G at level k -/
structure WZWModel (G : Type) (H : Type _) where
  level : ℕ
  level_positive : level > 0
  group_dim : ℕ
  dual_coxeter : ℕ
  /-- Primary operators labeled by highest weight representations -/
  primary : ℕ → Primary2D H
  /-- Weight formula -/
  primary_weight : ∀ (j : ℕ),
    ∃ (h_val : ℝ), (primary j).h = h_val

/-- WZW central charge formula -/
noncomputable def wzw_c (level group_dim dual_coxeter : ℕ) : ℝ :=
  (level * group_dim : ℝ) / (level + dual_coxeter)

/-- SU(2)_k WZW model data -/
structure SU2WZWData (H : Type _) where
  wzw : WZWModel Unit H
  level_val : wzw.level > 0
  group_dim_eq : wzw.group_dim = 3
  dual_coxeter_eq : wzw.dual_coxeter = 2
  /-- SU(2) primary weight formula: h_j = j(j+1)/(k+2) -/
  su2_weight : ∀ (j : ℕ) (hj : 2 * j ≤ wzw.level),
    (wzw.primary j).h = (j * (j + 1) : ℝ) / (wzw.level + 2)

end PhysicsLogic.QFT.CFT.TwoDimensional
