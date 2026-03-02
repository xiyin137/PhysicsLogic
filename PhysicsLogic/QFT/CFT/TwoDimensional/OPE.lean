-- ModularPhysics/Core/QFT/CFT/TwoDimensional/OPE.lean
import PhysicsLogic.QFT.CFT.TwoDimensional.Virasoro
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic

namespace PhysicsLogic.QFT.CFT.TwoDimensional

open CFT

set_option linter.unusedVariables false

/- ============= OPERATOR PRODUCT EXPANSION (OPE) ============= -/

/-- OPE theory in 2D CFT.

    OPE in 2D: φ_i(z,z̄) φ_j(w,w̄) = ∑_k C^k_{ij} (z-w)^{h_k-h_i-h_j} (z̄-w̄)^{h̄_k-h̄_i-h̄_j} φ_k(w,w̄)
    Fundamental structure of 2D CFT!

    This expansion follows from the state-operator correspondence:
    φ_i(z) φ_j(w) creates a state |ψ⟩ = φ_i(z) φ_j(w) |0⟩
    Expanding in energy eigenstates gives the OPE -/
structure OPE2DTheory where
  /-- OPE expansion of two primary fields -/
  ope2D : ∀ {H : Type _}
    (φ_i φ_j : Primary2D H)
    (z w : ℂ),
    List (ℂ × Primary2D H)
  /-- OPE coefficient (3-point function coefficient) -/
  opeCoeff2D : ℕ → ℕ → ℕ → ℂ
  /-- Convergence radius for the local OPE channel of two primaries. -/
  convergenceRadius : ∀ {H : Type _}
    (φ_i φ_j : Primary2D H), ℝ
  /-- Convergence radius is strictly positive. -/
  convergenceRadius_pos : ∀ {H : Type _}
    (φ_i φ_j : Primary2D H), convergenceRadius φ_i φ_j > 0
  /-- OPE expansion converges inside the selected radius. -/
  ope_convergence_in_disc : ∀ {H : Type _}
    (φ_i φ_j : Primary2D H)
    (z w : ℂ),
    ‖z - w‖ < convergenceRadius φ_i φ_j
  /-- Left-nested OPE channel `(φ_i φ_j) φ_k`. -/
  leftNestedOPE2D : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (z_i z_j z_k : ℂ),
    List (ℂ × Primary2D H)
  /-- Right-nested OPE channel `φ_i (φ_j φ_k)`. -/
  rightNestedOPE2D : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (z_i z_j z_k : ℂ),
    List (ℂ × Primary2D H)
  /-- Associativity of OPE: both nested channel decompositions agree
      in the overlap region `|z_i-z_j| < |z_j-z_k|`. -/
  ope_associativity_2d : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (z_i z_j z_k : ℂ)
    (h_order : ‖z_i - z_j‖ < ‖z_j - z_k‖),
    leftNestedOPE2D φ_i φ_j φ_k z_i z_j z_k =
      rightNestedOPE2D φ_i φ_j φ_k z_i z_j z_k

/- ============= STRUCTURE CONSTANTS ============= -/

/-- Structure constants in 2D CFT -/
structure StructureConstant2DTheory where
  /-- Structure constant from 3-point function
      ⟨φ_i(z_i,z̄_i) φ_j(z_j,z̄_j) φ_k(z_k,z̄_k)⟩ = C_ijk / |z_i-z_j|^... |z_j-z_k|^... |z_i-z_k|^... -/
  structure_constant_from_3pt : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H), ℂ
  /-- Phase entering the reality condition of structure constants. -/
  realityPhase : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H), ℂ
  /-- The reality phase is unit-norm. -/
  realityPhase_unit : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H),
    ‖realityPhase φ_i φ_j φ_k‖ = 1
  /-- Reality condition for unitary CFT: C_{ijk}* = C_{ijk} up to phases -/
  structure_constant_reality : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (h_unitary : IsUnitary2D ⟨φ_i.h⟩),  -- unitarity of the theory
    starRingEnd ℂ (structure_constant_from_3pt φ_i φ_j φ_k) =
      realityPhase φ_i φ_j φ_k * structure_constant_from_3pt φ_i φ_j φ_k
  /-- Polynomial associativity constraints on a chosen operator list. -/
  associativityPolynomialConstraints : ∀ {H : Type _},
    List (List (Primary2D H) → ℂ)
  /-- Structure constants satisfy polynomial equations from associativity -/
  structure_constant_polynomial_equations : ∀ {H : Type _}
    (operators : List (Primary2D H)),
    ∀ P ∈ associativityPolynomialConstraints (H := H), P operators = 0

/- ============= GLOBAL CONFORMAL TRANSFORMATIONS ============= -/

/-- SL(2,ℂ) transformations: z → (az+b)/(cz+d) -/
structure MoebiusTransform where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  determinant_condition : a * d - b * c = 1

/-- Apply Moebius transformation -/
noncomputable def applyMoebius (m : MoebiusTransform) (z : ℂ) : ℂ :=
  (m.a * z + m.b) / (m.c * z + m.d)

/-- Global conformal transformation theory in 2D -/
structure GlobalConformalTheory2D where
  /-- Holomorphic Möbius Jacobian factor for the given primary insertion. -/
  holomorphicFactor : ∀ {H : Type _}
    (φ : Primary2D H) (m : MoebiusTransform) (z : ℂ), ℂ
  /-- Antiholomorphic Möbius Jacobian factor for the given primary insertion. -/
  antiholomorphicFactor : ∀ {H : Type _}
    (φ : Primary2D H) (m : MoebiusTransform) (zBar : ℂ), ℂ
  /-- Holomorphic factor is nonzero. -/
  holomorphicFactor_nonzero : ∀ {H : Type _}
    (φ : Primary2D H) (m : MoebiusTransform) (z : ℂ),
    holomorphicFactor φ m z ≠ 0
  /-- Antiholomorphic factor is nonzero. -/
  antiholomorphicFactor_nonzero : ∀ {H : Type _}
    (φ : Primary2D H) (m : MoebiusTransform) (zBar : ℂ),
    antiholomorphicFactor φ m zBar ≠ 0
  /-- Primary field transforms under Moebius: φ(z) → (cz+d)^{-2h} φ((az+b)/(cz+d)) -/
  primary_moebius_transform : ∀ {H : Type _} [SMul ℂ H]
    (φ : Primary2D H)
    (m : MoebiusTransform)
    (z zBar : ℂ)
    (state : H),
    φ.field (applyMoebius m z) (applyMoebius m zBar) state =
      (holomorphicFactor φ m z * antiholomorphicFactor φ m zBar) •
        φ.field z zBar state
  /-- Ward insertion generated by global conformal transformations. -/
  globalWardInsertion : ∀ {H : Type _}
    (n : ℕ)
    (operators : Fin n → Primary2D H)
    (points : Fin n → ℂ), ℂ
  /-- Contact-term side of the global Ward identity. -/
  globalWardContactTerm : ∀ {H : Type _}
    (n : ℕ)
    (operators : Fin n → Primary2D H)
    (points : Fin n → ℂ), ℂ
  /-- Global conformal Ward identity from SL(2,ℂ) -/
  global_conformal_ward : ∀ {H : Type _}
    (n : ℕ)
    (operators : Fin n → Primary2D H)
    (points : Fin n → ℂ),
    globalWardInsertion n operators points = globalWardContactTerm n operators points

/- ============= OPE FROM STATE-OPERATOR CORRESPONDENCE ============= -/

/-- State-operator correspondence in 2D CFT.
    Every state |ψ⟩ in the Hilbert space corresponds to a local operator O_ψ(0)
    via |ψ⟩ = O_ψ(0)|0⟩ -/
structure StateOperatorCorrespondence2D where
  /-- OPE state decomposition coefficients/states in a fixed channel. -/
  opeDecomposition : ∀ {H : Type _}
    (φ_i φ_j : Primary2D H)
    (z w : ℂ)
    (vacuum : H),
    List (ℂ × H)
  /-- State produced by the operator product in radial quantization. -/
  stateFromOperatorProduct : ∀ {H : Type _}
    (φ_i φ_j : Primary2D H)
    (z w : ℂ)
    (vacuum : H), H
  /-- The operator-product state is reconstructed by summing decomposition terms. -/
  decomposition_reconstructs_state : ∀ {H : Type _} [AddCommMonoid H] [SMul ℂ H]
    (φ_i φ_j : Primary2D H)
    (z w : ℂ)
    (vacuum : H),
    stateFromOperatorProduct φ_i φ_j z w vacuum =
      (opeDecomposition φ_i φ_j z w vacuum).foldl
        (fun acc term => acc + term.1 • term.2) 0
  /-- Nontrivial operator-product state requires a nonempty decomposition list. -/
  nontrivial_state_implies_nonempty : ∀ {H : Type _} [AddCommMonoid H] [SMul ℂ H]
    (φ_i φ_j : Primary2D H)
    (z w : ℂ)
    (vacuum : H),
    stateFromOperatorProduct φ_i φ_j z w vacuum ≠ 0 →
    (opeDecomposition φ_i φ_j z w vacuum) ≠ []
  /-- OPE coefficient extracted from a chosen inner product pairing. -/
  opeCoefficientFromInnerProduct : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (inner_product : H → H → ℂ), ℂ
  /-- Reference matrix element used to define OPE coefficients from states. -/
  referenceMatrixElement : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (inner_product : H → H → ℂ), ℂ
  /-- OPE coefficients determined by inner products of states -/
  ope_coeff_from_inner_product : ∀ {H : Type _}
    (φ_i φ_j φ_k : Primary2D H)
    (inner_product : H → H → ℂ),
    opeCoefficientFromInnerProduct φ_i φ_j φ_k inner_product =
      referenceMatrixElement φ_i φ_j φ_k inner_product

end PhysicsLogic.QFT.CFT.TwoDimensional
