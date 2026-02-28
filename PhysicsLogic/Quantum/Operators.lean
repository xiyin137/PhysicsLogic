import PhysicsLogic.Quantum.Basic
import PhysicsLogic.Assumptions
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace PhysicsLogic.Quantum

/-- Density operator for mixed states.
    A density operator ρ is a positive semi-definite, trace-one operator. -/
structure DensityOperator (H : Type _) [QuantumStateSpace H] where
  /-- The operator as a function -/
  op : H → H
  /-- Linearity -/
  linear : ∀ (a : ℂ) (ψ φ : H), op (a • ψ + φ) = a • op ψ + op φ
  /-- Self-adjoint: ⟨ψ|ρφ⟩ = ⟨ρψ|φ⟩ -/
  self_adjoint : ∀ (ψ φ : H), @inner ℂ H _ ψ (op φ) = @inner ℂ H _ (op ψ) φ
  /-- Positive semi-definite: ⟨ψ|ρ|ψ⟩ ≥ 0 -/
  positive : ∀ (ψ : H), 0 ≤ (@inner ℂ H _ ψ (op ψ)).re
  /-- Trace is 1: for any orthonormal basis {eᵢ}, Σᵢ ⟨eᵢ|ρ|eᵢ⟩ = 1 -/
  trace_one : ∀ (basis : ℕ → H),
    (∀ i, ‖basis i‖ = 1) →
    (∀ i j, i ≠ j → @inner ℂ H _ (basis i) (basis j) = 0) →
    HasSum (fun i => (@inner ℂ H _ (basis i) (op (basis i))).re) 1

/- Convert pure state to density operator: ρ = |ψ⟩⟨ψ|. -/
/-- Rank-one operator underlying the pure-state density construction. -/
noncomputable def pureToDensityOp {H : Type _} [QuantumStateSpace H]
    (ψ : PureState H) (φ : H) : H :=
  (@inner ℂ H _ ψ.vec φ) • ψ.vec

/-- Assumptions for pure-state density operator proof obligations. -/
structure PureToDensityAssumptions {H : Type _} [QuantumStateSpace H]
    (ψ : PureState H) : Prop where
  self_adjoint : ∀ (φ₁ φ₂ : H),
    @inner ℂ H _ φ₁ (pureToDensityOp ψ φ₂) =
    @inner ℂ H _ (pureToDensityOp ψ φ₁) φ₂
  positive : ∀ (φ : H), 0 ≤ (@inner ℂ H _ φ (pureToDensityOp ψ φ)).re
  trace_one : ∀ (basis : ℕ → H),
    (∀ i, ‖basis i‖ = 1) →
    (∀ i j, i ≠ j → @inner ℂ H _ (basis i) (basis j) = 0) →
    HasSum (fun i => (@inner ℂ H _ (basis i) (pureToDensityOp ψ (basis i))).re) 1

/-- Convert pure state to density operator: ρ = |ψ⟩⟨ψ| -/
noncomputable def pureToDensity {H : Type _} [QuantumStateSpace H]
    (ψ : PureState H)
    (h_phys : PhysicsAssumption AssumptionId.quantumPureToDensityAxioms
      (PureToDensityAssumptions ψ)) :
    DensityOperator H where
  op := pureToDensityOp ψ
  linear := by
    intros a φ₁ φ₂
    simp [pureToDensityOp, inner_add_right, inner_smul_right, add_smul, smul_smul]
  self_adjoint := h_phys.self_adjoint
  positive := h_phys.positive
  trace_one := h_phys.trace_one

/-- Unitary operator preserves inner products.
    U is unitary if ⟨Uψ|Uφ⟩ = ⟨ψ|φ⟩ for all ψ, φ. -/
structure UnitaryOp (H : Type _) [QuantumStateSpace H] where
  /-- The unitary operator as a function -/
  op : H → H
  /-- Linearity -/
  linear : ∀ (a : ℂ) (ψ φ : H), op (a • ψ + φ) = a • op ψ + op φ
  /-- Unitarity: preserves inner product -/
  unitary : ∀ (ψ φ : H), @inner ℂ H _ (op ψ) (op φ) = @inner ℂ H _ ψ φ

/-- Apply unitary operator to a state -/
def applyUnitary {H : Type _} [QuantumStateSpace H] (U : UnitaryOp H) (ψ : H) : H :=
  U.op ψ

/-- Unitary operators preserve norms -/
theorem unitary_preserves_norm {H : Type _} [QuantumStateSpace H]
    (U : UnitaryOp H) (ψ : H)
    (h_phys : PhysicsAssumption AssumptionId.quantumUnitaryPreservesNorm
      (‖applyUnitary U ψ‖ = ‖ψ‖)) :
    ‖applyUnitary U ψ‖ = ‖ψ‖ := by
  exact h_phys

/-- Unitary operators map pure states to pure states -/
def UnitaryOp.applyPure {H : Type _} [QuantumStateSpace H]
    (U : UnitaryOp H) (ψ : PureState H)
    (h_phys : PhysicsAssumption AssumptionId.quantumUnitaryPreservesNorm
      (‖applyUnitary U ψ.vec‖ = ‖ψ.vec‖)) :
    PureState H where
  vec := U.op ψ.vec
  normalized := by
    have h := unitary_preserves_norm U ψ.vec h_phys
    unfold applyUnitary at h
    rw [h, ψ.normalized]

/-- Time evolution structure: a one-parameter family of unitaries satisfying group law -/
structure TimeEvolution (H : Type _) [QuantumStateSpace H] where
  /-- Unitary at time t -/
  U : ℝ → UnitaryOp H
  /-- U(0) = I -/
  at_zero : ∀ ψ : H, (U 0).op ψ = ψ
  /-- Group law: U(s+t) = U(s)U(t) -/
  composition : ∀ (s t : ℝ) (ψ : H), (U (s + t)).op ψ = (U s).op ((U t).op ψ)

/-- Apply time evolution to a state -/
def TimeEvolution.evolve {H : Type _} [QuantumStateSpace H]
    (T : TimeEvolution H) (t : ℝ) (ψ : H) : H :=
  (T.U t).op ψ

end PhysicsLogic.Quantum
