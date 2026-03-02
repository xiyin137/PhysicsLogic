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
  /-- Abstract trace functional used in this interface. -/
  traceFunctional : (H → H) → ℝ
  /-- Unit-trace normalization. -/
  trace_one : traceFunctional op = 1

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
  trace_one : ∃ (traceFunctional : (H → H) → ℝ),
    traceFunctional (pureToDensityOp ψ) = 1

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
  traceFunctional := Classical.choose h_phys.trace_one
  trace_one := Classical.choose_spec h_phys.trace_one

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
    (U : UnitaryOp H) (ψ : H) :
    ‖applyUnitary U ψ‖ = ‖ψ‖ := by
  have h_inner :
      @inner ℂ H _ (applyUnitary U ψ) (applyUnitary U ψ) = @inner ℂ H _ ψ ψ := by
    simpa [applyUnitary] using U.unitary ψ ψ
  have h_sq : ‖applyUnitary U ψ‖ ^ (2 : ℕ) = ‖ψ‖ ^ (2 : ℕ) := by
    calc
      ‖applyUnitary U ψ‖ ^ (2 : ℕ) =
          (@inner ℂ H _ (applyUnitary U ψ) (applyUnitary U ψ)).re := by
            simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) (x := applyUnitary U ψ))
      _ = (@inner ℂ H _ ψ ψ).re := by
            simpa using congrArg Complex.re h_inner
      _ = ‖ψ‖ ^ (2 : ℕ) := by
            simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) (x := ψ)).symm
  exact (sq_eq_sq₀ (norm_nonneg (applyUnitary U ψ)) (norm_nonneg ψ)).1 h_sq

/-- Unitary operators map pure states to pure states -/
def UnitaryOp.applyPure {H : Type _} [QuantumStateSpace H]
    (U : UnitaryOp H) (ψ : PureState H) :
    PureState H where
  vec := U.op ψ.vec
  normalized := by
    have h := unitary_preserves_norm U ψ.vec
    unfold applyUnitary at h
    rw [h, ψ.normalized]

/-- Time evolution structure: a one-parameter family of unitaries satisfying group law -/
structure TimeEvolution (H : Type _) [QuantumStateSpace H] where
  /-- Unitary at time t -/
  U : TimeScale → UnitaryOp H
  /-- U(0) = I -/
  at_zero : ∀ ψ : H, (U 0).op ψ = ψ
  /-- Group law: U(s+t) = U(s)U(t) -/
  composition : ∀ (s t : TimeScale) (ψ : H), (U (s + t)).op ψ = (U s).op ((U t).op ψ)

/-- Apply time evolution to a state -/
def TimeEvolution.evolve {H : Type _} [QuantumStateSpace H]
    (T : TimeEvolution H) (t : TimeScale) (ψ : H) : H :=
  (T.U t).op ψ

end PhysicsLogic.Quantum
