import PhysicsLogic.Quantum.Basic
import PhysicsLogic.Quantum.Composite
import PhysicsLogic.Assumptions

namespace PhysicsLogic.Quantum

/-- Probability (Born rule) -/
noncomputable def bornRule {H : Type _} [QuantumStateSpace H]
    (ψ φ : PureState H) : ℝ :=
  let z := innerProduct ψ.vec φ.vec
  z.re ^ 2 + z.im ^ 2

/-- Two states are orthogonal -/
def orthogonal {H : Type _} [QuantumStateSpace H] (ψ φ : H) : Prop :=
  innerProduct ψ φ = 0

/-- Orthogonal basis states in a QubitBasis -/
theorem qubitBasis_orthogonal (basis : QubitBasis) : orthogonal basis.ket0 basis.ket1 :=
  basis.orthogonal

/-- Singlet state (Bell state as a pure state) -/
noncomputable def singlet {T : TensorProductSpace Qubit Qubit} (basis : QubitBasis)
    (bell : BellState basis T) : PureState T.carrier :=
  bell.toPureState

/-- Orthogonal states have zero probability -/
theorem orthogonal_zero_prob {H : Type _} [QuantumStateSpace H]
    (ψ φ : PureState H)
    (h : orthogonal ψ.vec φ.vec) :
    bornRule ψ φ = 0 := by
  unfold bornRule orthogonal innerProduct at *
  simp [h]

-- ========================================
-- OBSERVABLES AND EXPECTATION VALUES
-- ========================================

/-- A Hermitian operator (observable) on a quantum state space.
    This structure captures the essential properties of observables. -/
structure Observable (H : Type*) [QuantumStateSpace H] where
  /-- Apply the observable to a state (as a linear operator) -/
  apply : H → H
  /-- Observables are linear -/
  linear : ∀ (a : ℂ) (ψ φ : H), apply (a • ψ + φ) = a • apply ψ + apply φ
  /-- Self-adjointness: ⟨ψ|Aφ⟩ = ⟨Aψ|φ⟩ (no conjugation needed in Mathlib's convention) -/
  hermitian : ∀ (ψ φ : H), @inner ℂ H _ ψ (apply φ) = @inner ℂ H _ (apply ψ) φ

/-- Apply observable to a state -/
def apply_observable {H : Type*} [QuantumStateSpace H] (A : Observable H) (ψ : H) : H :=
  A.apply ψ

/-- Expectation value ⟨ψ|A|ψ⟩ -/
noncomputable def expectation {H : Type*} [QuantumStateSpace H]
    (ψ : PureState H) (A : Observable H) : ℂ :=
  innerProduct ψ.vec (apply_observable A ψ.vec)

/-- Physical observables have real expectation values (from Hermiticity) -/
theorem expectation_real {H : Type*} [QuantumStateSpace H]
    (ψ : PureState H) (A : Observable H)
    (h_phys : PhysicsAssumption AssumptionId.quantumExpectationReal
      ((expectation ψ A).im = 0)) :
    (expectation ψ A).im = 0 := by
  exact h_phys

/-- Real-valued expectation value -/
noncomputable def expectation_value {H : Type*} [QuantumStateSpace H]
    (ψ : PureState H) (A : Observable H) : ℝ :=
  (expectation ψ A).re

-- ========================================
-- PAULI OPERATORS
-- ========================================

/-- Specification for Pauli operators on a qubit.
    The Pauli matrices σ_x, σ_y, σ_z form a basis for traceless Hermitian 2×2 matrices. -/
structure PauliOperators where
  /-- Pauli X matrix -/
  pauli_x : Observable Qubit
  /-- Pauli Y matrix -/
  pauli_y : Observable Qubit
  /-- Pauli Z matrix -/
  pauli_z : Observable Qubit
  /-- Pauli algebra: σ_x² = I -/
  pauli_x_sq : ∀ ψ : Qubit, pauli_x.apply (pauli_x.apply ψ) = ψ
  /-- Pauli algebra: σ_y² = I -/
  pauli_y_sq : ∀ ψ : Qubit, pauli_y.apply (pauli_y.apply ψ) = ψ
  /-- Pauli algebra: σ_z² = I -/
  pauli_z_sq : ∀ ψ : Qubit, pauli_z.apply (pauli_z.apply ψ) = ψ

/-- Pauli operator in a direction specified by angles (θ, φ) on the Bloch sphere
    σ_n = sin(θ)cos(φ)σ_x + sin(θ)sin(φ)σ_y + cos(θ)σ_z -/
noncomputable def pauliDirectionApply (paulis : PauliOperators) (θ φ : ℝ) (ψ : Qubit) : Qubit :=
  (Real.sin θ * Real.cos φ) • paulis.pauli_x.apply ψ +
  (Real.sin θ * Real.sin φ) • paulis.pauli_y.apply ψ +
  (Real.cos θ) • paulis.pauli_z.apply ψ

/-- Assumptions for directional Pauli observable proof obligations. -/
structure PauliDirectionAssumptions (paulis : PauliOperators) (θ φ : ℝ) : Prop where
  linear : ∀ (a : ℂ) (ψ₁ ψ₂ : Qubit),
    pauliDirectionApply paulis θ φ (a • ψ₁ + ψ₂) =
      a • pauliDirectionApply paulis θ φ ψ₁ + pauliDirectionApply paulis θ φ ψ₂
  hermitian : ∀ (ψ₁ ψ₂ : Qubit),
    @inner ℂ Qubit _ ψ₁ (pauliDirectionApply paulis θ φ ψ₂) =
      @inner ℂ Qubit _ (pauliDirectionApply paulis θ φ ψ₁) ψ₂

/-- Pauli operator in a direction specified by angles (θ, φ) on the Bloch sphere
    σ_n = sin(θ)cos(φ)σ_x + sin(θ)sin(φ)σ_y + cos(θ)σ_z -/
noncomputable def pauli_direction (paulis : PauliOperators) (θ φ : ℝ)
    (h_phys : PhysicsAssumption AssumptionId.quantumPauliDirectionObservable
      (PauliDirectionAssumptions paulis θ φ)) : Observable Qubit where
  apply := pauliDirectionApply paulis θ φ
  linear := h_phys.linear
  hermitian := h_phys.hermitian

/-- Tensor product of observables on a tensor product space.
    Given observables A on H₁ and B on H₂, this defines A ⊗ B on the tensor product.
    This is kept abstract as the detailed construction depends on the tensor product structure. -/
structure TensorObservable {H₁ H₂ : Type*}
    [QuantumStateSpace H₁] [QuantumStateSpace H₂]
    (T : TensorProductSpace H₁ H₂) (A : Observable H₁) (B : Observable H₂) where
  /-- The tensor product observable on the carrier space -/
  obs : Observable T.carrier
  /-- Action on simple tensors: (A ⊗ B)(ψ ⊗ φ) = (Aψ) ⊗ (Bφ) -/
  action_on_tensors : ∀ (ψ : H₁) (φ : H₂),
    obs.apply (T.tensor ψ φ) = T.tensor (A.apply ψ) (B.apply φ)

/-- Notation for tensor observable (requires explicit tensor product structure) -/
notation:100 A " ⊗ᴼ[" T "] " B => TensorObservable T A B

-- ========================================
-- BELL STATE SPIN CORRELATIONS
-- ========================================

/-- Singlet state spin correlation (standard QM calculation)

    For the singlet state |ψ⟩ = (|01⟩ - |10⟩)/√2,
    measuring spin along directions a and b gives:
    ⟨ψ| σ_a ⊗ σ_b |ψ⟩ = -cos(a - b)

    This is the famous quantum mechanical prediction for EPR pairs. -/
theorem singlet_pauli_correlation (basis : QubitBasis)
    (bell : BellState basis qubitTensorProduct)
    (paulis : PauliOperators) (a b : ℝ)
    (h_pauli_a : PhysicsAssumption AssumptionId.quantumPauliDirectionObservable
      (PauliDirectionAssumptions paulis (Real.pi / 2) a))
    (h_pauli_b : PhysicsAssumption AssumptionId.quantumPauliDirectionObservable
      (PauliDirectionAssumptions paulis (Real.pi / 2) b))
    (tensorObs : TensorObservable qubitTensorProduct
      (pauli_direction paulis (Real.pi / 2) a h_pauli_a)
      (pauli_direction paulis (Real.pi / 2) b h_pauli_b))
    (h_phys : PhysicsAssumption AssumptionId.quantumSingletPauliCorrelation
      (expectation_value (singlet basis bell) tensorObs.obs =
        -Real.cos (a - b))) :
    expectation_value (singlet basis bell) tensorObs.obs =
    -Real.cos (a - b) := by
  exact h_phys

end PhysicsLogic.Quantum
