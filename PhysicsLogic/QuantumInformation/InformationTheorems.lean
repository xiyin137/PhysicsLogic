import PhysicsLogic.Quantum
import PhysicsLogic.QuantumInformation.Entanglement
import PhysicsLogic.Assumptions

namespace PhysicsLogic.QuantumInformation

open Quantum QuantumInformation

/-- Structure for quantum information protocols -/
structure InformationProtocols (H : Type _) [QuantumStateSpace H]
    (T : TensorProductSpace H H) where
  /-- Reference ancilla state -/
  ancilla : H
  /-- Quantum teleportation protocol -/
  teleportation : PureState H → DensityOperator T.carrier → H
  /-- Dense coding protocol -/
  denseCoding : DensityOperator T.carrier → ℝ

/-- Structure for qubit information protocols with capacity results -/
structure QubitInformationProtocols
    (ip : InformationProtocols Qubit qubitTensorProduct) where
  /-- Dense coding achieves 2 bits per qubit with maximally entangled state -/
  dense_coding_capacity :
    ∃ (rho : DensityOperator QubitPair), ip.denseCoding rho = 2

/-- Structure for quantum error correction -/
structure QECCTheory (H : Type _) [QuantumStateSpace H] where
  /-- Type of quantum error correction codes [[n,k,d]] -/
  QECC : ℕ → ℕ → ℕ → Type _
  /-- Quantum Hamming bound -/
  quantum_hamming_bound : ∀ (n k d : ℕ), QECC n k d → Prop

/-- Structure for black hole information theory -/
structure BlackHoleInformation where
  /-- Page curve for evaporating black hole -/
  page_curve : TimeScale → EntropyMeasure → EntropyMeasure
  /-- Page time: when radiation entropy equals black hole entropy -/
  page_time : EntropyMeasure → TimeScale

/-- Teleportation classical cost (2 classical bits for qubits) -/
def teleportation_classical_cost : ℝ := 2

variable {H : Type _} [QuantumStateSpace H]

/-- Entropy functionals entering strong subadditivity for a fixed tripartite state space. -/
structure StrongSubadditivityData {HA HB HC : Type _}
    [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
    (T_BC : TensorProductSpace HB HC)
    (T_A_BC : TensorProductSpace HA T_BC.carrier) where
  /-- Entropy of the full state ρ_{ABC}. -/
  entropyABC : DensityOperator T_A_BC.carrier → ℝ
  /-- Entropy of the reduced state ρ_{AB}. -/
  entropyAB : DensityOperator T_A_BC.carrier → ℝ
  /-- Entropy of the reduced state ρ_{BC}. -/
  entropyBC : DensityOperator T_A_BC.carrier → ℝ
  /-- Entropy of the reduced state ρ_B. -/
  entropyB : DensityOperator T_A_BC.carrier → ℝ

/-- Strong subadditivity (SSA).

    This is a THEOREM (Lieb-Ruskai 1973), not an axiom itself. -/
theorem strong_subadditivity {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
  (T_BC : TensorProductSpace HB HC)
  (T_A_BC : TensorProductSpace HA T_BC.carrier)
  (ssa : StrongSubadditivityData T_BC T_A_BC)
  (rho : DensityOperator T_A_BC.carrier)
  (h_phys : PhysicsAssumption AssumptionId.qiStrongSubadditivity
    (ssa.entropyABC rho + ssa.entropyB rho ≤ ssa.entropyAB rho + ssa.entropyBC rho)) :
  ssa.entropyABC rho + ssa.entropyB rho ≤ ssa.entropyAB rho + ssa.entropyBC rho := by
  exact h_phys

/-- No-cloning theorem (Wootters-Zurek 1982, Dieks 1982).

    This is a THEOREM (provable from linearity of quantum mechanics), not an axiom itself.
    Takes a tensor product structure as parameter. -/
structure CloningMap (H : Type _) [QuantumStateSpace H]
    (T : TensorProductSpace H H) where
  /-- Candidate universal cloning map on two-copy states. -/
  map : T.carrier → T.carrier
  /-- Linearity constraint from quantum dynamics. -/
  linear : ∀ (a : ℂ) (ψ φ : T.carrier), map (a • ψ + φ) = a • map ψ + map φ

theorem no_cloning
  (T : TensorProductSpace H H)
  (ip : InformationProtocols H T)
  (h_phys : PhysicsAssumption AssumptionId.qiNoCloning
    (¬∃ (cloning : CloningMap H T),
      ∀ (psi : H), cloning.map (T.tensor psi ip.ancilla) = T.tensor psi psi)) :
  ¬∃ (cloning : CloningMap H T),
    ∀ (psi : H), cloning.map (T.tensor psi ip.ancilla) = T.tensor psi psi := by
  exact h_phys

/-- Linear deleting-channel candidates acting on two-copy inputs. -/
structure DeletingMap (H : Type _) [QuantumStateSpace H]
    (T : TensorProductSpace H H) where
  /-- Candidate deleting map on two-copy states. -/
  map : T.carrier → T.carrier
  /-- Linearity constraint from quantum dynamics. -/
  linear : ∀ (a : ℂ) (ψ φ : T.carrier), map (a • ψ + φ) = a • map ψ + map φ

/-- No-deleting theorem (Pati-Braunstein 2000).

    This is a THEOREM (provable from unitarity), not an axiom itself. -/
theorem no_deleting
  (T : TensorProductSpace H H)
  (h_phys : PhysicsAssumption AssumptionId.qiNoDeleting
    (¬∃ (deleting : DeletingMap H T) (blank : H),
      ∀ (psi : H), deleting.map (T.tensor psi psi) = T.tensor psi blank)) :
  ¬∃ (deleting : DeletingMap H T) (blank : H),
    ∀ (psi : H), deleting.map (T.tensor psi psi) = T.tensor psi blank := by
  exact h_phys

/-- No-broadcasting theorem (Barnum et al. 1996).

    This is a THEOREM (provable from quantum mechanics), not an axiom itself. -/
structure BroadcastingMap (H : Type _) [QuantumStateSpace H]
    (T : TensorProductSpace H H) where
  /-- Candidate broadcasting map on density operators. -/
  map : DensityOperator H → DensityOperator T.carrier

theorem no_broadcasting
  (T : TensorProductSpace H H)
  (pt1 : PartialTrace1 T)
  (pt2 : PartialTrace2 T)
  (h_phys : PhysicsAssumption AssumptionId.qiNoBroadcasting
    (¬∃ (broadcast : BroadcastingMap H T),
      ∀ (rho : DensityOperator H),
        pt1.trace (broadcast.map rho) = rho ∧
        pt2.trace (broadcast.map rho) = rho)) :
  ¬∃ (broadcast : BroadcastingMap H T),
    ∀ (rho : DensityOperator H),
      pt1.trace (broadcast.map rho) = rho ∧
      pt2.trace (broadcast.map rho) = rho := by
  exact h_phys

end PhysicsLogic.QuantumInformation
