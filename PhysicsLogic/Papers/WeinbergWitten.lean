import PhysicsLogic.Assumptions
import PhysicsLogic.Symmetries.Lorentz
import PhysicsLogic.Symmetries.Poincare
import PhysicsLogic.Symmetries.Representations
import PhysicsLogic.ClassicalFieldTheory.EnergyMomentum
import PhysicsLogic.QFT.Wightman
import PhysicsLogic.QFT.Smatrix
import PhysicsLogic.QFT.PathIntegral
import PhysicsLogic.Quantum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic.Linarith

/-!
# Weinberg-Witten theorem

This module formalizes the logical core of the Weinberg-Witten no-go theorem
(Weinberg & Witten, Phys. Lett. B 96 (1980) 59).

## Theorem statements

1. **Current branch**: A massless one-particle state carrying nonzero charge
   of a Lorentz-covariant conserved 4-current must have helicity `|h| ≤ 1/2`.
2. **Stress branch**: A massless one-particle state with a nonzero rotation
   eigenmode of an off-forward Lorentz-covariant conserved stress-tensor matrix
   element must have helicity `|h| ≤ 1`.

## Formalization strategy

The current branch still packages the hard QFT step as an explicit no-go
proposition, accessed through `PhysicsAssumption`.

The stress branch is split into two pieces.

1. The algebraic rotation argument from the stringbook prologue is proved in
   Lean: in a frame with `\vec p' = -\vec p`, the matrix element
   `⟨p', h| T_{μν}(0) |p, h⟩` picks up the helicity phase `e^{2 i h θ}` from
   the states, while an explicit nonzero tensor rotation eigenmode only allows
   rotation weights `0, ±1, ±2`. This yields `|h| ≤ 1`.
2. The final analytic bridge is recorded as typed sequence data:
   a family `p'_n → p` of off-forward rotation-frame setups together with
   continuity of a chosen tensor mode and the forward-limit normalization
   `⟨p', h|T_{μν}(0)|p, h⟩ → p_μ p_ν / ((2π)^3 p^0)`. This yields the final
   contradiction for local stress tensors when `spin > 1`.

The structures connect to the project's QFT library:
- `PureState H` and `OnShellMomentum` for one-particle states
- `FieldDistribution H 4` for operator-valued current/stress distributions
- `WightmanQFT`, `NoetherCurrentData`, and `ContinuousSymmetry` for the operator
  and path-integral interfaces
- `PhysicsAssumption` with `AssumptionId` for traceable unresolved inputs
-/

namespace PhysicsLogic.Paper.WeinbergWitten

open PhysicsLogic PhysicsLogic.Symmetries PhysicsLogic.Quantum SpaceTime
open PhysicsLogic.QFT.Smatrix PhysicsLogic.QFT.Wightman PhysicsLogic.QFT.PathIntegral
open scoped ComplexConjugate

set_option autoImplicit false

/-! ## Massless one-particle states -/

/-- Massless one-particle state in 4D, living in a Hilbert space `H`.

For massless particles, the little group is `ISO(2)` and physical
one-particle states are classified by a helicity `h`. Instead of an opaque
labeling `Prop`, we record actual eigenstate data for a momentum operator and a
helicity operator acting on the Hilbert space. -/
structure MomentumHelicityEigenstateData
    (H : Type _) [QuantumStateSpace H]
    (ket : PureState H) (momentum : OnShellMomentum (0 : InvariantMass))
    (helicity : ℝ) where
  /-- Abstract four-momentum operators acting on the Hilbert space. -/
  momentumOperator : Fin 4 → H → H
  /-- Abstract helicity operator. -/
  helicityOperator : H → H
  /-- `ket` is an eigenstate of the momentum operator with eigenvalue `p^μ`. -/
  momentum_eigenvector :
    ∀ μ, momentumOperator μ ket.vec = ((momentum.p μ : ℝ) : ℂ) • ket.vec
  /-- `ket` is an eigenstate of the helicity operator with eigenvalue `h`. -/
  helicity_eigenvector :
    helicityOperator ket.vec = ((helicity : ℝ) : ℂ) • ket.vec

structure MasslessOneParticleState (H : Type _) [QuantumStateSpace H] where
  /-- Underlying normalized state vector in the Hilbert space. -/
  ket : PureState H
  /-- Positive-energy on-shell momentum with invariant mass `m = 0`. -/
  momentum : OnShellMomentum (0 : InvariantMass)
  /-- Helicity quantum number `h`. -/
  helicity : ℝ
  /-- Physical spin magnitude. -/
  spin : ℝ
  /-- Eigenstate data realizing this state as `|p, h⟩`. -/
  eigenstateData : MomentumHelicityEigenstateData H ket momentum helicity
  spin_nonneg : 0 ≤ spin
  spin_eq_abs_helicity : spin = |helicity|

/-! ## Shared QFT interfaces -/

/-- Four-dimensional Minkowski point (alias for path-integral spacetime). -/
abbrev MinkowskiPoint := Fin 4 → ℝ

/-- Lorentz-vector operator-valued distribution `J^μ(x)`. -/
abbrev LorentzVectorDistribution (H : Type _) [QuantumStateSpace H] :=
  Fin 4 → FieldDistribution H 4

/-- Rank-two operator-valued distribution `T^{μν}(x)`. -/
abbrev RankTwoTensorDistribution (H : Type _) [QuantumStateSpace H] :=
  Fin 4 → Fin 4 → FieldDistribution H 4

/-- Charge matrix-element functional evaluated on one-particle states. -/
abbrev ChargeFunctional (H : Type _) [QuantumStateSpace H] :=
  PureState H → ComplexAmplitude

/-- Stress-tensor matrix element `⟨bra|T^{μν}(0)|ket⟩`. -/
abbrev StressMatrixElementFunctional (H : Type _) [QuantumStateSpace H] :=
  Fin 4 → Fin 4 → PureState H → PureState H → ComplexAmplitude

/-- The back-to-back frame used in the stringbook rotation argument:
equal energies and opposite spatial momenta. -/
def BackToBackSpatialMomenta
    (p p' : OnShellMomentum (0 : InvariantMass)) : Prop :=
  p'.p 0 = p.p 0 ∧ ∀ i : Fin 3, p'.p i.succ = -p.p i.succ

/-- Concrete relation between a charge functional and the zero component of a
stored current distribution, via a chosen smearing profile. -/
structure ChargeFromCurrentField
    (H : Type _) [QuantumStateSpace H]
    (currentField : LorentzVectorDistribution H)
    (chargeFunctional : ChargeFunctional H) where
  /-- Smearing profile selecting the current component used for the charge. -/
  smearing : SchwartzFunction 4
  /-- The charge functional is computed from the smeared `J^0` operator. -/
  charge_eq_current_zero :
    ∀ ψ : PureState H,
      chargeFunctional ψ =
        innerProduct ψ.vec (((currentField 0).toSmeared smearing).apply ψ.vec)

/-- Minimal bridge from the operator current to the path-integral Noether
current, expressed as a vacuum matrix-element comparison on explicit data. -/
structure CurrentNoetherVacuumBridge
    (H : Type _) [QuantumStateSpace H] (FieldConfig : Type*)
    (qft : WightmanQFT H 4)
    {action : ActionFunctional FieldConfig}
    (noetherCurrent : NoetherCurrentData FieldConfig MinkowskiPoint 4 action)
    (currentField : LorentzVectorDistribution H) where
  /-- Explicit path-integral field configuration used for comparison. -/
  fieldConfig : FieldConfig
  /-- Explicit spacetime point used for comparison. -/
  point : MinkowskiPoint
  /-- Smearing profile used on the operator side. -/
  smearing : SchwartzFunction 4
  /-- Vacuum matrix elements of the operator current recover the chosen
  Noether current components on the comparison data. -/
  vacuum_component_matches :
    ∀ μ,
      (innerProduct qft.vacuumFieldOps.vacuum
        (((currentField μ).toSmeared smearing).apply qft.vacuumFieldOps.vacuum)).re =
      noetherCurrent.current fieldConfig point μ

/-- Concrete relation between off-forward matrix elements and the stored stress
tensor distribution, again through a chosen smearing profile. -/
structure StressTensorMatrixElementFromField
    (H : Type _) [QuantumStateSpace H]
    (stressTensor : RankTwoTensorDistribution H)
    (stressMatrixElement : StressMatrixElementFunctional H)
    (bra ket : PureState H) where
  /-- Smearing profile selecting the local tensor insertion. -/
  smearing : SchwartzFunction 4
  /-- The matrix element is computed from the smeared tensor operator. -/
  matrix_element_eq :
    ∀ μ ν,
      stressMatrixElement μ ν bra ket =
        innerProduct bra.vec (((stressTensor μ ν).toSmeared smearing).apply ket.vec)

/-- Conservation equation for a concrete off-forward stress-tensor matrix
element. -/
def ConservedStressMatrixElement
    (H : Type _) [QuantumStateSpace H]
    (stressMatrixElement : StressMatrixElementFunctional H)
    (braMomentum ketMomentum : OnShellMomentum (0 : InvariantMass))
    (bra ket : PureState H) : Prop :=
  ∀ ν : Fin 4,
    ∑ μ : Fin 4,
      ((((braMomentum.p μ - ketMomentum.p μ : ℝ) : ℂ)) *
        stressMatrixElement μ ν bra ket) = 0

/-- Rotation phase `e^{i w θ}` used in the stress-branch argument. -/
noncomputable def rotationPhase (weight θ : ℝ) : ComplexAmplitude :=
  Complex.exp (Complex.I * (((weight * θ : ℝ) : ℂ)))

/-- Possible rotation weights for a rank-two tensor under rotations around the
momentum axis.

The vector representation has weights `0, 0, 1, -1`, so the tensor product can
only carry `-2, -1, 0, 1, 2`. -/
inductive TensorRotationWeight
  | minusTwo
  | minusOne
  | zero
  | plusOne
  | plusTwo
deriving DecidableEq, Repr

/-- Numeric value of an allowed stress-tensor rotation weight. -/
def TensorRotationWeight.toReal : TensorRotationWeight → ℝ
  | .minusTwo => -2
  | .minusOne => -1
  | .zero => 0
  | .plusOne => 1
  | .plusTwo => 2

/-- Every allowed tensor weight has absolute value at most `2`. -/
lemma TensorRotationWeight.abs_toReal_le_two (w : TensorRotationWeight) :
    |w.toReal| ≤ (2 : ℝ) := by
  cases w <;> norm_num [TensorRotationWeight.toReal]

/-- A complex linear combination of off-forward stress-tensor components. -/
noncomputable def tensorModeValue
    {H : Type _} [QuantumStateSpace H]
    (coeff : Fin 4 → Fin 4 → ComplexAmplitude)
    (stressMatrixElement : StressMatrixElementFunctional H)
    (bra ket : PureState H) : ComplexAmplitude :=
  ∑ μ, ∑ ν, coeff μ ν * stressMatrixElement μ ν bra ket

/-- The same linear combination, evaluated on the rotated matrix element. -/
noncomputable def rotatedTensorModeValue
    (coeff : Fin 4 → Fin 4 → ComplexAmplitude)
    (rotatedStressMatrixElement : Fin 4 → Fin 4 → ℝ → ComplexAmplitude)
    (θ : ℝ) : ComplexAmplitude :=
  ∑ μ, ∑ ν, coeff μ ν * rotatedStressMatrixElement μ ν θ

/-- A rotation mode of the off-forward stress-tensor matrix element.

This is the honest representation-theoretic input on the tensor side of the
stringbook argument: instead of pretending that each Cartesian component has a
definite weight, we choose an explicit complex linear combination of tensor
components that transforms with one allowed weight in `{-2,-1,0,1,2}`. -/
structure TensorRotationMode
    (H : Type _) [QuantumStateSpace H]
    (stressMatrixElement : StressMatrixElementFunctional H)
    (bra ket : PureState H)
    (rotatedStressMatrixElement : Fin 4 → Fin 4 → ℝ → ComplexAmplitude) where
  /-- Coefficients selecting a helicity-adapted tensor mode. -/
  coeff : Fin 4 → Fin 4 → ComplexAmplitude
  /-- Allowed weight carried by the selected mode. -/
  weight : TensorRotationWeight
  /-- The rotated mode carries the assigned phase for all angles. -/
  mode_rotation :
    ∀ θ,
      rotatedTensorModeValue coeff rotatedStressMatrixElement θ =
        rotationPhase weight.toReal θ *
          tensorModeValue coeff stressMatrixElement bra ket

/-- A nonzero rotation eigenmode of the off-forward stress-tensor matrix
element. -/
structure TensorRotationEigenmode
    (H : Type _) [QuantumStateSpace H]
    (stressMatrixElement : StressMatrixElementFunctional H)
    (bra ket : PureState H)
    (rotatedStressMatrixElement : Fin 4 → Fin 4 → ℝ → ComplexAmplitude)
    extends TensorRotationMode H stressMatrixElement bra ket rotatedStressMatrixElement where
  /-- The chosen mode is nonzero at `θ = 0`. -/
  nonzero :
    tensorModeValue coeff stressMatrixElement bra ket ≠ 0

/-- Forward-limit stress-tensor matrix element predicted by momentum
normalization in the stringbook argument. -/
noncomputable def forwardStressTensorEntry
    (p : OnShellMomentum (0 : InvariantMass)) (μ ν : Fin 4) : ComplexAmplitude :=
  ((((p.p μ * p.p ν) / (((2 * Real.pi) ^ (3 : ℕ)) * p.p 0) : ℝ)) : ℂ)

/-- The forward-limit value of a chosen tensor rotation mode. -/
noncomputable def forwardTensorModeValue
    (coeff : Fin 4 → Fin 4 → ComplexAmplitude)
    (p : OnShellMomentum (0 : InvariantMass)) : ComplexAmplitude :=
  ∑ μ, ∑ ν, coeff μ ν * forwardStressTensorEntry p μ ν

/-- A concrete rotation action on a one-particle state with a fixed phase
weight.

This packages the state-side input in the stringbook argument as actual
unitaries on the Hilbert space rather than a bare proposition about matrix
elements. -/
structure StateRotationAction
    (H : Type _) [QuantumStateSpace H]
    (state : MasslessOneParticleState H)
    (weight : ℝ) where
  /-- The rotation unitary for each angle `θ`. -/
  unitary : ℝ → UnitaryOp H
  /-- The chosen state is an eigenvector of that rotation action. -/
  phase_eigenvector :
    ∀ θ, (unitary θ).op state.ket.vec = rotationPhase weight θ • state.ket.vec

/-- The rotated pure state obtained from the stored unitary action. -/
def StateRotationAction.rotatedState
    {H : Type _} [QuantumStateSpace H]
    {state : MasslessOneParticleState H} {weight : ℝ}
    (action : StateRotationAction H state weight) (θ : ℝ) : PureState H :=
  (action.unitary θ).applyPure state.ket

/-- The rotated-state vector is the expected phase multiple of the original
state vector. -/
lemma StateRotationAction.rotatedState_vec
    {H : Type _} [QuantumStateSpace H]
    {state : MasslessOneParticleState H} {weight : ℝ}
    (action : StateRotationAction H state weight) (θ : ℝ) :
    (action.rotatedState θ).vec = rotationPhase weight θ • state.ket.vec :=
  action.phase_eigenvector θ

/-- A smeared field operator annihilates the zero vector. -/
lemma SmearedFieldOperator.apply_zero
    {H : Type _} [QuantumStateSpace H] {d : ℕ}
    (A : SmearedFieldOperator H d) :
    A.apply 0 = 0 := by
  have h : A.apply 0 = A.apply 0 + A.apply 0 := by
    simpa using A.linear (1 : ℂ) (0 : H) 0
  have h' := congrArg (fun x : H => x - A.apply 0) h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'.symm

/-- A smeared field operator is homogeneous with respect to complex scalars. -/
lemma SmearedFieldOperator.apply_smul
    {H : Type _} [QuantumStateSpace H] {d : ℕ}
    (A : SmearedFieldOperator H d) (a : ℂ) (ψ : H) :
    A.apply (a • ψ) = a • A.apply ψ := by
  simpa [SmearedFieldOperator.apply_zero] using A.linear a ψ 0

/-- Rotation phases add in the expected way. -/
lemma rotationPhase_add (a b θ : ℝ) :
    rotationPhase a θ * rotationPhase b θ = rotationPhase (a + b) θ := by
  calc
    rotationPhase a θ * rotationPhase b θ
      = Complex.exp (Complex.I * (((a * θ : ℝ) : ℂ))) *
          Complex.exp (Complex.I * (((b * θ : ℝ) : ℂ))) := rfl
    _ = Complex.exp
          ((Complex.I * (((a * θ : ℝ) : ℂ))) +
            (Complex.I * (((b * θ : ℝ) : ℂ)))) := by
          rw [← Complex.exp_add]
    _ = Complex.exp (Complex.I * ((((a + b) * θ : ℝ) : ℂ))) := by
          congr 1
          rw [show ((a + b) * θ : ℝ) = a * θ + b * θ by ring, Complex.ofReal_add, mul_add]
    _ = rotationPhase (a + b) θ := rfl

/-- Complex conjugation flips the sign of the rotation weight. -/
lemma star_rotationPhase (a θ : ℝ) :
    star (rotationPhase a θ) = rotationPhase (-a) θ := by
  calc
    star (rotationPhase a θ)
      = Complex.exp (conj (Complex.I * (((a * θ : ℝ) : ℂ)))) := by
          simpa [rotationPhase] using
            (Complex.exp_conj (Complex.I * (((a * θ : ℝ) : ℂ)))).symm
    _ = Complex.exp (Complex.I * ((((-a) * θ : ℝ) : ℂ))) := by
          congr 1
          rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
          calc
            -Complex.I * (((a * θ : ℝ) : ℂ))
              = Complex.I * (-(((a * θ : ℝ) : ℂ))) := by ring
            _ = Complex.I * ((((-a) * θ : ℝ) : ℂ)) := by
              congr 1
              rw [← Complex.ofReal_neg]
              congr 1
              ring
    _ = rotationPhase (-a) θ := rfl

lemma rotationPhase_sub_mul (a b θ : ℝ) :
    rotationPhase (a - b) θ =
      rotationPhase a θ * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) := by
  calc
    rotationPhase (a - b) θ = Complex.exp (Complex.I * ((((a - b) * θ : ℝ) : ℂ))) := rfl
    _ = Complex.exp
          ((Complex.I * (((a * θ : ℝ) : ℂ))) + (-(Complex.I * (((b * θ : ℝ) : ℂ))))) := by
          congr 1
          rw [sub_mul, Complex.ofReal_sub, mul_sub, sub_eq_add_neg]
    _ = rotationPhase a θ * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) := by
          rw [rotationPhase, Complex.exp_add]

lemma rotationPhase_self_mul_inv (b θ : ℝ) :
    rotationPhase b θ * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) = 1 := by
  calc
    rotationPhase b θ * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) =
        Complex.exp
          ((Complex.I * (((b * θ : ℝ) : ℂ))) + (-(Complex.I * (((b * θ : ℝ) : ℂ))))) := by
            rw [rotationPhase, ← Complex.exp_add]
    _ = Complex.exp 0 := by
          congr 1
          ring_nf
    _ = 1 := by simp

/-- If two rotation phases agree at the same angle, then the phase difference is `1`. -/
lemma rotationPhase_sub_eq_one {a b θ : ℝ}
    (h : rotationPhase a θ = rotationPhase b θ) :
    rotationPhase (a - b) θ = 1 := by
  have h' := congrArg
    (fun z : ℂ => z * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) ) h
  calc
    rotationPhase (a - b) θ =
        rotationPhase a θ * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) :=
      rotationPhase_sub_mul a b θ
    _ = rotationPhase b θ * Complex.exp (-(Complex.I * (((b * θ : ℝ) : ℂ)))) := h'
    _ = 1 := rotationPhase_self_mul_inv b θ

/-- At the angle `π / (a - b)`, the relative phase between unequal weights is `-1`. -/
lemma rotationPhase_critical_angle {a b : ℝ} (hab : a ≠ b) :
    rotationPhase (a - b) (Real.pi / (a - b)) = -1 := by
  have hdiff : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hmul : (a - b) * (Real.pi / (a - b)) = Real.pi := by
    field_simp [hdiff]
  simpa [rotationPhase, hmul, mul_comm, mul_left_comm, mul_assoc] using Complex.exp_pi_mul_I

/-- A nonzero complex component cannot simultaneously transform with two
different rotation weights for all angles. -/
lemma equal_weights_of_nonzero_rotation_component
    {a b : ℝ} {z : ComplexAmplitude}
    (hz : z ≠ 0)
    (h : ∀ θ : ℝ, rotationPhase a θ * z = rotationPhase b θ * z) :
    a = b := by
  by_contra hab
  have hphase :
      rotationPhase a (Real.pi / (a - b)) =
        rotationPhase b (Real.pi / (a - b)) := by
    exact (mul_left_injective₀ hz) (h (Real.pi / (a - b)))
  have hone :
      rotationPhase (a - b) (Real.pi / (a - b)) = 1 :=
    rotationPhase_sub_eq_one hphase
  have hneg :
      rotationPhase (a - b) (Real.pi / (a - b)) = -1 :=
    rotationPhase_critical_angle hab
  have : (1 : ℂ) = -1 := hone.symm.trans hneg
  norm_num at this

/-! ## Current-branch setup -/

/-- Current-branch data for Weinberg-Witten.

The current branch keeps the hard boost-scaling step abstract: the core QFT
derivation remains packaged as `CurrentWeinbergWittenNoGo`. -/
structure CurrentBranchSetup (H : Type _) [QuantumStateSpace H] where
  /-- Ambient relativistic QFT in operator language. -/
  qft : WightmanQFT H 4
  /-- Field-configuration space for the path-integral current package. -/
  FieldConfig : Type*
  /-- Path-integral presentation of the same theory. -/
  pathIntegral : PathIntegralData FieldConfig
  /-- Noether-current data for the relevant continuous symmetry. -/
  noetherCurrent : NoetherCurrentData FieldConfig MinkowskiPoint 4 pathIntegral.action
  /-- Massless one-particle state under study. -/
  state : MasslessOneParticleState H
  /-- Operator-valued current `J^μ(x)`. -/
  currentField : LorentzVectorDistribution H
  /-- Charge functional `⟨ψ|Q|ψ⟩`. -/
  chargeFunctional : ChargeFunctional H
  /-- Explicit bridge comparing the operator current to path-integral Noether data. -/
  currentNoetherBridge :
    CurrentNoetherVacuumBridge H FieldConfig qft noetherCurrent currentField
  /-- Concrete formula for the charge in terms of the stored current distribution. -/
  chargeFromCurrent :
    ChargeFromCurrentField H currentField chargeFunctional

/-- The state carries nonzero current charge. -/
def CarriesNonzeroCurrentCharge
    {H : Type _} [QuantumStateSpace H] (setup : CurrentBranchSetup H) : Prop :=
  setup.chargeFunctional setup.state.ket ≠ 0

/-- Hard current-branch Weinberg-Witten step, kept as a traceable assumption. -/
def CurrentWeinbergWittenNoGo
    {H : Type _} [QuantumStateSpace H] (setup : CurrentBranchSetup H) : Prop :=
  (1 / 2 : ℝ) < |setup.state.helicity| →
    setup.chargeFunctional setup.state.ket = 0

/-! ## Stress-tensor branch setup -/

/-- Stress-tensor branch data for the stringbook rotation argument.

`state` models `|p, h⟩`. The field `statePrime` models `|p', h⟩` in a frame with
`\vec p' = -\vec p`. The fields `incomingRotation`, `outgoingRotation`, and
`tensorMode` are the two sides of the book's covariance equation:

`R_μ{}^ρ(θ) R_ν{}^σ(θ) ⟨p', h| T_{ρσ}(0) |p, h⟩ = e^{2 i h θ} ⟨p', h| T_{μν}(0) |p, h⟩`.

The local-QFT ingredients (`stressTensor`, translation symmetry, conservation)
remain visible in the interface even though the rotation proof of `|h| ≤ 1`
only uses the phase-matching data. On the tensor side we package an explicit
rotation mode, rather than assigning fixed weights to Cartesian components. -/
structure StressRotationFrameSetup (H : Type _) [QuantumStateSpace H] where
  /-- Ambient relativistic QFT in operator language. -/
  qft : WightmanQFT H 4
  /-- Field-configuration space for the path-integral translation symmetry. -/
  FieldConfig : Type*
  /-- Path-integral presentation of the same theory. -/
  pathIntegral : PathIntegralData FieldConfig
  /-- Translation symmetry generating the stress tensor. -/
  translationSymmetry : ContinuousSymmetry FieldConfig pathIntegral.action
  /-- Incoming massless one-particle state `|p, h⟩`. -/
  state : MasslessOneParticleState H
  /-- Outgoing massless one-particle state `|p', h⟩`. -/
  statePrime : MasslessOneParticleState H
  /-- The incoming and outgoing states carry the same helicity label. -/
  sameHelicity : statePrime.helicity = state.helicity
  /-- In the chosen Lorentz frame, the momenta are back-to-back. -/
  backToBackFrame : BackToBackSpatialMomenta state.momentum statePrime.momentum
  /-- Operator-valued stress tensor `T^{μν}(x)`. -/
  stressTensor : RankTwoTensorDistribution H
  /-- Off-forward matrix element `⟨p', h|T^{μν}(0)|p, h⟩`. -/
  stressMatrixElement : StressMatrixElementFunctional H
  /-- Concrete formula relating the matrix element to the stored stress tensor. -/
  matrixElementFromTensor :
    StressTensorMatrixElementFromField H stressTensor stressMatrixElement statePrime.ket state.ket
  /-- Concrete off-forward conservation law for the matrix element. -/
  conservedMatrixElement :
    ConservedStressMatrixElement
      H stressMatrixElement statePrime.momentum state.momentum statePrime.ket state.ket
  /-- Rotation action on the incoming state `|p, h⟩`. -/
  incomingRotation : StateRotationAction H state state.helicity
  /-- Rotation action on the outgoing state `|p', h⟩`.

  Because `\vec p' = -\vec p`, the ket transforms with the opposite phase
  weight under rotations around the `\vec p` axis. -/
  outgoingRotation : StateRotationAction H statePrime (-statePrime.helicity)
  /-- A chosen rotation mode of the off-forward tensor matrix element. -/
  tensorMode :
    TensorRotationMode
      H stressMatrixElement statePrime.ket state.ket
      (fun μ ν θ =>
        innerProduct
          ((outgoingRotation.rotatedState θ).vec)
          (((stressTensor μ ν).toSmeared matrixElementFromTensor.smearing).apply
            ((incomingRotation.rotatedState θ).vec)))

/-- Stress-tensor branch setup with a nonzero off-forward tensor rotation
eigenmode. This is the precise off-forward input needed for the algebraic
rotation obstruction. -/
structure StressBranchSetup (H : Type _) [QuantumStateSpace H]
    extends StressRotationFrameSetup H where
  /-- The chosen tensor mode is nonzero off-forward. -/
  tensorMode_nonzero :
    tensorModeValue tensorMode.coeff stressMatrixElement statePrime.ket state.ket ≠ 0

/-- Rotated off-forward stress-tensor matrix element constructed from the
stored rotation actions on the bra/ket states. -/
noncomputable def StressRotationFrameSetup.rotatedStressMatrixElement
    {H : Type _} [QuantumStateSpace H]
    (setup : StressRotationFrameSetup H) (μ ν : Fin 4) (θ : ℝ) : ComplexAmplitude :=
  innerProduct
    ((setup.outgoingRotation.rotatedState θ).vec)
    (((setup.stressTensor μ ν).toSmeared setup.matrixElementFromTensor.smearing).apply
      ((setup.incomingRotation.rotatedState θ).vec))

/-- Convenience alias for the rotated matrix element on a nonzero stress branch
setup. -/
noncomputable def StressBranchSetup.rotatedStressMatrixElement
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H) (μ ν : Fin 4) (θ : ℝ) : ComplexAmplitude :=
  setup.toStressRotationFrameSetup.rotatedStressMatrixElement μ ν θ

/-- Sequence-based forward-limit bridge for the stress-tensor branch.

This packages the missing analytic step from the stringbook argument:

1. choose a fixed incoming state `|p,h⟩`,
2. choose off-forward rotation-frame data `|p'_n,h⟩` with `p'_n → p`,
3. assume the chosen tensor mode is continuous along that sequence,
4. identify the forward limit with the momentum-normalized value
   `p_μ p_ν / ((2π)^3 p^0)` projected onto the same mode.

The locality/wave-packet argument from the book is not re-proved here, but its
mathematical output is now recorded as actual convergence data rather than a
docstring remark. -/
structure StressForwardLimitBridge (H : Type _) [QuantumStateSpace H] where
  /-- Incoming massless one-particle state whose stress tensor is being tested. -/
  targetState : MasslessOneParticleState H
  /-- The local stress tensor shared across the off-forward family. -/
  stressTensor : RankTwoTensorDistribution H
  /-- Fixed tensor-mode coefficients used both off-forward and in the forward limit. -/
  modeCoeff : Fin 4 → Fin 4 → ComplexAmplitude
  /-- A sequence of off-forward rotation-frame setups approaching the forward limit. -/
  offForward : ℕ → StressRotationFrameSetup H
  /-- Each off-forward setup uses the same incoming state `|p,h⟩`. -/
  incomingState_eq : ∀ n, (offForward n).state = targetState
  /-- Each off-forward setup uses the same local stress tensor. -/
  stressTensor_eq : ∀ n, (offForward n).stressTensor = stressTensor
  /-- The chosen tensor-mode coefficients are fixed along the sequence. -/
  modeCoeff_eq : ∀ n, (offForward n).tensorMode.coeff = modeCoeff
  /-- The outgoing momentum approaches the incoming momentum componentwise. -/
  outgoingMomentum_tendsto :
    ∀ μ : Fin 4,
      Filter.Tendsto
        (fun n => (offForward n).statePrime.momentum.p μ)
        Filter.atTop
        (nhds (targetState.momentum.p μ))
  /-- Continuity of the chosen off-forward tensor mode along `p'_n → p`. -/
  modeValue_tendsto :
    Filter.Tendsto
      (fun n =>
        tensorModeValue
          modeCoeff
          (offForward n).stressMatrixElement
          (offForward n).statePrime.ket
          (offForward n).state.ket)
      Filter.atTop
      (nhds (forwardTensorModeValue modeCoeff targetState.momentum))
  /-- The momentum-normalized forward mode is nonzero. -/
  forwardMode_nonzero :
    forwardTensorModeValue modeCoeff targetState.momentum ≠ 0

/-- The chosen off-forward tensor mode along the forward-limit sequence. -/
noncomputable def StressForwardLimitBridge.offForwardModeValue
    {H : Type _} [QuantumStateSpace H]
    (bridge : StressForwardLimitBridge H) (n : ℕ) : ComplexAmplitude :=
  tensorModeValue
    bridge.modeCoeff
    (bridge.offForward n).stressMatrixElement
    (bridge.offForward n).statePrime.ket
    (bridge.offForward n).state.ket

/-- A nonzero forward limit forces some genuinely off-forward term in the
sequence to have a nonzero tensor mode. -/
theorem StressForwardLimitBridge.exists_nonzero_offForwardMode
    {H : Type _} [QuantumStateSpace H]
    (bridge : StressForwardLimitBridge H) :
    ∃ n, bridge.offForwardModeValue n ≠ 0 := by
  by_contra h_none
  have h_zero : ∀ n, bridge.offForwardModeValue n = 0 := by
    simpa [StressForwardLimitBridge.offForwardModeValue] using not_exists.mp h_none
  have h_tendsto_zero :
      Filter.Tendsto bridge.offForwardModeValue Filter.atTop (nhds (0 : ℂ)) := by
    have h_eq :
        bridge.offForwardModeValue = fun _ : ℕ => (0 : ℂ) := by
      funext n
      exact h_zero n
    rw [h_eq]
    exact tendsto_const_nhds
  have h_unique :
      (0 : ℂ) = forwardTensorModeValue bridge.modeCoeff bridge.targetState.momentum :=
    tendsto_nhds_unique h_tendsto_zero bridge.modeValue_tendsto
  exact bridge.forwardMode_nonzero h_unique.symm

/-- Upgrade one nonzero term of the forward-limit sequence to a genuine
stress-branch setup. -/
def StressForwardLimitBridge.branchSetupAt
    {H : Type _} [QuantumStateSpace H]
    (bridge : StressForwardLimitBridge H) (n : ℕ)
    (h_nonzero : bridge.offForwardModeValue n ≠ 0) :
    StressBranchSetup H where
  toStressRotationFrameSetup := bridge.offForward n
  tensorMode_nonzero := by
    rw [bridge.modeCoeff_eq n]
    simpa [StressForwardLimitBridge.offForwardModeValue] using h_nonzero

/-! ## Current branch consequences -/

/-- Under the current-branch no-go claim, helicity is bounded by `1/2`. -/
theorem current_branch_helicity_bound
    {H : Type _} [QuantumStateSpace H]
    (setup : CurrentBranchSetup H)
    (h_charge : CarriesNonzeroCurrentCharge setup)
    (h_no_go : PhysicsAssumption
      AssumptionId.wwCurrentBranchHelicityBound
      (CurrentWeinbergWittenNoGo setup)) :
    |setup.state.helicity| ≤ (1 / 2 : ℝ) := by
  by_contra h_not_bound
  have h_high : (1 / 2 : ℝ) < |setup.state.helicity| := lt_of_not_ge h_not_bound
  exact h_charge (h_no_go h_high)

/-- Under the current-branch no-go claim, spin is bounded by `1/2`. -/
theorem current_branch_spin_bound
    {H : Type _} [QuantumStateSpace H]
    (setup : CurrentBranchSetup H)
    (h_charge : CarriesNonzeroCurrentCharge setup)
    (h_no_go : PhysicsAssumption
      AssumptionId.wwCurrentBranchHelicityBound
      (CurrentWeinbergWittenNoGo setup)) :
    setup.state.spin ≤ (1 / 2 : ℝ) := by
  calc
    setup.state.spin = |setup.state.helicity| := setup.state.spin_eq_abs_helicity
    _ ≤ (1 / 2 : ℝ) :=
      current_branch_helicity_bound setup h_charge h_no_go

/-- No-go form: a massless state with `spin > 1/2` cannot carry nonzero charge
of a Lorentz-covariant conserved current. -/
theorem no_current_charge_for_spin_gt_half
    {H : Type _} [QuantumStateSpace H]
    (setup : CurrentBranchSetup H)
    (h_spin : setup.state.spin > (1 / 2 : ℝ))
    (h_no_go : PhysicsAssumption
      AssumptionId.wwCurrentBranchHelicityBound
      (CurrentWeinbergWittenNoGo setup)) :
    ¬ CarriesNonzeroCurrentCharge setup := by
  intro h_charge
  linarith
    [current_branch_spin_bound setup h_charge h_no_go]

/-- Spin-1 corollary: a massless spin-1 particle cannot carry nonzero charge
of a Lorentz-covariant conserved current. -/
theorem spin_one_no_current_charge
    {H : Type _} [QuantumStateSpace H]
    (setup : CurrentBranchSetup H)
    (h_spin_one : setup.state.spin = 1)
    (h_no_go : PhysicsAssumption
      AssumptionId.wwCurrentBranchHelicityBound
      (CurrentWeinbergWittenNoGo setup)) :
    ¬ CarriesNonzeroCurrentCharge setup :=
  no_current_charge_for_spin_gt_half
    setup (by linarith) h_no_go

/-! ## Stress-tensor branch consequences -/

/-- The rotation actions on the incoming and outgoing states produce the
helicity phase `e^{2 i h θ}` for the off-forward stress-tensor matrix
element. -/
theorem stress_branch_matrix_element_helicity_phase
    {H : Type _} [QuantumStateSpace H]
    (setup : StressRotationFrameSetup H)
    (μ ν : Fin 4) (θ : ℝ) :
    setup.rotatedStressMatrixElement μ ν θ =
      rotationPhase (2 * setup.state.helicity) θ *
        setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket := by
  unfold StressRotationFrameSetup.rotatedStressMatrixElement Quantum.innerProduct
  rw [setup.outgoingRotation.rotatedState_vec, setup.incomingRotation.rotatedState_vec]
  rw [SmearedFieldOperator.apply_smul, inner_smul_left, inner_smul_right]
  have hphase :
      star (rotationPhase (-setup.statePrime.helicity) θ) *
          rotationPhase setup.state.helicity θ =
        rotationPhase (2 * setup.state.helicity) θ := by
    rw [star_rotationPhase, neg_neg, rotationPhase_add, setup.sameHelicity]
    congr 1
    ring
  calc
    star (rotationPhase (-setup.statePrime.helicity) θ) *
        (rotationPhase setup.state.helicity θ *
          innerProduct setup.statePrime.ket.vec
            (((setup.stressTensor μ ν).toSmeared setup.matrixElementFromTensor.smearing).apply
              setup.state.ket.vec))
      = (star (rotationPhase (-setup.statePrime.helicity) θ) *
          rotationPhase setup.state.helicity θ) *
          innerProduct setup.statePrime.ket.vec
            (((setup.stressTensor μ ν).toSmeared setup.matrixElementFromTensor.smearing).apply
              setup.state.ket.vec) := by
          ring
    _ = rotationPhase (2 * setup.state.helicity) θ *
          innerProduct setup.statePrime.ket.vec
            (((setup.stressTensor μ ν).toSmeared setup.matrixElementFromTensor.smearing).apply
              setup.state.ket.vec) := by
          rw [hphase]
    _ = rotationPhase (2 * setup.state.helicity) θ *
          setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket := by
          rw [setup.matrixElementFromTensor.matrix_element_eq μ ν]

/-- The state-induced helicity phase extends from individual tensor components
to the chosen tensor rotation eigenmode. -/
theorem stress_branch_rotation_mode_helicity_phase
    {H : Type _} [QuantumStateSpace H]
    (setup : StressRotationFrameSetup H) (θ : ℝ) :
    rotatedTensorModeValue
        setup.tensorMode.coeff
        setup.rotatedStressMatrixElement θ =
      rotationPhase (2 * setup.state.helicity) θ *
        tensorModeValue
          setup.tensorMode.coeff
          setup.stressMatrixElement
          setup.statePrime.ket
          setup.state.ket := by
  unfold rotatedTensorModeValue tensorModeValue
  simp_rw [stress_branch_matrix_element_helicity_phase]
  calc
    ∑ μ, ∑ ν,
        setup.tensorMode.coeff μ ν *
          (rotationPhase (2 * setup.state.helicity) θ *
            setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket)
      =
        ∑ μ, ∑ ν,
          rotationPhase (2 * setup.state.helicity) θ *
            (setup.tensorMode.coeff μ ν *
              setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket) := by
          refine Finset.sum_congr rfl ?_
          intro μ _
          refine Finset.sum_congr rfl ?_
          intro ν _
          ring
    _ = ∑ μ,
          rotationPhase (2 * setup.state.helicity) θ *
            ∑ ν,
              setup.tensorMode.coeff μ ν *
                setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket := by
          refine Finset.sum_congr rfl ?_
          intro μ _
          rw [← Finset.mul_sum]
    _ =
        rotationPhase (2 * setup.state.helicity) θ *
          ∑ μ, ∑ ν,
            setup.tensorMode.coeff μ ν *
              setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket := by
          rw [← Finset.mul_sum]

/-- A nonzero tensor rotation eigenmode forces `2 h` to be one of the allowed
tensor weights `-2, -1, 0, 1, 2`. -/
theorem stress_branch_double_helicity_weight
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H) :
    ∃ w : TensorRotationWeight, 2 * setup.state.helicity = w.toReal := by
  let w := setup.tensorMode.weight
  refine ⟨w, ?_⟩
  apply equal_weights_of_nonzero_rotation_component setup.tensorMode_nonzero
  intro θ
  have h_tensor :
      rotatedTensorModeValue
          setup.tensorMode.coeff
          setup.rotatedStressMatrixElement θ =
        rotationPhase w.toReal θ *
          tensorModeValue
            setup.tensorMode.coeff
            setup.stressMatrixElement
            setup.statePrime.ket
            setup.state.ket := by
    simpa [StressBranchSetup.rotatedStressMatrixElement] using
      setup.tensorMode.mode_rotation θ
  calc
    rotationPhase (2 * setup.state.helicity) θ *
        tensorModeValue
          setup.tensorMode.coeff
          setup.stressMatrixElement
          setup.statePrime.ket
          setup.state.ket
      =
        rotatedTensorModeValue
          setup.tensorMode.coeff
          setup.rotatedStressMatrixElement θ := by
          symm
          exact stress_branch_rotation_mode_helicity_phase
            setup.toStressRotationFrameSetup θ
    _ = rotationPhase w.toReal θ *
        tensorModeValue
          setup.tensorMode.coeff
          setup.stressMatrixElement
          setup.statePrime.ket
          setup.state.ket :=
      h_tensor

/-- Under the stringbook rotation argument, helicity is bounded by `1`. -/
theorem stress_branch_helicity_bound
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H) :
    |setup.state.helicity| ≤ (1 : ℝ) := by
  rcases stress_branch_double_helicity_weight setup with ⟨w, hw⟩
  have h_weight_bound : |2 * setup.state.helicity| ≤ (2 : ℝ) := by
    rw [hw]
    exact TensorRotationWeight.abs_toReal_le_two w
  have h_abs_mul : |2 * setup.state.helicity| = 2 * |setup.state.helicity| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h_abs_mul] at h_weight_bound
  linarith

/-- Under the stress-tensor branch, spin is bounded by `1`. -/
theorem stress_branch_spin_bound
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H) :
    setup.state.spin ≤ (1 : ℝ) := by
  calc
    setup.state.spin = |setup.state.helicity| := setup.state.spin_eq_abs_helicity
    _ ≤ (1 : ℝ) := stress_branch_helicity_bound setup

/-- No-go form: no stress-branch setup with a nonzero rotation eigenmode can
exist for a massless state with `spin > 1`. -/
theorem no_stress_rotation_eigenmode_for_spin_gt_one
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H)
    (h_spin : setup.state.spin > (1 : ℝ)) :
    False := by
  linarith [stress_branch_spin_bound setup]

/-- Spin-2 corollary: no stress-branch setup with a nonzero rotation eigenmode
exists for a massless spin-2 particle in the Weinberg-Witten frame. -/
theorem spin_two_no_stress_rotation_eigenmode
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H)
    (h_spin_two : setup.state.spin = 2) :
    False :=
  no_stress_rotation_eigenmode_for_spin_gt_one setup (by linarith)

/-- Final Weinberg-Witten stress-branch contradiction.

If a local stress tensor has a forward limit compatible with momentum
normalization and the chosen tensor mode varies continuously along some
off-forward sequence `p'_n → p`, then a massless particle with `spin > 1`
cannot realize that data. -/
theorem no_local_stress_tensor_for_spin_gt_one
    {H : Type _} [QuantumStateSpace H]
    (bridge : StressForwardLimitBridge H)
    (h_spin : bridge.targetState.spin > (1 : ℝ)) :
    False := by
  rcases bridge.exists_nonzero_offForwardMode with ⟨n, hn⟩
  let setup := bridge.branchSetupAt n hn
  have h_setup_spin : setup.state.spin > (1 : ℝ) := by
    dsimp [setup, StressForwardLimitBridge.branchSetupAt]
    simpa [bridge.incomingState_eq n] using h_spin
  exact no_stress_rotation_eigenmode_for_spin_gt_one setup h_setup_spin

/-- Spin-2 corollary for the full stress-tensor branch including the
forward-limit bridge. -/
theorem spin_two_no_local_stress_tensor
    {H : Type _} [QuantumStateSpace H]
    (bridge : StressForwardLimitBridge H)
    (h_spin_two : bridge.targetState.spin = 2) :
    False :=
  no_local_stress_tensor_for_spin_gt_one bridge (by linarith)

end PhysicsLogic.Paper.WeinbergWitten
