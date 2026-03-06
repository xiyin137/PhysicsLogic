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
import Mathlib.Tactic.Linarith

/-!
# Weinberg-Witten theorem

This module formalizes the logical core of the Weinberg-Witten no-go theorem
(Weinberg & Witten, Phys. Lett. B 96 (1980) 59).

## Theorem statements

1. **Current branch**: A massless one-particle state carrying nonzero charge
   of a Lorentz-covariant conserved 4-current must have helicity `|h| ≤ 1/2`.
2. **Stress branch**: A massless one-particle state with nonzero matrix elements
   of a Lorentz-covariant conserved stress tensor must have helicity `|h| ≤ 1`.

## Formalization strategy

The current branch still packages the hard QFT step as an explicit no-go
proposition, accessed through `PhysicsAssumption`.

The stress branch is split into two pieces.

1. The algebraic rotation argument from the stringbook prologue is proved in
   Lean: in a frame with `\vec p' = -\vec p`, the matrix element
   `⟨p', h| T_{μν}(0) |p, h⟩` picks up the helicity phase `e^{2 i h θ}` from
   the states, while tensor covariance only allows rotation weights
   `0, ±1, ±2`. This yields `|h| ≤ 1`.
2. The final analytic bridge from the forward-limit normalization
   `⟨p', h|T_{μν}(0)|p, h⟩ → p_μ p_ν / ((2π)^3 p^0)` to a nonzero off-forward
   matrix element is not formalized here yet. This file stops at the algebraic
   rotation-weight obstruction.

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
`\vec p' = -\vec p`. The two fields `helicity_rotation_phase` and
`tensor_component_has_weight` are the two sides of the book's covariance
equation:

`R_μ{}^ρ(θ) R_ν{}^σ(θ) ⟨p', h| T_{ρσ}(0) |p, h⟩ = e^{2 i h θ} ⟨p', h| T_{μν}(0) |p, h⟩`.

The local-QFT ingredients (`stressTensor`, translation symmetry, conservation)
remain visible in the interface even though the rotation proof of `|h| ≤ 1`
only uses the phase-matching data. Opaque placeholder claims have been replaced
by explicit momentum relations and explicit formulas tying matrix elements to
the stored operator-valued distributions. -/
structure StressBranchSetup (H : Type _) [QuantumStateSpace H] where
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
  /-- `|p', h⟩` carries the same helicity label as `|p, h⟩`. -/
  statePrime_same_helicity : statePrime.helicity = state.helicity
  /-- In the chosen Lorentz frame, the momenta are back-to-back. -/
  backToBackFrame : BackToBackSpatialMomenta state.momentum statePrime.momentum
  /-- Operator-valued stress tensor `T^{μν}(x)`. -/
  stressTensor : RankTwoTensorDistribution H
  /-- Off-forward matrix element `⟨p', h|T^{μν}(0)|p, h⟩`. -/
  stressMatrixElement : StressMatrixElementFunctional H
  /-- Rotated off-forward matrix element in the special frame. -/
  rotatedStressMatrixElement : Fin 4 → Fin 4 → ℝ → ComplexAmplitude
  /-- Concrete formula relating the matrix element to the stored stress tensor. -/
  matrixElementFromTensor :
    StressTensorMatrixElementFromField H stressTensor stressMatrixElement statePrime.ket state.ket
  /-- Concrete off-forward conservation law for the matrix element. -/
  conservedMatrixElement :
    ConservedStressMatrixElement
      H stressMatrixElement statePrime.momentum state.momentum statePrime.ket state.ket
  /-- Rotation around the momentum axis acts on the states with total phase `e^{2 i h θ}`. -/
  helicity_rotation_phase :
    ∀ μ ν θ,
      rotatedStressMatrixElement μ ν θ =
        rotationPhase (2 * state.helicity) θ *
          stressMatrixElement μ ν statePrime.ket state.ket
  /-- Any nonzero tensor component has one of the five allowed tensor weights. -/
  tensor_component_has_weight :
    ∀ {μ ν},
      stressMatrixElement μ ν statePrime.ket state.ket ≠ 0 →
        ∃ w : TensorRotationWeight,
          ∀ θ,
            rotatedStressMatrixElement μ ν θ =
              rotationPhase w.toReal θ *
                stressMatrixElement μ ν statePrime.ket state.ket

/-- The chosen off-forward stress-tensor matrix element is nonzero. -/
def HasNonzeroStressMatrixElement
    {H : Type _} [QuantumStateSpace H] (setup : StressBranchSetup H) : Prop :=
  ∃ μ ν, setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket ≠ 0

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

/-- A nonzero off-forward stress-tensor matrix element forces `2 h` to be one
of the allowed tensor weights `-2, -1, 0, 1, 2`. -/
theorem stress_branch_double_helicity_weight
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H)
    (h_stress : HasNonzeroStressMatrixElement setup) :
    ∃ w : TensorRotationWeight, 2 * setup.state.helicity = w.toReal := by
  rcases h_stress with ⟨μ, ν, h_nonzero⟩
  rcases setup.tensor_component_has_weight h_nonzero with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  apply equal_weights_of_nonzero_rotation_component h_nonzero
  intro θ
  calc
    rotationPhase (2 * setup.state.helicity) θ *
        setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket
      = setup.rotatedStressMatrixElement μ ν θ := by
          symm
          exact setup.helicity_rotation_phase μ ν θ
    _ = rotationPhase w.toReal θ *
        setup.stressMatrixElement μ ν setup.statePrime.ket setup.state.ket :=
      hw θ

/-- Under the stringbook rotation argument, helicity is bounded by `1`. -/
theorem stress_branch_helicity_bound
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H)
    (h_stress : HasNonzeroStressMatrixElement setup) :
    |setup.state.helicity| ≤ (1 : ℝ) := by
  rcases stress_branch_double_helicity_weight setup h_stress with ⟨w, hw⟩
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
    (setup : StressBranchSetup H)
    (h_stress : HasNonzeroStressMatrixElement setup) :
    setup.state.spin ≤ (1 : ℝ) := by
  calc
    setup.state.spin = |setup.state.helicity| := setup.state.spin_eq_abs_helicity
    _ ≤ (1 : ℝ) := stress_branch_helicity_bound setup h_stress

/-- No-go form: a massless state with `spin > 1` cannot have nonzero
off-forward stress-tensor matrix elements in the Weinberg-Witten frame. -/
theorem no_stress_matrix_element_for_spin_gt_one
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H)
    (h_spin : setup.state.spin > (1 : ℝ)) :
    ¬ HasNonzeroStressMatrixElement setup := by
  intro h_stress
  linarith [stress_branch_spin_bound setup h_stress]

/-- Spin-2 corollary: a massless spin-2 particle (graviton) cannot have
nonzero off-forward matrix elements of a Lorentz-covariant conserved stress
tensor in the Weinberg-Witten rotation frame. -/
theorem spin_two_no_stress_matrix_element
    {H : Type _} [QuantumStateSpace H]
    (setup : StressBranchSetup H)
    (h_spin_two : setup.state.spin = 2) :
    ¬ HasNonzeroStressMatrixElement setup :=
  no_stress_matrix_element_for_spin_gt_one setup (by linarith)

end PhysicsLogic.Paper.WeinbergWitten
