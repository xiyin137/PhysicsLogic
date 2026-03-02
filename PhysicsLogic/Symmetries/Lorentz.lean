import Mathlib.GroupTheory.GroupAction.Defs
import PhysicsLogic.SpaceTime.Minkowski
import PhysicsLogic.SpaceTime.Causality
import PhysicsLogic.Assumptions

namespace PhysicsLogic.Symmetries

open SpaceTime

/-- Target proposition for composition preserving the Minkowski metric. -/
def LorentzComposePreservesMetric (Λ₁ Λ₂ : LorentzTransform) : Prop :=
  ∀ x y : SpaceTimePoint,
    minkowskiInnerProduct x y = minkowskiInnerProduct
      (fun μ => ∑ ν, (∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν) * x ν)
      (fun μ => ∑ ν, (∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν) * y ν)

/-- Composition of metric-preserving Lorentz transforms is metric-preserving. -/
theorem lorentz_compose_preserves_metric
    (Λ₁ Λ₂ : LorentzTransform) :
    LorentzComposePreservesMetric Λ₁ Λ₂ := by
  intro x y
  let x' : SpaceTimePoint := fun κ => ∑ ν, Λ₂.matrix κ ν * x ν
  let y' : SpaceTimePoint := fun κ => ∑ ν, Λ₂.matrix κ ν * y ν
  have h₂ : minkowskiInnerProduct x y = minkowskiInnerProduct x' y' := by
    simpa [x', y'] using Λ₂.preserves_metric x y
  have h₁ :
      minkowskiInnerProduct x' y' =
      minkowskiInnerProduct
        (fun μ => ∑ κ, Λ₁.matrix μ κ * x' κ)
        (fun μ => ∑ κ, Λ₁.matrix μ κ * y' κ) := by
    simpa [x', y'] using Λ₁.preserves_metric x' y'
  have hx :
      (fun μ => ∑ κ, Λ₁.matrix μ κ * x' κ) =
      (fun μ => ∑ ν, (∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν) * x ν) := by
    ext μ
    unfold x'
    calc
      ∑ κ, Λ₁.matrix μ κ * (∑ ν, Λ₂.matrix κ ν * x ν)
          = ∑ κ, ∑ ν, Λ₁.matrix μ κ * (Λ₂.matrix κ ν * x ν) := by
              simp [Finset.mul_sum]
      _ = ∑ κ, ∑ ν, x ν * (Λ₁.matrix μ κ * Λ₂.matrix κ ν) := by
            simp [mul_left_comm, mul_comm]
      _ = ∑ ν, ∑ κ, x ν * (Λ₁.matrix μ κ * Λ₂.matrix κ ν) := by
            rw [Finset.sum_comm]
      _ = ∑ ν, (∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν) * x ν := by
            simp [mul_comm, Finset.mul_sum]
  have hy :
      (fun μ => ∑ κ, Λ₁.matrix μ κ * y' κ) =
      (fun μ => ∑ ν, (∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν) * y ν) := by
    ext μ
    unfold y'
    calc
      ∑ κ, Λ₁.matrix μ κ * (∑ ν, Λ₂.matrix κ ν * y ν)
          = ∑ κ, ∑ ν, Λ₁.matrix μ κ * (Λ₂.matrix κ ν * y ν) := by
              simp [Finset.mul_sum]
      _ = ∑ κ, ∑ ν, y ν * (Λ₁.matrix μ κ * Λ₂.matrix κ ν) := by
            simp [mul_left_comm, mul_comm]
      _ = ∑ ν, ∑ κ, y ν * (Λ₁.matrix μ κ * Λ₂.matrix κ ν) := by
            rw [Finset.sum_comm]
      _ = ∑ ν, (∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν) * y ν := by
            simp [mul_comm, Finset.mul_sum]
  exact h₂.trans (h₁.trans (by simp [hx, hy]))

/-- Target proposition for inverse preserving the Minkowski metric. -/
def LorentzInversePreservesMetric (Λ : LorentzTransform) : Prop :=
  ∀ x y : SpaceTimePoint,
    minkowskiInnerProduct x y = minkowskiInnerProduct
      (fun μ =>
        ∑ ν,
          (let s_μ : ℝ := if μ = (0 : Fin 4) then -1 else 1
           let s_ν : ℝ := if ν = (0 : Fin 4) then -1 else 1
           s_μ * Λ.matrix ν μ * s_ν) * x ν)
      (fun μ =>
        ∑ ν,
          (let s_μ : ℝ := if μ = (0 : Fin 4) then -1 else 1
           let s_ν : ℝ := if ν = (0 : Fin 4) then -1 else 1
           s_μ * Λ.matrix ν μ * s_ν) * y ν)

/-- Lorentz composition -/
noncomputable def lorentzCompose (Λ₁ Λ₂ : LorentzTransform) :
    LorentzTransform where
  matrix := fun μ ν => ∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν
  preserves_metric := by
    exact lorentz_compose_preserves_metric Λ₁ Λ₂

/-- Lorentz inverse: Λ⁻¹ = η Λᵀ η

    For a Lorentz transformation satisfying Λᵀ η Λ = η, the inverse is:
    (Λ⁻¹)^μ_ν = η^{μμ} Λ^ν_μ η_{νν} = sign(μ) · Λ^ν_μ · sign(ν) -/
noncomputable def lorentzInverse (Λ : LorentzTransform)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ)) :
    LorentzTransform where
  matrix := fun μ ν =>
    let s_μ : ℝ := if μ = (0 : Fin 4) then -1 else 1
    let s_ν : ℝ := if ν = (0 : Fin 4) then -1 else 1
    s_μ * Λ.matrix ν μ * s_ν
  preserves_metric := by
    exact h_phys

noncomputable def lorentzMul :
    LorentzTransform → LorentzTransform → LorentzTransform :=
  fun Λ₁ Λ₂ => lorentzCompose Λ₁ Λ₂

noncomputable def lorentzInv
    (h_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ)) :
    LorentzTransform → LorentzTransform :=
  fun Λ => lorentzInverse Λ (h_inv Λ)

/-- Lorentz group structure -/
noncomputable def lorentzGroup
    (h_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ))
    (h_mul_assoc :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupMulAssoc
        (∀ a b c : LorentzTransform,
          lorentzMul (lorentzMul a b) c =
            lorentzMul a (lorentzMul b c)))
    (h_one_mul :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupOneMul
        (∀ a : LorentzTransform, lorentzMul LorentzTransform.id a = a))
    (h_mul_one :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupMulOne
        (∀ a : LorentzTransform, lorentzMul a LorentzTransform.id = a))
    (h_inv_mul_cancel :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupInvMulCancel
        (∀ a : LorentzTransform, lorentzMul (lorentzInv h_inv a) a = LorentzTransform.id)) :
    Group LorentzTransform where
  mul := lorentzMul
  one := LorentzTransform.id
  inv := lorentzInv h_inv
  mul_assoc := h_mul_assoc
  one_mul := h_one_mul
  mul_one := h_mul_one
  inv_mul_cancel := h_inv_mul_cancel

/-- Lorentz transformation preserves causal structure -/
theorem lorentz_preserves_timelike (Λ : LorentzTransform) (x y : SpaceTimePoint) :
    Timelike minkowskiMetric x y → Timelike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  exact SpaceTime.lorentz_preserves_timelike Λ x y

theorem lorentz_preserves_spacelike (Λ : LorentzTransform) (x y : SpaceTimePoint) :
    Spacelike minkowskiMetric x y → Spacelike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  exact SpaceTime.lorentz_preserves_spacelike Λ x y

theorem lorentz_preserves_lightlike (Λ : LorentzTransform) (x y : SpaceTimePoint) :
    Lightlike minkowskiMetric x y → Lightlike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  exact SpaceTime.lorentz_preserves_lightlike Λ x y

end PhysicsLogic.Symmetries
