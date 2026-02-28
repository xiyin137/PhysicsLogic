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
noncomputable def lorentzCompose (Λ₁ Λ₂ : LorentzTransform)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzComposePreservesMetric
        (LorentzComposePreservesMetric Λ₁ Λ₂)) :
    LorentzTransform where
  matrix := fun μ ν => ∑ κ, Λ₁.matrix μ κ * Λ₂.matrix κ ν
  preserves_metric := by
    exact h_phys

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

noncomputable def lorentzMul
    (h_comp : ∀ Λ₁ Λ₂,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzComposePreservesMetric
        (LorentzComposePreservesMetric Λ₁ Λ₂)) :
    LorentzTransform → LorentzTransform → LorentzTransform :=
  fun Λ₁ Λ₂ => lorentzCompose Λ₁ Λ₂ (h_comp Λ₁ Λ₂)

noncomputable def lorentzInv
    (h_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ)) :
    LorentzTransform → LorentzTransform :=
  fun Λ => lorentzInverse Λ (h_inv Λ)

/-- Lorentz group structure -/
noncomputable def lorentzGroup
    (h_comp : ∀ Λ₁ Λ₂,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzComposePreservesMetric
        (LorentzComposePreservesMetric Λ₁ Λ₂))
    (h_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ))
    (h_mul_assoc :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupMulAssoc
        (∀ a b c : LorentzTransform,
          lorentzMul h_comp (lorentzMul h_comp a b) c =
            lorentzMul h_comp a (lorentzMul h_comp b c)))
    (h_one_mul :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupOneMul
        (∀ a : LorentzTransform, lorentzMul h_comp LorentzTransform.id a = a))
    (h_mul_one :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupMulOne
        (∀ a : LorentzTransform, lorentzMul h_comp a LorentzTransform.id = a))
    (h_inv_mul_cancel :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzGroupInvMulCancel
        (∀ a : LorentzTransform, lorentzMul h_comp (lorentzInv h_inv a) a = LorentzTransform.id)) :
    Group LorentzTransform where
  mul := lorentzMul h_comp
  one := LorentzTransform.id
  inv := lorentzInv h_inv
  mul_assoc := h_mul_assoc
  one_mul := h_one_mul
  mul_one := h_mul_one
  inv_mul_cancel := h_inv_mul_cancel

/-- Lorentz transformation preserves causal structure -/
theorem lorentz_preserves_timelike (Λ : LorentzTransform) (x y : SpaceTimePoint)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzPreservesTimelike
        (Timelike minkowskiMetric x y →
          Timelike minkowskiMetric (Λ.apply x) (Λ.apply y))) :
  Timelike minkowskiMetric x y → Timelike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  exact h_phys

theorem lorentz_preserves_spacelike (Λ : LorentzTransform) (x y : SpaceTimePoint)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzPreservesSpacelike
        (Spacelike minkowskiMetric x y →
          Spacelike minkowskiMetric (Λ.apply x) (Λ.apply y))) :
  Spacelike minkowskiMetric x y → Spacelike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  exact h_phys

theorem lorentz_preserves_lightlike (Λ : LorentzTransform) (x y : SpaceTimePoint)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzPreservesLightlike
        (Lightlike minkowskiMetric x y →
          Lightlike minkowskiMetric (Λ.apply x) (Λ.apply y))) :
  Lightlike minkowskiMetric x y → Lightlike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  exact h_phys

end PhysicsLogic.Symmetries
