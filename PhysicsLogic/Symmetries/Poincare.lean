import PhysicsLogic.Symmetries.Lorentz
import PhysicsLogic.SpaceTime.Basic

namespace PhysicsLogic.Symmetries

open SpaceTime

/-- Poincaré transformation: (Λ, a) with x ↦ Λx + a -/
structure PoincareTransform where
  lorentz : LorentzTransform
  translation : Fin 4 → ℝ

/-- Apply Poincaré transformation to spacetime point -/
noncomputable def PoincareTransform.apply (P : PoincareTransform) (x : SpaceTimePoint) : SpaceTimePoint :=
  fun μ => (P.lorentz.apply x) μ + P.translation μ

/-- Apply Poincaré transformation to a set -/
noncomputable def poincareImage (g : PoincareTransform) (O : Set SpaceTimePoint) : Set SpaceTimePoint :=
  {x | ∃ y ∈ O, x = g.apply y}

/-- Poincaré composition -/
noncomputable def poincareCompose
    (P₁ P₂ : PoincareTransform) : PoincareTransform where
  lorentz := lorentzCompose P₁.lorentz P₂.lorentz
  translation := fun μ => P₁.translation μ + (P₁.lorentz.apply (fun ν => P₂.translation ν)) μ

/-- Poincaré identity -/
noncomputable def poincareIdentity : PoincareTransform where
  lorentz := LorentzTransform.id
  translation := fun _ => 0

/-- Poincaré inverse -/
noncomputable def poincareInverse
    (h_lorentz_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ))
    (P : PoincareTransform) : PoincareTransform where
  lorentz := lorentzInverse P.lorentz (h_lorentz_inv P.lorentz)
  translation := fun μ => -((lorentzInverse P.lorentz (h_lorentz_inv P.lorentz)).apply P.translation) μ

noncomputable def poincareMul :
    PoincareTransform → PoincareTransform → PoincareTransform :=
  fun P₁ P₂ => poincareCompose P₁ P₂

noncomputable def poincareInv
    (h_lorentz_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ)) :
    PoincareTransform → PoincareTransform :=
  fun P => poincareInverse h_lorentz_inv P

/-- Poincaré group structure -/
noncomputable def poincareGroup
    (h_lorentz_inv : ∀ Λ,
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzInversePreservesMetric
        (LorentzInversePreservesMetric Λ))
    (h_mul_assoc :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.poincareGroupMulAssoc
        (∀ a b c : PoincareTransform,
          poincareMul (poincareMul a b) c =
            poincareMul a (poincareMul b c)))
    (h_one_mul :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.poincareGroupOneMul
        (∀ a : PoincareTransform, poincareMul poincareIdentity a = a))
    (h_mul_one :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.poincareGroupMulOne
        (∀ a : PoincareTransform, poincareMul a poincareIdentity = a))
    (h_inv_mul_cancel :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.poincareGroupInvMulCancel
        (∀ a : PoincareTransform, poincareMul (poincareInv h_lorentz_inv a) a = poincareIdentity)) :
    Group PoincareTransform where
  mul := poincareMul
  one := poincareIdentity
  inv := poincareInv h_lorentz_inv
  mul_assoc := h_mul_assoc
  one_mul := h_one_mul
  mul_one := h_mul_one
  inv_mul_cancel := h_inv_mul_cancel

end PhysicsLogic.Symmetries
