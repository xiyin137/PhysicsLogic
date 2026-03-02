import PhysicsLogic.Symmetries.Lorentz
import PhysicsLogic.SpaceTime.Basic

namespace PhysicsLogic.Symmetries

open SpaceTime

/-- Poincaré transformation: (Λ, a) with x ↦ Λx + a -/
structure PoincareTransform where
  lorentz : LorentzTransform
  translation : Fin 4 → ℝ

@[ext]
theorem PoincareTransform.ext {P₁ P₂ : PoincareTransform}
    (h_lorentz : P₁.lorentz = P₂.lorentz)
    (h_translation : P₁.translation = P₂.translation) :
    P₁ = P₂ := by
  cases P₁
  cases P₂
  cases h_lorentz
  cases h_translation
  rfl

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

theorem poincare_one_mul (a : PoincareTransform) :
    poincareMul poincareIdentity a = a := by
  apply PoincareTransform.ext
  · exact lorentz_one_mul a.lorentz
  · funext μ
    simp [poincareMul, poincareCompose, poincareIdentity, LorentzTransform.apply, LorentzTransform.id]

theorem poincare_mul_one (a : PoincareTransform) :
    poincareMul a poincareIdentity = a := by
  apply PoincareTransform.ext
  · exact lorentz_mul_one a.lorentz
  · funext μ
    simp [poincareMul, poincareCompose, poincareIdentity, LorentzTransform.apply, LorentzTransform.id]

theorem poincare_mul_assoc (a b c : PoincareTransform) :
    poincareMul (poincareMul a b) c = poincareMul a (poincareMul b c) := by
  apply PoincareTransform.ext
  · exact lorentz_mul_assoc a.lorentz b.lorentz c.lorentz
  · funext μ
    have h_comp_apply :
        (lorentzCompose a.lorentz b.lorentz).apply c.translation μ =
          a.lorentz.apply (b.lorentz.apply c.translation) μ := by
      change
        ∑ ν, (∑ κ, a.lorentz.matrix μ κ * b.lorentz.matrix κ ν) * c.translation ν =
          ∑ κ, a.lorentz.matrix μ κ * (∑ ν, b.lorentz.matrix κ ν * c.translation ν)
      calc
        ∑ ν, (∑ κ, a.lorentz.matrix μ κ * b.lorentz.matrix κ ν) * c.translation ν
            = ∑ ν, ∑ κ, (a.lorentz.matrix μ κ * b.lorentz.matrix κ ν) * c.translation ν := by
                simp [Finset.sum_mul]
        _ = ∑ ν, ∑ κ, a.lorentz.matrix μ κ * (b.lorentz.matrix κ ν * c.translation ν) := by
              simp [mul_assoc]
        _ = ∑ κ, ∑ ν, a.lorentz.matrix μ κ * (b.lorentz.matrix κ ν * c.translation ν) := by
              rw [Finset.sum_comm]
        _ = ∑ κ, a.lorentz.matrix μ κ * (∑ ν, b.lorentz.matrix κ ν * c.translation ν) := by
              simp [Finset.mul_sum]
    have h_apply_add :
        a.lorentz.apply (fun ν => b.translation ν + (b.lorentz.apply c.translation) ν) μ =
          a.lorentz.apply b.translation μ + a.lorentz.apply (b.lorentz.apply c.translation) μ := by
      simp [LorentzTransform.apply, Finset.sum_add_distrib, mul_add]
    calc
      ((a.translation μ + a.lorentz.apply b.translation μ) +
          (lorentzCompose a.lorentz b.lorentz).apply c.translation μ)
          =
          a.translation μ +
            (a.lorentz.apply b.translation μ +
              (lorentzCompose a.lorentz b.lorentz).apply c.translation μ) := by
            ac_rfl
      _ = a.translation μ +
            (a.lorentz.apply b.translation μ +
              a.lorentz.apply (b.lorentz.apply c.translation) μ) := by
            simp [h_comp_apply]
      _ = a.translation μ +
            a.lorentz.apply (fun ν => b.translation ν + (b.lorentz.apply c.translation) ν) μ := by
            simp [h_apply_add]
      _ = (poincareCompose a (poincareCompose b c)).translation μ := by
            rfl

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
    (h_inv_mul_cancel :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.poincareGroupInvMulCancel
        (∀ a : PoincareTransform, poincareMul (poincareInv h_lorentz_inv a) a = poincareIdentity)) :
    Group PoincareTransform where
  mul := poincareMul
  one := poincareIdentity
  inv := poincareInv h_lorentz_inv
  mul_assoc := poincare_mul_assoc
  one_mul := poincare_one_mul
  mul_one := poincare_mul_one
  inv_mul_cancel := h_inv_mul_cancel

end PhysicsLogic.Symmetries
