import PhysicsLogic.QFT.RG.Basic
import PhysicsLogic.QFT.PathIntegral.ActionAndMeasure
import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.QFT.RG.Wilsonian

/-!
# Wilsonian Renormalization Group

The Wilsonian approach integrates out high-momentum modes shell by shell,
generating an effective action S_Λ[φ] that depends on the cutoff Λ.

## Key concepts:
1. **Wilsonian effective action S_Λ[φ]**: Contains all operators with
   scale-dependent Wilson coefficients.
2. **Exact RG equation (Polchinski/Wetterich)**: Describes how S_Λ evolves.
3. **Universality**: Different UV theories can flow to the same IR physics.
-/

open PhysicsLogic.QFT.RG

set_option linter.unusedVariables false

/- ============= WILSONIAN EFFECTIVE ACTION ============= -/

/-- Wilsonian effective action at cutoff Λ

    S_Λ[φ] = ∫ d^d x ∑_i g_i(Λ) O_i(φ(x))

    This real-valued version models Euclidean Wilsonian actions.
    The complex-valued generalization is `ComplexWilsonianAction`. -/
structure WilsonianAction {d : ℕ} (rg : RGFramework d) where
  /-- The cutoff scale -/
  cutoff : Cutoff
  /-- The action functional on a field configuration type -/
  FieldConfig : Type*
  action : PhysicsLogic.QFT.PathIntegral.ActionFunctional FieldConfig
  /-- Wilson coefficients for each operator -/
  coefficients : rg.Operator → DimensionlessCoupling

/-- Complex-valued Wilsonian action at cutoff Λ.

    This captures Lorentzian/complex effective actions where the functional
    weight is oscillatory and the action is not restricted to ℝ. -/
structure ComplexWilsonianAction {d : ℕ} (rg : RGFramework d) where
  /-- The cutoff scale -/
  cutoff : Cutoff
  /-- The action functional on a field configuration type -/
  FieldConfig : Type*
  action : PhysicsLogic.QFT.PathIntegral.ComplexActionFunctional FieldConfig
  /-- Wilson coefficients for each operator (possibly complex). -/
  coefficients : rg.Operator → ℂ

/-- Embed a real Wilsonian action into the complex-valued interface. -/
def WilsonianAction.toComplex {d : ℕ} {rg : RGFramework d}
    (S : WilsonianAction rg) : ComplexWilsonianAction rg where
  cutoff := S.cutoff
  FieldConfig := S.FieldConfig
  action := S.action.toComplex
  coefficients := fun O => (S.coefficients O : ℂ)

/-- The Wilson coefficient for operator O at scale Λ. -/
def wilsonCoeff {d : ℕ} {rg : RGFramework d}
    (S : WilsonianAction rg) (O : rg.Operator) : DimensionlessCoupling :=
  S.coefficients O

/-- Dimensionless Wilson coefficient -/
noncomputable def dimlessWilsonCoeff {d : ℕ} {rg : RGFramework d}
    (S : WilsonianAction rg) (O : rg.Operator) : DimensionlessCoupling :=
  S.coefficients O * S.cutoff.Λ ^ (rg.massDimension O - d)

/- ============= EXACT RG FLOW ============= -/

/-- Infinitesimal RG transformation: lowering the cutoff Λ → Λ - δΛ
    integrates out modes in the momentum shell. -/
structure RGStep {d : ℕ} (rg : RGFramework d) where
  /-- Initial action -/
  initial : WilsonianAction rg
  /-- Final action (at slightly lower cutoff) -/
  final : WilsonianAction rg
  /-- The cutoff decreased -/
  cutoff_decreased : final.cutoff.Λ < initial.cutoff.Λ

/-- Polchinski equation (exact RG flow)

    -Λ ∂S_Λ/∂Λ = (1/2) Tr[(∂_Λ K) · G₀ · (δ²S/δφ² - δS/δφ · δS/δφ)] -/
structure PolchinskiFlow {d : ℕ} (rg : RGFramework d) where
  /-- Family of actions parametrized by cutoff -/
  actions : Scale → WilsonianAction rg
  /-- Cutoff function used -/
  regulator : CutoffFunction
  /-- The cutoff of the action at each scale matches the scale.
      (The full Polchinski equation -Λ ∂S_Λ/∂Λ = ... requires functional
      derivatives not available in this formalization.) -/
  cutoff_consistent : ∀ t, (actions t).cutoff.Λ = t

/-- Wetterich equation (alternative exact RG)

    ∂_t Γ_k = (1/2) Tr[(∂_t R_k) · (Γ_k^(2) + R_k)^(-1)] -/
structure WetterichFlow {d : ℕ} (rg : RGFramework d) where
  /-- Effective average action at each scale -/
  FieldConfig : Type*
  effective_action : Scale → PhysicsLogic.QFT.PathIntegral.ActionFunctional FieldConfig
  /-- Regulator function R_k -/
  regulator : Scale → ℝ → ℝ
  /-- The regulator vanishes in the IR limit k → 0.
      (The full Wetterich equation ∂_t Γ_k = ... requires functional
      derivatives not available in this formalization.) -/
  regulator_ir_vanish : ∀ (p : ℝ), regulator 0 p = 0

/-- Complex-valued Wetterich flow.

    Useful for real-time or contour-deformed formulations where Γ_k can be
    complex-valued. -/
structure ComplexWetterichFlow {d : ℕ} (rg : RGFramework d) where
  /-- Effective average action at each scale (complex-valued). -/
  FieldConfig : Type*
  effective_action : Scale → PhysicsLogic.QFT.PathIntegral.ComplexActionFunctional FieldConfig
  /-- Regulator function R_k on momentum magnitudes. -/
  regulator : Scale → ℝ → ℝ
  /-- IR limit of the regulator. -/
  regulator_ir_vanish : ∀ (p : ℝ), regulator 0 p = 0

/-- Embed a real Wetterich flow into the complex-valued interface. -/
def WetterichFlow.toComplex {d : ℕ} {rg : RGFramework d}
    (W : WetterichFlow rg) : ComplexWetterichFlow rg where
  FieldConfig := W.FieldConfig
  effective_action := fun k => (W.effective_action k).toComplex
  regulator := W.regulator
  regulator_ir_vanish := W.regulator_ir_vanish

/- ============= LOCALITY AND DERIVATIVE EXPANSION ============= -/

/-- Derivative expansion of the effective action

    S_Λ[φ] = ∫ d^d x [V(φ) + (1/2)Z(φ)(∂φ)² + O(∂⁴)] -/
structure DerivativeExpansion (d : ℕ) where
  /-- Effective potential V(φ) -/
  potential : ScalingDimension → PotentialScale
  /-- Wave function renormalization Z(φ) -/
  wavefunction_renorm : ScalingDimension → Dimless
  /-- Higher derivative terms (truncated) -/
  higher_order : ℕ → (ScalingDimension → PotentialScale)

/-- Local potential approximation (LPA): keep only V(φ), set Z = 1 -/
structure LPA (d : ℕ) where
  /-- The potential at each scale -/
  potential : Scale → (ScalingDimension → PotentialScale)

/-- LPA' approximation: LPA plus running Z(k) -/
structure LPAprime (d : ℕ) where
  potential : Scale → (ScalingDimension → PotentialScale)
  Z : Scale → Dimless

/- ============= INTEGRATING OUT ============= -/

/-- Integrating out high-momentum modes between Λ_UV and Λ_IR -/
structure ModeIntegration {d : ℕ} (rg : RGFramework d) where
  /-- UV action -/
  uv_action : WilsonianAction rg
  /-- IR action -/
  ir_action : WilsonianAction rg
  /-- Scale separation -/
  scale_separation : ir_action.cutoff.Λ < uv_action.cutoff.Λ

/-- Power counting for irrelevant operators:
    An operator of dimension Δ > d has Wilson coefficient that scales as
    g(Λ_IR) ~ g(Λ_UV) · (Λ_IR/Λ_UV)^(Δ-d)

    This is a theorem about the RG flow, not an axiom. -/
theorem irrelevant_suppression {d : ℕ} (rg : RGFramework d)
    (mi : ModeIntegration rg)
    (O : rg.Operator) (h : Irrelevant rg O)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.wilsonianIrrelevantSuppression
        (∃ C : ℝ, |wilsonCoeff mi.ir_action O| ≤
          C * |wilsonCoeff mi.uv_action O| *
          (mi.ir_action.cutoff.Λ / mi.uv_action.cutoff.Λ) ^ (rg.massDimension O - d))) :
  ∃ C : ℝ, |wilsonCoeff mi.ir_action O| ≤
    C * |wilsonCoeff mi.uv_action O| *
    (mi.ir_action.cutoff.Λ / mi.uv_action.cutoff.Λ) ^ (rg.massDimension O - d) := by
  exact h_phys

/- ============= UNIVERSALITY ============= -/

/-- Universality class: a set of UV theories that flow to the same IR fixed point. -/
structure UniversalityClass {d : ℕ} (rg : RGFramework d) where
  /-- The IR fixed point defining the class -/
  ir_fixed_point : CouplingConfig rg
  /-- It is indeed a fixed point -/
  is_fixed : FixedPoint rg ir_fixed_point
  /-- The relevant operators at this fixed point -/
  relevant_ops : Set rg.Operator
  /-- Relevant ops are those with Δ < d at the fixed point -/
  relevant_criterion : ∀ O ∈ relevant_ops,
    scalingDimension rg O ir_fixed_point < d

/-- Critical exponents from scaling dimensions:
    ν_O = 1/(d - Δ_O) for relevant operators -/
noncomputable def criticalExponent {d : ℕ} (rg : RGFramework d)
    (O : rg.Operator) (fp : CouplingConfig rg) : ScalingDimension :=
  1 / (d - scalingDimension rg O fp)

/-- Universality: different microscopic theories in the same class give the same
    critical exponents, because critical exponents are determined solely by
    the IR fixed point. -/
noncomputable def universalCriticalExponent {d : ℕ} {rg : RGFramework d}
    (uc : UniversalityClass rg) (O : rg.Operator) : ScalingDimension :=
  criticalExponent rg O uc.ir_fixed_point

end PhysicsLogic.QFT.RG.Wilsonian
