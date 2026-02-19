import PhysicsLogic.ClassicalFieldTheory.Action
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace PhysicsLogic.ClassicalFieldTheory

/-- Structure for Euler-Lagrange equations and Hamilton's equations -/
structure EquationsOfMotion (F : Type*) (actionTheory : ActionTheory F) where
  /-- Euler-Lagrange equations: ∂L/∂φ - ∂_μ(∂L/∂(∂_μφ)) = 0 -/
  eulerLagrange : ClassicalField F → Prop
  /-- Hamilton's equations: φ̇ = δH/δπ, π̇ = -δH/δφ -/
  hamiltonEquations : ClassicalField F → Prop
  /-- Field satisfies EL equations iff the action is stationary under all variations.
      For any one-parameter family of fields φ(ε) with φ(0) = φ,
      the derivative d/dε S[φ(ε)]|_{ε=0} = 0. -/
  euler_lagrange_stationary : ∀ (phi : ClassicalField F)
    (variation : ℝ → ClassicalField F),
    variation 0 = phi →
    (eulerLagrange phi ↔ deriv (fun ε => actionTheory.Action (variation ε)) 0 = 0)
  /-- Equivalence of Lagrangian and Hamiltonian formulations -/
  lagrangian_hamiltonian_equivalence : ∀ (phi : ClassicalField F),
    eulerLagrange phi ↔ hamiltonEquations phi

end PhysicsLogic.ClassicalFieldTheory
