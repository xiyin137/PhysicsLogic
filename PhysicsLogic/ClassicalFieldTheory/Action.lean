import PhysicsLogic.ClassicalFieldTheory.Fields
import PhysicsLogic.Units

namespace PhysicsLogic.ClassicalFieldTheory

/-- Structure for action principle and Hamiltonian formulation -/
structure ActionTheory (F : Type*) where
  /-- Action functional S[φ] = ∫ L d⁴x -/
  Action : ClassicalField F → ActionScale
  /-- Lagrangian density L(φ, ∂φ) -/
  lagrangianDensity : ClassicalField F → SpaceTimePoint → DensityScale
  /-- Hamiltonian density H(φ, π) -/
  hamiltonianDensity : ClassicalField F → SpaceTimePoint → DensityScale
  /-- Canonical momentum π = ∂L/∂(∂_t φ) -/
  canonicalMomentum : ClassicalField F → ClassicalField F
  /-- Legendre transform: H = πφ̇ - L -/
  legendreTransform : ClassicalField F → Prop

/-- Poisson bracket structure on a space of observables over field configurations. -/
structure PoissonStructure (F : Type*) where
  /-- Type of classical observables on the field-configuration space. -/
  Observable : Type*
  /-- Evaluation of an observable on a field configuration. -/
  eval : Observable → ClassicalField F → ScalingDimension
  /-- Poisson bracket maps two observables to an observable. -/
  poissonBracket : Observable → Observable → Observable

end PhysicsLogic.ClassicalFieldTheory
