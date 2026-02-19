import PhysicsLogic.FluidMechanics.Basic
import PhysicsLogic.FluidMechanics.Conservation

namespace PhysicsLogic.FluidMechanics

set_option autoImplicit false

/- ============= VORTICITY DYNAMICS ============= -/

variable (ops : DifferentialOperators)
variable (md : MaterialDerivative ops)

/-- Vorticity transport for incompressible flow: Dω/Dt = ω·∇v + ν∇²ω -/
def vorticityTransportEquation
  (v : VelocityField)
  (ν : ℝ) : Prop :=
  isIncompressible ops v ∧
  let ω := vorticity ops v
  ∀ x t i, md.materialDerivativeVector v ω x t i =
           (∑ j : Fin 3, ω x t j * ops.gradient (fun y s => v y s i) x t j) +
           ν * ops.vectorLaplacian ω x t i

/-- Structure for vorticity dynamics theorems -/
structure VorticityTheory (ops : DifferentialOperators) (md : MaterialDerivative ops) where
  /-- In 2D, vorticity stretching term vanishes -/
  vorticity_2d_no_stretching : ∀ (v : VelocityField),
    (∀ x t, v x t 2 = 0) →
    (∀ x t j, vorticity ops v x t j * ops.gradient (fun y s => v y s 0) x t j +
              vorticity ops v x t j * ops.gradient (fun y s => v y s 1) x t j = 0)
  /-- Helmholtz first theorem: for inviscid incompressible flow, the
      vorticity is frozen into the fluid. Formally, if ω satisfies
      the vorticity transport equation with ν = 0, then Dω/Dt = ω·∇v,
      i.e., vorticity is advected and stretched by the flow. -/
  helmholtz_first_theorem : ∀ (v : VelocityField) (ω : VectorField3D),
    ω = vorticity ops v →
    isIncompressible ops v →
    ∀ x t i, md.materialDerivativeVector v ω x t i =
      ∑ j : Fin 3, ω x t j * ops.gradient (fun y s => v y s i) x t j

end PhysicsLogic.FluidMechanics
