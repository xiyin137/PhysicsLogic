import PhysicsLogic.ClassicalFieldTheory.Scalar
import PhysicsLogic.ClassicalFieldTheory.YangMills

namespace PhysicsLogic.ClassicalFieldTheory

/-- Structure for soliton solutions in field theory -/
structure SolitonTheory (F : Type*) (actionTheory : ActionTheory F)
    (eom : EquationsOfMotion F actionTheory)
    (scalarOps : ScalarFieldOperators)
    (emt : EnergyMomentumTheory F actionTheory eom scalarOps) where
  /-- Topological charge for solitons -/
  solitonCharge : ClassicalField F → ℤ
  /-- Soliton stability from topology -/
  soliton_stable : ∀ (phi : ClassicalField F) (_h : solitonCharge phi ≠ 0),
    ∃ (E_min : ℝ), ∀ (psi : ClassicalField F),
      solitonCharge psi = solitonCharge phi → emt.totalEnergy psi ≥ E_min

/-- Structure for scalar solitons -/
structure ScalarSolitons where
  /-- Kink solution (φ⁴ in 1+1D) -/
  kinkSolution : ScalarField
  /-- Domain wall -/
  domainWall : ScalarField
  /-- Cosmic string -/
  cosmicString : ScalarField

/-- Structure for gauge solitons -/
structure GaugeSolitons (ymt : YangMillsTheory) where
  /-- Vortex solution (Abrikosov-Nielsen-Olesen) -/
  vortexSolution : ComplexScalarField × EMPotential
  /-- Monopole solution ('t Hooft-Polyakov) -/
  magneticMonopole : ymt.YMField
  /-- Skyrmion -/
  skyrmion : VectorField

end PhysicsLogic.ClassicalFieldTheory
