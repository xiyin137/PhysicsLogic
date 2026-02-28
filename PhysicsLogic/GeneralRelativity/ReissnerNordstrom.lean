import PhysicsLogic.GeneralRelativity.Singularities
import PhysicsLogic.ClassicalFieldTheory.Fields
import PhysicsLogic.Assumptions

namespace PhysicsLogic.GeneralRelativity

open SpaceTime ClassicalFieldTheory

/-- Reissner-Nordström metric (charged, non-rotating):

    ds² = -(1 - 2GM/rc² + GQ²/r²c⁴)c²dt² + (1 - 2GM/rc² + GQ²/r²c⁴)⁻¹dr² + r²dΩ²
-/
noncomputable def reissnerNordstromMetricTensor
    (consts : GRConstants) (M Q : ℝ)
    (x : SpaceTimePoint) (mu nu : Fin 4) : ℝ :=
  let r := Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2)
  let delta := 1 - 2 * consts.G * M / (r * consts.c^2) + consts.G * Q^2 / (r^2 * consts.c^4)
  match mu, nu with
  | 0, 0 => -delta * consts.c^2
  | 1, 1 => 1 / delta
  | 2, 2 => r^2
  | 3, 3 => r^2 * (Real.sin (x 2))^2
  | _, _ => 0

noncomputable def reissnerNordstromInverseMetricTensor
    (consts : GRConstants) (M Q : ℝ)
    (x : SpaceTimePoint) (mu nu : Fin 4) : ℝ :=
  let r := Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2)
  let delta := 1 - 2 * consts.G * M / (r * consts.c^2) + consts.G * Q^2 / (r^2 * consts.c^4)
  match mu, nu with
  | 0, 0 => -(1 / delta) / consts.c^2
  | 1, 1 => delta
  | 2, 2 => 1 / r^2
  | 3, 3 => 1 / (r^2 * (Real.sin (x 2))^2)
  | _, _ => 0

noncomputable def reissnerNordstromMetricDeterminant
    (consts : GRConstants) (x : SpaceTimePoint) : ℝ :=
  -consts.c^2 * (Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2))^4 * (Real.sin (x 2))^2

/-- Well-formedness package for the abstract RN metric data. -/
def ReissnerNordstromMetricWellFormed (consts : GRConstants) (M Q : ℝ) : Prop :=
  (∀ x mu nu,
      reissnerNordstromMetricTensor consts M Q x mu nu =
        reissnerNordstromMetricTensor consts M Q x nu mu) ∧
  (∀ x, reissnerNordstromMetricDeterminant consts x ≠ 0) ∧
  (∀ x mu nu,
      ∑ rho,
        reissnerNordstromInverseMetricTensor consts M Q x mu rho *
          reissnerNordstromMetricTensor consts M Q x rho nu = if mu = nu then 1 else 0)

noncomputable def reissnerNordstromMetric (consts : GRConstants) (M Q : ℝ)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.reissnerNordstromMetricWellFormed
        (ReissnerNordstromMetricWellFormed consts M Q)) : SpacetimeMetric := by
  rcases h_phys with ⟨h_symm, h_nondeg, h_inv⟩
  refine
    { g := reissnerNordstromMetricTensor consts M Q
      symmetric := ?_
      inverseMetric := reissnerNordstromInverseMetricTensor consts M Q
      metricDeterminant := reissnerNordstromMetricDeterminant consts
      metric_nondegenerate := ?_
      inverse_metric_identity := ?_
      signature := fun _ mu => if mu = 0 then -1 else 1 }
  · exact h_symm
  · exact h_nondeg
  · exact h_inv

/-- Inner (Cauchy) horizon -/
noncomputable def rnInnerHorizon (consts : GRConstants) (M Q : ℝ) : ℝ :=
  consts.G * M / consts.c^2 - Real.sqrt ((consts.G * M / consts.c^2)^2 - consts.G * Q^2 / consts.c^4)

/-- Outer (event) horizon -/
noncomputable def rnOuterHorizon (consts : GRConstants) (M Q : ℝ) : ℝ :=
  consts.G * M / consts.c^2 + Real.sqrt ((consts.G * M / consts.c^2)^2 - consts.G * Q^2 / consts.c^4)

/-- Structure for Reissner-Nordström black hole theory -/
structure RNTheory (consts : GRConstants) (M Q : ℝ) where
  /-- Assumed well-formedness of the RN metric package. -/
  metric_well_formed :
    PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.reissnerNordstromMetricWellFormed
      (ReissnerNordstromMetricWellFormed consts M Q)
  /-- Connection theory for RN metric -/
  connection : ConnectionTheory (reissnerNordstromMetric consts M Q metric_well_formed)
  /-- Curvature theory for RN metric -/
  curvature : CurvatureTheory (reissnerNordstromMetric consts M Q metric_well_formed)
  /-- RN metric solves Einstein-Maxwell equations -/
  solves_einstein_maxwell : ∃ (T : TensorField 4 4),
    satisfiesEFE consts curvature T
  /-- RN reduces to Schwarzschild when Q = 0 -/
  reduces_to_schwarzschild : Q = 0 →
    ∀ (hM : M > 0)
      (h_phys :
        PhysicsLogic.PhysicsAssumption
          PhysicsLogic.AssumptionId.schwarzschildMetricWellFormed
          (SchwarzschildMetricWellFormed consts M hM)),
      reissnerNordstromMetric consts M Q metric_well_formed = schwarzschildMetric consts M hM h_phys
  /-- Electric field of charged black hole -/
  electricField : ℝ → ℝ  -- as function of radius
  /-- Electric field formula: E = Q/(4πε₀r²) -/
  electric_field_formula : ∀ (r : ℝ), r > 0 → electricField r = Q / (4 * Real.pi * r^2)

/-- Charged (Reissner-Nordström) black hole parameters -/
structure RNBlackHoleParams (consts : GRConstants) where
  mass : ℝ
  mass_pos : mass > 0
  charge : ℝ

/-- Extremal condition: Q² = (GM/c²)² (horizons coincide) -/
def IsExtremalRN (consts : GRConstants) (params : RNBlackHoleParams consts) : Prop :=
  params.charge^2 = (consts.G * params.mass / consts.c^2)^2

/-- Structure for RN singularity and horizon analysis -/
structure RNSingularityTheory (consts : GRConstants) (M Q : ℝ) (rn : RNTheory consts M Q) where
  /-- Naked singularity if Q² > (GM/c²)² (violates weak cosmic censorship?) -/
  naked_singularity_if_overcharged :
    Q^2 > (consts.G * M / consts.c^2)^2 →
    ∃ x, CurvatureSingularity rn.curvature x
  /-- Cauchy horizon is unstable (mass inflation):
      The curvature becomes unbounded near the inner horizon for
      sub-extremal black holes. This is a consequence of blue-shift
      instability: perturbations are infinitely amplified at the Cauchy horizon. -/
  cauchy_horizon_instability :
    Q^2 < (consts.G * M / consts.c^2)^2 →
    ∃ x, CurvatureSingularity rn.curvature x

end PhysicsLogic.GeneralRelativity
