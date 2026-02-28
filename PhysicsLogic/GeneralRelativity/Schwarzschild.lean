import PhysicsLogic.GeneralRelativity.EnergyConditions
import PhysicsLogic.SpaceTime.Symmetries
import PhysicsLogic.Assumptions

namespace PhysicsLogic.GeneralRelativity

open SpaceTime

/-- Schwarzschild radius: r_s = 2GM/c² -/
noncomputable def schwarzschildRadius (consts : GRConstants) (M : ℝ) : ℝ :=
  2 * consts.G * M / consts.c^2

/-- Schwarzschild metric in Schwarzschild coordinates (t,r,θ,φ):

    ds² = -(1-r_s/r)c²dt² + (1-r_s/r)⁻¹dr² + r²(dθ² + sin²θ dφ²)

    Describes static, spherically symmetric vacuum solution
-/
noncomputable def schwarzschildMetricTensor (consts : GRConstants) (M : ℝ) (_hM : M > 0)
    (x : SpaceTimePoint) (μ ν : Fin 4) : ℝ :=
  let r := Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2)
  let rs := schwarzschildRadius consts M
  if r > rs then
    match μ, ν with
    | 0, 0 => -(1 - rs / r) * consts.c^2
    | 1, 1 => (1 - rs / r)⁻¹
    | 2, 2 => r^2
    | 3, 3 => r^2 * (Real.sin (x 2))^2
    | _, _ => 0
  else 0

noncomputable def schwarzschildInverseMetricTensor (consts : GRConstants) (M : ℝ) (_hM : M > 0)
    (x : SpaceTimePoint) (μ ν : Fin 4) : ℝ :=
  let r := Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2)
  let rs := schwarzschildRadius consts M
  if r > rs then
    match μ, ν with
    | 0, 0 => -(1 - rs / r)⁻¹ / consts.c^2
    | 1, 1 => (1 - rs / r)
    | 2, 2 => r⁻¹^2
    | 3, 3 => (r^2 * (Real.sin (x 2))^2)⁻¹
    | _, _ => 0
  else 0

noncomputable def schwarzschildMetricDeterminant (consts : GRConstants) (M : ℝ) (_hM : M > 0)
    (x : SpaceTimePoint) : ℝ :=
  let r := Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2)
  let rs := schwarzschildRadius consts M
  if r > rs then -consts.c^2 * r^4 * (Real.sin (x 2))^2 else 0

/-- Well-formedness package for abstract Schwarzschild metric data. -/
def SchwarzschildMetricWellFormed (consts : GRConstants) (M : ℝ) (hM : M > 0) : Prop :=
  (∀ x μ ν,
      schwarzschildMetricTensor consts M hM x μ ν = schwarzschildMetricTensor consts M hM x ν μ) ∧
  (∀ x, schwarzschildMetricDeterminant consts M hM x ≠ 0) ∧
  (∀ x μ ν,
      ∑ ρ,
        schwarzschildInverseMetricTensor consts M hM x μ ρ *
          schwarzschildMetricTensor consts M hM x ρ ν = if μ = ν then 1 else 0)

noncomputable def schwarzschildMetric (consts : GRConstants) (M : ℝ) (hM : M > 0)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.schwarzschildMetricWellFormed
        (SchwarzschildMetricWellFormed consts M hM)) :
    SpacetimeMetric := by
  rcases h_phys with ⟨h_symm, h_nondeg, h_inv⟩
  refine
    { g := schwarzschildMetricTensor consts M hM
      symmetric := ?_
      inverseMetric := schwarzschildInverseMetricTensor consts M hM
      metricDeterminant := schwarzschildMetricDeterminant consts M hM
      metric_nondegenerate := ?_
      inverse_metric_identity := ?_
      signature := fun _ μ => if μ = 0 then -1 else 1 }
  · exact h_symm
  · exact h_nondeg
  · exact h_inv

/-- Structure for Schwarzschild spacetime theory -/
structure SchwarzschildTheory (consts : GRConstants) (M : ℝ) (hM : M > 0) where
  /-- Assumed well-formedness of Schwarzschild metric data. -/
  metric_well_formed :
    PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.schwarzschildMetricWellFormed
      (SchwarzschildMetricWellFormed consts M hM)
  /-- Connection theory for Schwarzschild metric -/
  connection : ConnectionTheory (schwarzschildMetric consts M hM metric_well_formed)
  /-- Curvature theory for Schwarzschild metric -/
  curvature : CurvatureTheory (schwarzschildMetric consts M hM metric_well_formed)
  /-- Schwarzschild metric solves vacuum Einstein equations -/
  solves_vacuum_efe : VacuumEFE consts curvature
  /-- Schwarzschild is static: has timelike Killing vector ∂_t -/
  is_static : Static connection
  /-- Timelike Killing vector (time translation) -/
  timeKilling : SpaceTimePoint → Fin 4 → ℝ
  /-- Rotational Killing vectors (spherical symmetry) -/
  rotKilling : Fin 3 → SpaceTimePoint → Fin 4 → ℝ
  /-- Time translation is timelike Killing -/
  time_is_timelike_killing : TimelikeKilling connection timeKilling
  /-- Rotations are spacelike Killing -/
  rot_is_spacelike_killing : ∀ i, SpacelikeKilling connection (rotKilling i)
  /-- Event horizon located at r = r_s = 2GM/c² -/
  horizon_location :
    KillingHorizon connection timeKilling =
      {x : SpaceTimePoint | Real.sqrt ((x 1)^2 + (x 2)^2 + (x 3)^2) = schwarzschildRadius consts M}
  /-- Curvature singularity at r = 0 (coordinate-independent)

      The Kretschmann scalar K = R_μνρσ R^μνρσ diverges as r → 0.
      For Schwarzschild: K = 48G²M²/r⁶ → ∞ as r → 0.

      This is a true curvature singularity, not a coordinate artifact. -/
  singularity_at_origin :
    ∀ (seq : ℕ → SpaceTimePoint),
      (∀ n, Real.sqrt ((seq n 1)^2 + (seq n 2)^2 + (seq n 3)^2) > 0) →
      (Filter.Tendsto (fun n => Real.sqrt ((seq n 1)^2 + (seq n 2)^2 + (seq n 3)^2))
        Filter.atTop (nhds 0)) →
      -- Kretschmann scalar diverges
      Filter.Tendsto (fun n =>
        ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
          (curvature.riemannTensor (seq n) μ ν ρ σ)^2)
        Filter.atTop Filter.atTop

/-- Structure for uniqueness theorems (Birkhoff) -/
  structure UniquenessTheorems (consts : GRConstants) where
  /-- Birkhoff's theorem: Schwarzschild is unique spherically symmetric vacuum solution -/
  birkhoff_theorem : ∀ (metric : SpacetimeMetric) (conn : ConnectionTheory metric)
    (curv : CurvatureTheory metric),
    VacuumEFE consts curv →
    (∃ (ξs : Fin 3 → SpaceTimePoint → Fin 4 → ℝ),
      ∀ i, KillingVector conn (ξs i)) →
    ∃ (M : ℝ) (hM : M > 0)
      (h_phys :
        PhysicsLogic.PhysicsAssumption
          PhysicsLogic.AssumptionId.schwarzschildMetricWellFormed
          (SchwarzschildMetricWellFormed consts M hM)),
      metric = schwarzschildMetric consts M hM h_phys

/-- Structure for Schwarzschild geodesic motion -/
structure SchwarzschildGeodesics (consts : GRConstants) (M : ℝ) (hM : M > 0)
    (st : SchwarzschildTheory consts M hM) where
  /-- Circular orbit radii for massive particles -/
  circularOrbitRadius : ℝ → ℝ
  /-- ISCO (Innermost Stable Circular Orbit) radius -/
  iscoRadius : ℝ
  /-- ISCO = 6GM/c² for Schwarzschild -/
  isco_value : iscoRadius = 6 * consts.G * M / consts.c^2
  /-- Photon sphere radius -/
  photonSphereRadius : ℝ
  /-- Photon sphere = 3GM/c² for Schwarzschild -/
  photon_sphere_value : photonSphereRadius = 3 * consts.G * M / consts.c^2

end PhysicsLogic.GeneralRelativity
