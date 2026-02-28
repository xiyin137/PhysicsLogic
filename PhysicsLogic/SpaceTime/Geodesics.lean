import PhysicsLogic.SpaceTime.Connections
import PhysicsLogic.SpaceTime.Curves
import PhysicsLogic.SpaceTime.Curvature

namespace PhysicsLogic.SpaceTime

variable {metric : SpacetimeMetric}

/-- Geodesic equation - PURELY GEOMETRIC

    A curve is a geodesic if its tangent vector is parallel transported.

    d²x^μ/dλ² + Γ^μ_νρ (dx^ν/dλ)(dx^ρ/dλ) = 0

    This is true for ANY metric, whether or not it satisfies Einstein equations.
-/
def Geodesic (ct : ConnectionTheory metric) (γ : Curve) : Prop :=
  ∀ t μ,
    deriv (deriv (fun s => γ s μ)) t +
    (∑ ν, ∑ ρ, ct.christoffel (γ t) μ ν ρ *
      deriv (fun s => γ s ν) t *
      deriv (fun s => γ s ρ) t) = 0

/-- Timelike geodesic -/
def TimelikeGeodesic (ct : ConnectionTheory metric) (γ : Curve) : Prop :=
  Geodesic ct γ ∧ TimelikeCurve metric γ

/-- Null geodesic -/
def NullGeodesic (ct : ConnectionTheory metric) (γ : Curve) : Prop :=
  Geodesic ct γ ∧ NullCurve metric γ

/-- Spacelike geodesic -/
def SpacelikeGeodesic (ct : ConnectionTheory metric) (γ : Curve) : Prop :=
  Geodesic ct γ ∧ SpacelikeCurve metric γ

/-- Structure for geodesic theory -/
structure GeodesicTheory (metric : SpacetimeMetric) where
  /-- The underlying connection theory -/
  connTheory : ConnectionTheory metric
  /-- The underlying curvature theory -/
  curvTheory : CurvatureTheory metric
  /-- Geodesic deviation equation (measures tidal forces) -/
  geodesicDeviation : (γ : Curve) → (ξ : ℝ → Fin 4 → ℝ) → Geodesic connTheory γ → Prop
  /-- Affine parameter for geodesics -/
  AffineParameter : (γ : Curve) → Geodesic connTheory γ → Type _

/-- In Minkowski space, inertial observers follow geodesics -/
theorem inertial_is_geodesic (ct : ConnectionTheory minkowskiMetric) (γ : Worldline) :
    (∀ x μ ν ρ, ct.christoffel x μ ν ρ = 0) →
    (∀ t μ, deriv (deriv (fun s => γ s μ)) t = 0) →
    Geodesic ct γ := by
  intro h_christoffel_zero h_inertial t μ
  have h_second_deriv : deriv (deriv (fun s => γ s μ)) t = 0 := h_inertial t μ
  simp [h_christoffel_zero, h_second_deriv]

end PhysicsLogic.SpaceTime
