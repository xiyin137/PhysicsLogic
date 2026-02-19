import PhysicsLogic.SpaceTime.Causality
import PhysicsLogic.SpaceTime.Curves

namespace PhysicsLogic.SpaceTime

/-- Spacelike hypersurface (Cauchy surface candidate) -/
def SpacelikeHypersurface (metric : SpacetimeMetric) (S : Set SpaceTimePoint) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Spacelike metric x y

/-- Timelike hypersurface -/
def TimelikeHypersurface (metric : SpacetimeMetric) (S : Set SpaceTimePoint) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Timelike metric x y

/-- Null hypersurface with respect to a given metric (event horizon is an example).
    Every pair of distinct points on S is lightlike separated in the given metric. -/
def NullHypersurface (metric : SpacetimeMetric) (S : Set SpaceTimePoint) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Lightlike metric x y

/-- Foliation of spacetime by spacelike hypersurfaces -/
structure Foliation (metric : SpacetimeMetric) where
  leaves : ℝ → Set SpaceTimePoint
  spacelike : ∀ t, SpacelikeHypersurface metric (leaves t)
  covers : ∀ x : SpaceTimePoint, ∃ t, x ∈ leaves t

/-- Cauchy surface: spacelike surface intersected exactly once by every inextendible timelike curve.
    The inextendibility condition is essential — without it, any spacelike surface would trivially
    satisfy the intersection property (a curve segment might not reach S). -/
def CauchySurface (metric : SpacetimeMetric) (S : Set SpaceTimePoint) : Prop :=
  SpacelikeHypersurface metric S ∧
  ∀ γ : Curve, TimelikeCurve metric γ → Inextendible γ →
    ∃! t : ℝ, γ t ∈ S

/-- Globally hyperbolic spacetime: has Cauchy surface -/
def GloballyHyperbolic (metric : SpacetimeMetric) : Prop :=
  ∃ S, CauchySurface metric S

/-- Achronal set: no two points are timelike separated -/
def Achronal (metric : SpacetimeMetric) (S : Set SpaceTimePoint) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ¬Timelike metric x y

/-- Edgeless achronal set: achronal and closed under causal limits.
    A point p is on the edge of S if every neighborhood of p contains points
    q, r with q ≪ p ≪ r (chronologically) and a timelike curve from q to r
    not meeting S. An edgeless set has no such points. -/
def Edgeless (metric : SpacetimeMetric) (S : Set SpaceTimePoint) : Prop :=
  Achronal metric S ∧
  ∀ p ∈ S, ¬∃ (q r : SpaceTimePoint),
    Timelike metric q p ∧ Timelike metric p r ∧
    ∃ γ : Curve, TimelikeCurve metric γ ∧ γ 0 = q ∧ (∃ t, γ t = r) ∧
    ∀ t, γ t ∉ S

/-- Domain of dependence: region determined by data on S.
    A point x is in D(S) if every inextendible timelike curve through x intersects S. -/
def DomainOfDependence (metric : SpacetimeMetric) (S : Set SpaceTimePoint) :
    Set SpaceTimePoint :=
  {x | ∀ γ : Curve, TimelikeCurve metric γ → Inextendible γ →
       (∃ t₀, γ t₀ = x) → (∃ t₁, γ t₁ ∈ S)}

/-- Structure for hypersurface geometry -/
structure HypersurfaceTheory (metric : SpacetimeMetric) (S : Set SpaceTimePoint) where
  /-- Normal vector to hypersurface -/
  normalVector : (x : SpaceTimePoint) → x ∈ S → Fin 4 → ℝ
  /-- Extrinsic curvature (second fundamental form) of embedded hypersurface -/
  extrinsicCurvature : SpaceTimePoint → Fin 4 → Fin 4 → ℝ
  /-- Induced metric on hypersurface -/
  inducedMetric : SpacetimeMetric

end PhysicsLogic.SpaceTime
