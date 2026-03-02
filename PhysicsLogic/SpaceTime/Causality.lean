import PhysicsLogic.SpaceTime.Metrics
import PhysicsLogic.SpaceTime.Minkowski
import PhysicsLogic.Assumptions

namespace PhysicsLogic.SpaceTime

/-- Causal character of separation (general metric) -/
inductive CausalCharacter
  | Timelike
  | Null
  | Spacelike

/-- Determine causal character from metric -/
noncomputable def causalCharacter (metric : SpacetimeMetric) (x y : SpaceTimePoint) : CausalCharacter :=
  let v := fun μ => x μ - y μ
  let norm := innerProduct metric x v v
  if norm < 0 then CausalCharacter.Timelike
  else if norm = 0 then CausalCharacter.Null
  else CausalCharacter.Spacelike

/-- Timelike separation (works for any metric) -/
def Timelike (metric : SpacetimeMetric) (x y : SpaceTimePoint) : Prop :=
  innerProduct metric x (fun μ => x μ - y μ) (fun μ => x μ - y μ) < 0

/-- Spacelike separation (works for any metric) -/
def Spacelike (metric : SpacetimeMetric) (x y : SpaceTimePoint) : Prop :=
  innerProduct metric x (fun μ => x μ - y μ) (fun μ => x μ - y μ) > 0

/-- Lightlike (null) separation (works for any metric) -/
def Lightlike (metric : SpacetimeMetric) (x y : SpaceTimePoint) : Prop :=
  innerProduct metric x (fun μ => x μ - y μ) (fun μ => x μ - y μ) = 0

/-- Causal classification is exhaustive -/
theorem causal_trichotomy (metric : SpacetimeMetric) (x y : SpaceTimePoint) :
  Timelike metric x y ∨ Spacelike metric x y ∨ Lightlike metric x y := by
  simp only [Timelike, Spacelike, Lightlike]
  rcases lt_trichotomy (innerProduct metric x (fun μ => x μ - y μ) (fun μ => x μ - y μ)) 0 with h | h | h
  · left; exact h
  · right; right; exact h
  · right; left; exact h

/-- Causal relation: x can causally influence y -/
def Causal (metric : SpacetimeMetric) (x y : SpaceTimePoint) : Prop :=
  (time y ≥ time x) ∧ (Timelike metric x y ∨ Lightlike metric x y)

/-- Future light cone (general metric) -/
def FutureLightCone (metric : SpacetimeMetric) (p : SpaceTimePoint) : Set SpaceTimePoint :=
  {q | time q > time p ∧ Lightlike metric p q}

/-- Past light cone (general metric) -/
def PastLightCone (metric : SpacetimeMetric) (p : SpaceTimePoint) : Set SpaceTimePoint :=
  {q | time q < time p ∧ Lightlike metric p q}

/-- Causal future (general metric) -/
def CausalFuture (metric : SpacetimeMetric) (p : SpaceTimePoint) : Set SpaceTimePoint :=
  {q | Causal metric p q}

/-- Causal past (general metric) -/
def CausalPast (metric : SpacetimeMetric) (p : SpaceTimePoint) : Set SpaceTimePoint :=
  {q | Causal metric q p}

/-- Spacelike separated sets -/
def SpacelikeSeparated (metric : SpacetimeMetric) (A B : Set SpaceTimePoint) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, Spacelike metric a b

/-- Chronological future (strict timelike) -/
def ChronologicalFuture (metric : SpacetimeMetric) (p : SpaceTimePoint) : Set SpaceTimePoint :=
  {q | time q > time p ∧ Timelike metric p q}

/-- Chronological past (strict timelike) -/
def ChronologicalPast (metric : SpacetimeMetric) (p : SpaceTimePoint) : Set SpaceTimePoint :=
  {q | time q < time p ∧ Timelike metric q p}

/-- Causal diamond (Alexandrov set) -/
def CausalDiamond (metric : SpacetimeMetric) (p q : SpaceTimePoint) : Set SpaceTimePoint :=
  CausalFuture metric p ∩ CausalPast metric q

/-- For the flat Minkowski metric, `innerProduct` matches `minkowskiInnerProduct`. -/
theorem innerProduct_minkowski_eq (x : SpaceTimePoint) (v w : Fin 4 → ℝ) :
    innerProduct minkowskiMetric x v w = minkowskiInnerProduct v w := by
  simp [innerProduct, minkowskiMetric, minkowskiInnerProduct, Fin.sum_univ_four]

/-- Timelike criterion in Minkowski space as interval negativity. -/
theorem timelike_iff_minkowskiInterval_neg (x y : SpaceTimePoint) :
    Timelike minkowskiMetric x y ↔ minkowskiInterval x y < 0 := by
  simp [Timelike, minkowskiInterval, innerProduct_minkowski_eq]

/-- Spacelike criterion in Minkowski space as interval positivity. -/
theorem spacelike_iff_minkowskiInterval_pos (x y : SpaceTimePoint) :
    Spacelike minkowskiMetric x y ↔ minkowskiInterval x y > 0 := by
  simp [Spacelike, minkowskiInterval, innerProduct_minkowski_eq]

/-- Lightlike criterion in Minkowski space as vanishing interval. -/
theorem lightlike_iff_minkowskiInterval_zero (x y : SpaceTimePoint) :
    Lightlike minkowskiMetric x y ↔ minkowskiInterval x y = 0 := by
  simp [Lightlike, minkowskiInterval, innerProduct_minkowski_eq]

/-- Lorentz transformation preserves causal structure (Minkowski only). -/
theorem lorentz_preserves_timelike (Λ : LorentzTransform) (x y : SpaceTimePoint) :
    Timelike minkowskiMetric x y → Timelike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  intro h_timelike
  have h_interval_neg : minkowskiInterval x y < 0 :=
    (timelike_iff_minkowskiInterval_neg x y).1 h_timelike
  have h_interval_inv :
      minkowskiInterval (Λ.apply x) (Λ.apply y) = minkowskiInterval x y :=
    lorentz_preserves_interval Λ x y
  have h_image_interval_neg : minkowskiInterval (Λ.apply x) (Λ.apply y) < 0 := by
    simpa [h_interval_inv] using h_interval_neg
  exact (timelike_iff_minkowskiInterval_neg (Λ.apply x) (Λ.apply y)).2 h_image_interval_neg

theorem lorentz_preserves_spacelike (Λ : LorentzTransform) (x y : SpaceTimePoint) :
    Spacelike minkowskiMetric x y → Spacelike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  intro h_spacelike
  have h_interval_pos : minkowskiInterval x y > 0 :=
    (spacelike_iff_minkowskiInterval_pos x y).1 h_spacelike
  have h_interval_inv :
      minkowskiInterval (Λ.apply x) (Λ.apply y) = minkowskiInterval x y :=
    lorentz_preserves_interval Λ x y
  have h_image_interval_pos : minkowskiInterval (Λ.apply x) (Λ.apply y) > 0 := by
    simpa [h_interval_inv] using h_interval_pos
  exact (spacelike_iff_minkowskiInterval_pos (Λ.apply x) (Λ.apply y)).2 h_image_interval_pos

theorem lorentz_preserves_lightlike (Λ : LorentzTransform) (x y : SpaceTimePoint) :
    Lightlike minkowskiMetric x y → Lightlike minkowskiMetric (Λ.apply x) (Λ.apply y) := by
  intro h_lightlike
  have h_interval_zero : minkowskiInterval x y = 0 :=
    (lightlike_iff_minkowskiInterval_zero x y).1 h_lightlike
  have h_interval_inv :
      minkowskiInterval (Λ.apply x) (Λ.apply y) = minkowskiInterval x y :=
    lorentz_preserves_interval Λ x y
  have h_image_interval_zero : minkowskiInterval (Λ.apply x) (Λ.apply y) = 0 := by
    simpa [h_interval_inv] using h_interval_zero
  exact (lightlike_iff_minkowskiInterval_zero (Λ.apply x) (Λ.apply y)).2 h_image_interval_zero

end PhysicsLogic.SpaceTime
