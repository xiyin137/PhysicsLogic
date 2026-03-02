import PhysicsLogic.SpaceTime.Metrics
import PhysicsLogic.Assumptions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PhysicsLogic.SpaceTime

/-- Minkowski metric (flat spacetime) -/
noncomputable def minkowskiMetric : SpacetimeMetric where
  g := fun _ μ ν =>
    if μ = ν then
      if μ = 0 then -1 else 1
    else 0
  symmetric := by
    intro x μ ν
    by_cases h1 : μ = ν
    · simp [h1]
    · by_cases h2 : ν = μ
      · simp [h2]
      · simp [h1, Ne.symm h1]
  inverseMetric := fun _ μ ν =>
    if μ = ν then
      if μ = 0 then -1 else 1
    else 0
  metricDeterminant := fun _ => -1
  metric_nondegenerate := by intro _; norm_num
  inverse_metric_identity := by
    intro x μ ν
    fin_cases μ <;> fin_cases ν <;> simp
  signature := fun _ μ => if μ = 0 then -1 else 1

/-- Minkowski inner product (constant across spacetime) -/
noncomputable def minkowskiInnerProduct (v w : Fin 4 → ℝ) : ℝ :=
  -(v 0 * w 0) + (v 1 * w 1) + (v 2 * w 2) + (v 3 * w 3)

/-- Interval between two events in Minkowski spacetime -/
noncomputable def minkowskiInterval (x y : SpaceTimePoint) : ℝ :=
  minkowskiInnerProduct (fun μ => x μ - y μ) (fun μ => x μ - y μ)

/-- Minkowski metric is symmetric -/
theorem minkowski_symm (x y : SpaceTimePoint) :
  minkowskiInnerProduct x y = minkowskiInnerProduct y x := by
  simp [minkowskiInnerProduct]
  ring

/-- Minkowski metric is bilinear -/
theorem minkowski_bilinear (a b : ℝ) (x y z : SpaceTimePoint) :
  minkowskiInnerProduct (fun μ => a * x μ + b * y μ) z =
  a * minkowskiInnerProduct x z + b * minkowskiInnerProduct y z := by
  simp [minkowskiInnerProduct]
  ring

/-- Interval is symmetric -/
theorem interval_symm (x y : SpaceTimePoint) :
  minkowskiInterval x y = minkowskiInterval y x := by
  simp [minkowskiInterval, minkowskiInnerProduct]
  ring

/-- Structure for Minkowski spacetime with proper time -/
structure MinkowskiSpacetime where
  /-- Proper time along a path in Minkowski spacetime -/
  properTime : (ℝ → SpaceTimePoint) → ℝ → ℝ → ℝ
  /-- Rest frame of an observer -/
  restFrame : (ℝ → SpaceTimePoint) → ℝ → LorentzTransform

/- ============= LORENTZ TRANSFORMATIONS (GENERAL DIMENSION) ============= -/

/-- Minkowski inner product in d dimensions with signature (-,+,+,...,+) -/
noncomputable def minkowskiInnerProductGen {d : ℕ} [NeZero d] (v w : Fin d → ℝ) : ℝ :=
  -(v 0 * w 0) + ∑ i : Fin d, if i = 0 then 0 else v i * w i

/-- General Lorentz transformation in d dimensions: preserves Minkowski metric -/
structure LorentzTransformGen (d : ℕ) [NeZero d] where
  matrix : Fin d → Fin d → ℝ
  preserves_metric : ∀ x y : Fin d → ℝ,
    minkowskiInnerProductGen x y = minkowskiInnerProductGen
      (fun μ => ∑ ν, matrix μ ν * x ν)
      (fun μ => ∑ ν, matrix μ ν * y ν)

/-- Apply general Lorentz transformation -/
def LorentzTransformGen.apply {d : ℕ} [NeZero d]
  (Λ : LorentzTransformGen d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun μ => ∑ ν, Λ.matrix μ ν * x ν

/-- Identity Lorentz transformation in d dimensions -/
noncomputable def LorentzTransformGen.id (d : ℕ) [NeZero d] : LorentzTransformGen d where
  matrix := fun μ ν => if μ = ν then 1 else 0
  preserves_metric := by
    intro x y
    simp [minkowskiInnerProductGen]

/-- Properness marker predicate for Lorentz transformations.
At this abstraction level we track the interface without committing to a
determinant formalization. -/
def IsProperLorentzGen {d : ℕ} [NeZero d] (_Λ : LorentzTransformGen d) : Prop := True

/-- Orthochronous marker predicate: forward time orientation is preserved. -/
def IsOrthochronousLorentzGen {d : ℕ} [NeZero d] (Λ : LorentzTransformGen d) : Prop :=
  Λ.matrix 0 0 ≥ 1

/-- Proper-orthochronous Lorentz transformation marker in general dimension.
`proper` and `orthochronous` are interface predicates at this abstraction layer. -/
structure RestrictedLorentzTransformGen (d : ℕ) [NeZero d] where
  toLorentz : LorentzTransformGen d
  proper : IsProperLorentzGen toLorentz
  orthochronous : IsOrthochronousLorentzGen toLorentz

/-- Dimension-generic Poincaré transformation `(Λ, a)` acting as `x ↦ Λx + a`. -/
structure PoincareTransformGen (d : ℕ) [NeZero d] where
  /-- Lorentz part `Λ`. -/
  lorentz : LorentzTransformGen d
  /-- Translation part `a`. -/
  translation : Fin d → ℝ

/-- Apply a dimension-generic Poincaré transformation to a spacetime point. -/
def PoincareTransformGen.apply {d : ℕ} [NeZero d]
    (g : PoincareTransformGen d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun μ => (∑ ν, g.lorentz.matrix μ ν * x ν) + g.translation μ

/-- Image of a region under a dimension-generic Poincaré transformation. -/
def poincareImageGen {d : ℕ} [NeZero d]
    (g : PoincareTransformGen d) (O : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {x | ∃ y ∈ O, x = g.apply y}

/-- Identity element of the dimension-generic Poincaré group. -/
noncomputable def PoincareTransformGen.id (d : ℕ) [NeZero d] : PoincareTransformGen d where
  lorentz := LorentzTransformGen.id d
  translation := fun _ => 0

/-- Poincaré composition in general dimension:
`(Λ₁,a₁) ∘ (Λ₂,a₂) = (Λ₁Λ₂, Λ₁a₂ + a₁)`. -/
noncomputable def PoincareTransformGen.compose {d : ℕ} [NeZero d]
    (g₁ g₂ : PoincareTransformGen d) : PoincareTransformGen d where
  lorentz :=
    { matrix := fun μ ν => ∑ κ, g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν
      preserves_metric := by
        intro x y
        let x' : Fin d → ℝ := fun κ => ∑ ν, g₂.lorentz.matrix κ ν * x ν
        let y' : Fin d → ℝ := fun κ => ∑ ν, g₂.lorentz.matrix κ ν * y ν
        have h₂ : minkowskiInnerProductGen x y = minkowskiInnerProductGen x' y' := by
          simpa [x', y'] using g₂.lorentz.preserves_metric x y
        have h₁ :
            minkowskiInnerProductGen x' y' =
            minkowskiInnerProductGen
              (fun μ => ∑ κ, g₁.lorentz.matrix μ κ * x' κ)
              (fun μ => ∑ κ, g₁.lorentz.matrix μ κ * y' κ) := by
          simpa [x', y'] using g₁.lorentz.preserves_metric x' y'
        have hx :
            (fun μ => ∑ κ, g₁.lorentz.matrix μ κ * x' κ) =
            (fun μ => ∑ ν, (∑ κ, g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) * x ν) := by
          ext μ
          unfold x'
          calc
            ∑ κ, g₁.lorentz.matrix μ κ * (∑ ν, g₂.lorentz.matrix κ ν * x ν)
                = ∑ κ, ∑ ν, g₁.lorentz.matrix μ κ * (g₂.lorentz.matrix κ ν * x ν) := by
                    simp [Finset.mul_sum]
            _ = ∑ κ, ∑ ν, x ν * (g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) := by
                  simp [mul_left_comm, mul_comm]
            _ = ∑ ν, ∑ κ, x ν * (g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) := by
                  rw [Finset.sum_comm]
            _ = ∑ ν, (∑ κ, g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) * x ν := by
                  simp [mul_comm, Finset.mul_sum]
        have hy :
            (fun μ => ∑ κ, g₁.lorentz.matrix μ κ * y' κ) =
            (fun μ => ∑ ν, (∑ κ, g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) * y ν) := by
          ext μ
          unfold y'
          calc
            ∑ κ, g₁.lorentz.matrix μ κ * (∑ ν, g₂.lorentz.matrix κ ν * y ν)
                = ∑ κ, ∑ ν, g₁.lorentz.matrix μ κ * (g₂.lorentz.matrix κ ν * y ν) := by
                    simp [Finset.mul_sum]
            _ = ∑ κ, ∑ ν, y ν * (g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) := by
                  simp [mul_left_comm, mul_comm]
            _ = ∑ ν, ∑ κ, y ν * (g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) := by
                  rw [Finset.sum_comm]
            _ = ∑ ν, (∑ κ, g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν) * y ν := by
                  simp [mul_comm, Finset.mul_sum]
        exact h₂.trans (h₁.trans (by simp [hx, hy])) }
  translation := fun μ => g₁.translation μ + ∑ ν, g₁.lorentz.matrix μ ν * g₂.translation ν

/-- Restricted (proper-orthochronous) Poincaré transformation in general dimension. -/
structure RestrictedPoincareTransformGen (d : ℕ) [NeZero d] where
  lorentz : RestrictedLorentzTransformGen d
  translation : Fin d → ℝ

/-- Forget the restriction markers and view a restricted Poincaré element
as an ordinary Poincaré transformation. -/
def RestrictedPoincareTransformGen.toPoincare {d : ℕ} [NeZero d]
    (g : RestrictedPoincareTransformGen d) : PoincareTransformGen d where
  lorentz := g.lorentz.toLorentz
  translation := g.translation

/-- Apply a restricted Poincaré transformation to a spacetime point. -/
def RestrictedPoincareTransformGen.apply {d : ℕ} [NeZero d]
    (g : RestrictedPoincareTransformGen d) (x : Fin d → ℝ) : Fin d → ℝ :=
  (g.toPoincare).apply x

/-- Image of a region under a restricted Poincaré transformation. -/
def restrictedPoincareImageGen {d : ℕ} [NeZero d]
    (g : RestrictedPoincareTransformGen d) (O : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  poincareImageGen g.toPoincare O

/-- In 4D, the general Minkowski inner product specializes to the explicit 4D form. -/
theorem minkowskiInnerProductGen_four (x y : Fin 4 → ℝ) :
    minkowskiInnerProductGen x y = minkowskiInnerProduct x y := by
  simp [minkowskiInnerProductGen, minkowskiInnerProduct, Fin.sum_univ_four]
  ring

/- ============= 4D LORENTZ TRANSFORMATIONS (BACKWARD COMPATIBILITY) ============= -/

/-- Lorentz transformation in 4D (backward compatible) -/
structure LorentzTransform where
  matrix : Fin 4 → Fin 4 → ℝ
  preserves_metric : ∀ x y : SpaceTimePoint,
    minkowskiInnerProduct x y = minkowskiInnerProduct
      (fun μ => ∑ ν, matrix μ ν * x ν)
      (fun μ => ∑ ν, matrix μ ν * y ν)

/-- Extensionality for Lorentz transformations -/
@[ext]
theorem LorentzTransform.ext {Λ₁ Λ₂ : LorentzTransform}
  (h : Λ₁.matrix = Λ₂.matrix) : Λ₁ = Λ₂ := by
  cases Λ₁; cases Λ₂
  congr

/-- Apply Lorentz transformation to spacetime point -/
def LorentzTransform.apply (Λ : LorentzTransform) (x : SpaceTimePoint) : SpaceTimePoint :=
  fun μ => ∑ ν, Λ.matrix μ ν * x ν

/-- Identity Lorentz transformation -/
noncomputable def LorentzTransform.id : LorentzTransform where
  matrix := fun μ ν => if μ = ν then 1 else 0
  preserves_metric := by
    intro x y
    simp [minkowskiInnerProduct]

/-- Convert 4D Lorentz transform to general form -/
def LorentzTransform.toGen (Λ : LorentzTransform) : LorentzTransformGen 4 where
  matrix := Λ.matrix
  preserves_metric := by
    intro x y
    simpa [minkowskiInnerProductGen_four] using Λ.preserves_metric x y

/-- Lorentz transformation preserves intervals -/
theorem lorentz_preserves_interval (Λ : LorentzTransform) (x y : SpaceTimePoint) :
  minkowskiInterval (Λ.apply x) (Λ.apply y) = minkowskiInterval x y := by
  simp only [minkowskiInterval, LorentzTransform.apply]
  have h : (fun μ => ∑ ν, Λ.matrix μ ν * x ν - ∑ ν, Λ.matrix μ ν * y ν) =
           (fun μ => ∑ ν, Λ.matrix μ ν * (x ν - y ν)) := by
    ext μ
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext ν
    ring
  rw [h]
  exact (Λ.preserves_metric (fun ν => x ν - y ν) (fun ν => x ν - y ν)).symm

/-- Boost velocity must be subluminal -/
def ValidBoostVelocity (v : ℝ) : Prop := v^2 < 1

/-- Matrix entries for an x-direction Lorentz boost. -/
noncomputable def lorentzBoostMatrix (v : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun μ ν =>
    let γ := 1 / Real.sqrt (1 - v^2)
    match μ, ν with
    | 0, 0 => γ
    | 0, 1 => -γ * v
    | 1, 0 => -γ * v
    | 1, 1 => γ
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0

/-- Lorentz boost in x-direction -/
noncomputable def lorentzBoost (v : ℝ) (_h : ValidBoostVelocity v)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.lorentzBoostPreservesMetric
        (∀ x y : SpaceTimePoint,
          minkowskiInnerProduct x y = minkowskiInnerProduct
            (fun μ => ∑ ν, lorentzBoostMatrix v μ ν * x ν)
            (fun μ => ∑ ν, lorentzBoostMatrix v μ ν * y ν))) :
    LorentzTransform where
  matrix := lorentzBoostMatrix v
  preserves_metric := by
    simpa [lorentzBoostMatrix] using h_phys

/-- Matrix entries for a spatial rotation around the z-axis. -/
noncomputable def spatialRotationMatrix (θ : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun μ ν =>
    match μ, ν with
    | 0, 0 => 1
    | 1, 1 => Real.cos θ
    | 1, 2 => -(Real.sin θ)
    | 2, 1 => Real.sin θ
    | 2, 2 => Real.cos θ
    | 3, 3 => 1
    | _, _ => 0

/-- Spatial rotation around z-axis -/
noncomputable def spatialRotation (θ : ℝ)
    (h_phys :
      PhysicsLogic.PhysicsAssumption
        PhysicsLogic.AssumptionId.spatialRotationPreservesMetric
        (∀ x y : SpaceTimePoint,
          minkowskiInnerProduct x y = minkowskiInnerProduct
            (fun μ => ∑ ν, spatialRotationMatrix θ μ ν * x ν)
            (fun μ => ∑ ν, spatialRotationMatrix θ μ ν * y ν))) :
    LorentzTransform where
  matrix := spatialRotationMatrix θ
  preserves_metric := by
    simpa [spatialRotationMatrix] using h_phys

end PhysicsLogic.SpaceTime
