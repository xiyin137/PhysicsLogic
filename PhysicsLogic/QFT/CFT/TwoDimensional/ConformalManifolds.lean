import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.QFT.CFT.TwoDimensional

set_option autoImplicit false

/-- `C^2/Z_k` twisted-sector counting with exactly marginal descendants in `(4,4)` SCFT. -/
structure OrbifoldConformalManifoldData where
  orbifoldOrder : Nat
  twistedSectorCount : Nat
  exactlyMarginalCount : Nat

/-- Twisted-sector count `(k-1)` and exactly-marginal count `4(k-1)` for `C^2/Z_k`. -/
def OrbifoldConformalManifoldDimensionFormula
    (data : OrbifoldConformalManifoldData) : Prop :=
  data.orbifoldOrder > 1 /\
  data.twistedSectorCount = data.orbifoldOrder - 1 /\
  data.exactlyMarginalCount = 4 * data.twistedSectorCount

/-- Assumed `C^2/Z_k` conformal-manifold dimension counting package. -/
theorem orbifold_conformal_manifold_dimension_formula
    (data : OrbifoldConformalManifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dOrbifoldConformalManifoldDimensionFormula
      (OrbifoldConformalManifoldDimensionFormula data)) :
    OrbifoldConformalManifoldDimensionFormula data := by
  exact h_phys

/-- Squared complex distance `|z₁-z₂|²` used in two-point normalization formulas. -/
def squaredDistance (z₁ z₂ : ℂ) : ℝ :=
  Complex.normSq (z₁ - z₂)

/-- Zamolodchikov metric/two-point function package for exactly marginal operators. -/
def ZamolodchikovMetricTwoPointNormalization {I : Type*}
    (G : I → I → ℝ) (twoPoint : I → I → ℂ → ℂ → ℂ) : Prop :=
  (∀ i j : I, G i j = G j i) /\
  (∀ i : I, 0 ≤ G i i) /\
  (∀ i j : I, ∀ z₁ z₂ : ℂ, z₁ ≠ z₂ ->
    twoPoint i j z₁ z₂ =
      ((G i j : ℂ) / ((squaredDistance z₁ z₂ : ℂ) ^ (2 : Nat))))

/-- Assumed Zamolodchikov-metric package from marginal-operator two-point normalization. -/
theorem zamolodchikov_metric_two_point_normalization {I : Type*}
    (G : I → I → ℝ) (twoPoint : I → I → ℂ → ℂ → ℂ)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dZamolodchikovMetricTwoPointNormalization
      (ZamolodchikovMetricTwoPointNormalization G twoPoint)) :
    ZamolodchikovMetricTwoPointNormalization G twoPoint := by
  exact h_phys

/-- Distinguishing regular/singular fixed points on the `k=2` orbifold conformal manifold. -/
structure OrbifoldKTwoConformalManifoldData where
  relativeModuliDimension : Nat
  z2FixedPointCount : Nat
  regularFixedPointCount : Nat
  singularFixedPointCount : Nat
  aleResolutionTripletDimension : Nat
  bFieldPeriodSingletDimension : Nat

/-- `k=2` data: `M̃₂=(R³×S¹)/Z₂`, with triplet ALE and singlet `B`-period directions. -/
def OrbifoldKTwoModuliFixedPointDistinction
    (data : OrbifoldKTwoConformalManifoldData) : Prop :=
  data.relativeModuliDimension = 4 /\
  data.z2FixedPointCount = 2 /\
  data.regularFixedPointCount = 1 /\
  data.singularFixedPointCount = 1 /\
  data.aleResolutionTripletDimension = 3 /\
  data.bFieldPeriodSingletDimension = 1

/-- Assumed `k=2` orbifold conformal-manifold fixed-point distinction package. -/
theorem orbifold_k_two_moduli_fixed_point_distinction
    (data : OrbifoldKTwoConformalManifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dOrbifoldKTwoModuliFixedPointDistinction
      (OrbifoldKTwoModuliFixedPointDistinction data)) :
    OrbifoldKTwoModuliFixedPointDistinction data := by
  exact h_phys

end PhysicsLogic.QFT.CFT.TwoDimensional
