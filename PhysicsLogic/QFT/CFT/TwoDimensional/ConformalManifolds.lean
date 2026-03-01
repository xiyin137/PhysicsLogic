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

/-- D1-D5 conformal-manifold/U-duality arithmetic data for the 2D `(4,4)` CFT. -/
structure D1D5ConformalManifoldGeometryData where
  q1 : Nat
  q5 : Nat
  gcdCharge : Nat
  invariantK : Nat
  marginalMultipletCount : Nat
  moduliDimension : Nat

/-- D1-D5 conformal-manifold geometry package:
`k = Q1Q5/(gcd(Q1,Q5))^2`, moduli dimension `20`, and multiples-of-four marginal directions. -/
def D1D5ConformalManifoldGeometryPackage
    (data : D1D5ConformalManifoldGeometryData) : Prop :=
  data.q1 > 0 /\
  data.q5 > 0 /\
  data.gcdCharge = Nat.gcd data.q1 data.q5 /\
  data.invariantK * data.gcdCharge ^ (2 : Nat) = data.q1 * data.q5 /\
  data.moduliDimension = 20 /\
  data.moduliDimension = 4 * data.marginalMultipletCount

/-- Assumed D1-D5 conformal-manifold geometry package in the 2D CFT lane. -/
theorem d1_d5_conformal_manifold_geometry_package
    (data : D1D5ConformalManifoldGeometryData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dD1D5ConformalManifoldQuaternionicQuotient
      (D1D5ConformalManifoldGeometryPackage data)) :
    D1D5ConformalManifoldGeometryPackage data := by
  exact h_phys

/-- Axion-dilaton attractor/U-duality data on the D1-D5 conformal-manifold subspace. -/
structure D1D5AttractorTauData where
  q1 : Nat
  q5 : Nat
  gcdCharge : Nat
  gamma0Level : Nat
  tau : ℂ
  tauTilde : ℂ

/-- Attractor/duality package:
`tauTilde = (Q1/Q5) tau`, `Im(tau)>0`, and `Gamma_0(k)` level arithmetic
`k = Q1Q5/(gcd(Q1,Q5))^2`. -/
def D1D5AttractorTauGamma0Package
    (data : D1D5AttractorTauData) : Prop :=
  data.q1 > 0 /\
  data.q5 > 0 /\
  0 < data.tau.im /\
  data.gcdCharge = Nat.gcd data.q1 data.q5 /\
  data.gamma0Level * data.gcdCharge ^ (2 : Nat) = data.q1 * data.q5 /\
  data.tauTilde = ((data.q1 : ℂ) / (data.q5 : ℂ)) * data.tau

/-- Assumed D1-D5 attractor/`Gamma_0(k)` package in the 2D CFT lane. -/
theorem d1_d5_attractor_tau_gamma0_package
    (data : D1D5AttractorTauData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dD1D5AttractorTauGamma0Level
      (D1D5AttractorTauGamma0Package data)) :
    D1D5AttractorTauGamma0Package data := by
  exact h_phys

/-- Symmetric-product orbifold locus data inside the D1-D5 conformal manifold. -/
structure D1D5SymmetricProductOrbifoldData where
  q1 : Nat
  q5 : Nat
  tau : ℂ
  a : Int
  b : Int
  gPrime : ℝ
  singularLocusReTau : ℝ
  symmetricOrbifoldReTau : ℝ

/-- Symmetric-product orbifold package:
regular/singular-locus distinction (`Re(tau)=1/2` vs `Re(tau)=0`) and
U-duality parametrization `(a tau + b)/(Q1 tau + Q5) = 1/2 + i/g'`. -/
def D1D5SymmetricProductOrbifoldLocusPackage
    (data : D1D5SymmetricProductOrbifoldData) : Prop :=
  data.q1 > 0 /\
  data.q5 > 0 /\
  Nat.Coprime data.q1 data.q5 /\
  data.gPrime > 0 /\
  data.singularLocusReTau = 0 /\
  data.symmetricOrbifoldReTau = (1 / 2 : ℝ) /\
  data.singularLocusReTau ≠ data.symmetricOrbifoldReTau /\
  data.a * (data.q5 : Int) - data.b * (data.q1 : Int) = 1 /\
  ((data.q1 : ℂ) * data.tau + (data.q5 : ℂ)) ≠ 0 /\
  (((data.a : ℂ) * data.tau + (data.b : ℂ)) /
      ((data.q1 : ℂ) * data.tau + (data.q5 : ℂ)) =
    ((1 / 2 : ℂ) + Complex.I * (1 / (data.gPrime : ℂ))))

/-- Assumed D1-D5 symmetric-product-orbifold locus package in the 2D CFT lane. -/
theorem d1_d5_symmetric_product_orbifold_locus_package
    (data : D1D5SymmetricProductOrbifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dD1D5SymmetricProductOrbifoldLocus
      (D1D5SymmetricProductOrbifoldLocusPackage data)) :
    D1D5SymmetricProductOrbifoldLocusPackage data := by
  exact h_phys

end PhysicsLogic.QFT.CFT.TwoDimensional
