import PhysicsLogic.Assumptions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

namespace PhysicsLogic.QFT.PathIntegral

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- 2D axial-anomaly data for a massless Dirac fermion coupled to a background `U(1)` field. -/
structure TwoDAxialAnomalyData where
  axialCurrentDivergence : ℝ
  fieldStrengthDual : ℝ

/-- 2D axial anomaly relation `∂_μ j_A^μ = (1 / 2π) ε^{μν} F_{μν}` at coefficient level. -/
def TwoDAxialCurrentAnomaly (data : TwoDAxialAnomalyData) : Prop :=
  data.axialCurrentDivergence = (1 / (2 * Real.pi)) * data.fieldStrengthDual

/-- Assumed 2D axial-current anomaly relation from Appendix O. -/
theorem two_d_axial_current_anomaly
    (data : TwoDAxialAnomalyData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyAxial2dCurrentDivergence
      (TwoDAxialCurrentAnomaly data)) :
    TwoDAxialCurrentAnomaly data := by
  exact h_phys

/-- 4D axial-anomaly data for a massless Dirac fermion in a background Abelian field. -/
structure FourDAxialAnomalyData where
  axialCurrentDivergence : ℝ
  pontryaginDensity : ℝ

/-- 4D axial anomaly relation `∂_μ j_A^μ = (1 / 16π²) ε^{μνρσ} F_{μν} F_{ρσ}`. -/
def FourDAxialCurrentAnomaly (data : FourDAxialAnomalyData) : Prop :=
  data.axialCurrentDivergence =
    (1 / (16 * Real.pi ^ (2 : ℕ))) * data.pontryaginDensity

/-- Assumed 4D axial-current anomaly relation from Appendix O. -/
theorem four_d_axial_current_anomaly
    (data : FourDAxialAnomalyData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyAxial4dCurrentDivergence
      (FourDAxialCurrentAnomaly data)) :
    FourDAxialCurrentAnomaly data := by
  exact h_phys

/-- 4D `U(1)` chiral-gauge anomaly data (`δ_ζ Γ` against `ζ F∧F`). -/
structure U1ChiralGaugeAnomalyData where
  effectiveActionVariation : ℝ
  integratedZetaFF : ℝ

/-- 4D chiral `U(1)` gauge-anomaly variation relation.
`δ_ζ Γ = -(1 / 96π²) ∫ ζ ε^{μνρσ} F_{μν} F_{ρσ}`. -/
def U1ChiralGaugeVariationAnomaly (data : U1ChiralGaugeAnomalyData) : Prop :=
  data.effectiveActionVariation =
    -((1 / (96 * Real.pi ^ (2 : ℕ))) * data.integratedZetaFF)

/-- Assumed 4D chiral `U(1)` gauge-anomaly variation relation from Appendix O. -/
theorem u1_chiral_gauge_variation_anomaly
    (data : U1ChiralGaugeAnomalyData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGaugeU1ChiralVariation
      (U1ChiralGaugeVariationAnomaly data)) :
    U1ChiralGaugeVariationAnomaly data := by
  exact h_phys

/-- Multi-`U(1)` chiral-fermion charge data and cubic-anomaly coefficients. -/
structure MultiU1ChargeData (nFermions nU1 : ℕ) where
  charges : Fin nFermions → Fin nU1 → ℝ
  dCoeff : Fin nU1 → Fin nU1 → Fin nU1 → ℝ

/-- Cubic anomaly coefficients:
`d_{abc} = Σ_j q_j^{(a)} q_j^{(b)} q_j^{(c)}`. -/
def MultiU1CubicAnomalyCoefficients {nFermions nU1 : ℕ}
    (data : MultiU1ChargeData nFermions nU1) : Prop :=
  ∀ a b c : Fin nU1,
    data.dCoeff a b c =
      ∑ j : Fin nFermions, data.charges j a * data.charges j b * data.charges j c

/-- Assumed multi-`U(1)` cubic-anomaly coefficient relation from Appendix O. -/
theorem multi_u1_cubic_anomaly_coefficients
    {nFermions nU1 : ℕ}
    (data : MultiU1ChargeData nFermions nU1)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGaugeU1CubicCoefficient
      (MultiU1CubicAnomalyCoefficients data)) :
    MultiU1CubicAnomalyCoefficients data := by
  exact h_phys

/-- Counterterm-shift data for multi-`U(1)` gauge-anomaly coefficients. -/
structure MultiU1CountertermData (nU1 : ℕ) where
  baseDCoeff : Fin nU1 → Fin nU1 → Fin nU1 → ℝ
  shiftedDCoeff : Fin nU1 → Fin nU1 → Fin nU1 → ℝ
  hCoeff : Fin nU1 → Fin nU1 → Fin nU1 → ℝ

/-- Counterterm ambiguity relation:
`d'_{abc} = d_{abc} + 1/2 (h_{ab,c} + h_{ac,b})` with `h_{ab,c} = -h_{ba,c}`. -/
def MultiU1CountertermShift {nU1 : ℕ}
    (data : MultiU1CountertermData nU1) : Prop :=
  (∀ a b c : Fin nU1, data.hCoeff a b c = -data.hCoeff b a c) ∧
  (∀ a b c : Fin nU1,
    data.shiftedDCoeff a b c =
      data.baseDCoeff a b c +
        (1 / 2 : ℝ) * (data.hCoeff a b c + data.hCoeff a c b))

/-- Assumed multi-`U(1)` counterterm-shift relation from Appendix O. -/
theorem multi_u1_counterterm_shift
    {nU1 : ℕ}
    (data : MultiU1CountertermData nU1)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGaugeU1CountertermShift
      (MultiU1CountertermShift data)) :
    MultiU1CountertermShift data := by
  exact h_phys

/-- General gauge-anomaly descent data in even spacetime dimension `d`. -/
structure GaugeDescentData where
  d : ℕ
  deltaGamma : ℂ
  integralId : ℂ
  dId : ℂ
  deltaIdPlus1 : ℂ
  dIdPlus1 : ℂ
  idPlus2 : ℂ

/-- Descent relations:
`δ_ζ Γ = -∫ I_d`, `d I_d = δ_ζ I_{d+1}`, `d I_{d+1} = I_{d+2}`. -/
def GaugeDescentRelations (data : GaugeDescentData) : Prop :=
  Even data.d ∧
  data.deltaGamma = -data.integralId ∧
  data.dId = data.deltaIdPlus1 ∧
  data.dIdPlus1 = data.idPlus2

/-- Assumed gauge-anomaly descent relations from Appendix O. -/
theorem gauge_descent_relations
    (data : GaugeDescentData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGaugeDescentRelations
      (GaugeDescentRelations data)) :
    GaugeDescentRelations data := by
  exact h_phys

/-- Chiral-fermion gauge-anomaly-polynomial data in even spacetime dimension `d`. -/
structure ChiralFermionGaugeAnomalyPolynomialData where
  d : ℕ
  anomalyPolynomial : ℂ
  tracePower : ℂ

/-- Anomaly-polynomial relation for a Weyl fermion in representation `R`:
`I_{d+2} = 1 / (((d+2)/2)! (2π)^{d/2}) * tr_R(F^{(d+2)/2})`. -/
def ChiralFermionGaugeAnomalyPolynomial
    (data : ChiralFermionGaugeAnomalyPolynomialData) : Prop :=
  Even data.d ∧
  data.anomalyPolynomial =
    (1 /
      ((Nat.factorial ((data.d + 2) / 2) : ℂ) *
        ((2 * Real.pi : ℂ) ^ (data.d / 2)))) *
      data.tracePower

/-- Assumed chiral-fermion gauge-anomaly-polynomial relation from Appendix O. -/
theorem chiral_fermion_gauge_anomaly_polynomial
    (data : ChiralFermionGaugeAnomalyPolynomialData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGaugeChiralFermionPolynomial
      (ChiralFermionGaugeAnomalyPolynomial data)) :
    ChiralFermionGaugeAnomalyPolynomial data := by
  exact h_phys

/-- Gravitational-anomaly descent data in `d = 4k+2` dimensions. -/
structure GravitationalDescentData where
  k : ℕ
  dimension : ℕ
  dI4k2 : ℂ
  deltaI4k3 : ℂ
  dI4k3 : ℂ
  i4k4 : ℂ

/-- Gravitational descent relations in `d = 4k+2` dimensions. -/
def GravitationalDescentRelations (data : GravitationalDescentData) : Prop :=
  data.dimension = 4 * data.k + 2 ∧
  data.dI4k2 = data.deltaI4k3 ∧
  data.dI4k3 = data.i4k4

/-- Assumed gravitational-anomaly descent relations from Appendix O. -/
theorem gravitational_descent_relations
    (data : GravitationalDescentData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGravitationalDescent4kPlus2
      (GravitationalDescentRelations data)) :
    GravitationalDescentRelations data := by
  exact h_phys

/-- Gravitational-anomaly-polynomial data for a complex Weyl fermion in `d = 4k+2`. -/
structure GravitationalAnomalyPolynomialData where
  k : ℕ
  anomalyPolynomial : ℂ
  ahatTopFormComponent : ℂ

/-- Gravitational anomaly-polynomial relation:
`I_{4k+4} = -(2π)^{-(2k+1)} [det((R/2)/sinh(R/2))]^{1/2}|_{R^{2k+2}}`. -/
def GravitationalAnomalyPolynomial
    (data : GravitationalAnomalyPolynomialData) : Prop :=
  data.anomalyPolynomial =
    -((1 / ((2 * Real.pi : ℂ) ^ (2 * data.k + 1))) * data.ahatTopFormComponent)

/-- Assumed gravitational anomaly-polynomial relation from Appendix O. -/
theorem gravitational_anomaly_polynomial
    (data : GravitationalAnomalyPolynomialData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGravitationalAhatPolynomial
      (GravitationalAnomalyPolynomial data)) :
    GravitationalAnomalyPolynomial data := by
  exact h_phys

/-- Explicit 10D Majorana-Weyl gravitational anomaly-polynomial coefficient data. -/
structure D10MajoranaWeylAnomalyData where
  anomalyPolynomial : ℂ
  trR6 : ℂ
  trR4trR2 : ℂ
  trR2cubed : ℂ

/-- 10D Majorana-Weyl anomaly-polynomial coefficient package from Appendix O. -/
def D10MajoranaWeylAnomalyPolynomial
    (data : D10MajoranaWeylAnomalyData) : Prop :=
  data.anomalyPolynomial =
    (1 / ((2 * Real.pi : ℂ) ^ (5 : ℕ))) *
      ((1 / (725760 : ℂ)) * data.trR6 +
        (1 / (552960 : ℂ)) * data.trR4trR2 +
        (1 / (1327104 : ℂ)) * data.trR2cubed)

/-- Assumed explicit 10D Majorana-Weyl gravitational anomaly-polynomial coefficients. -/
theorem d10_majorana_weyl_anomaly_polynomial
    (data : D10MajoranaWeylAnomalyData)
    (h_phys : PhysicsAssumption
      AssumptionId.qftAnomalyGravitationalD10MwPolynomial
      (D10MajoranaWeylAnomalyPolynomial data)) :
    D10MajoranaWeylAnomalyPolynomial data := by
  exact h_phys

end PhysicsLogic.QFT.PathIntegral
