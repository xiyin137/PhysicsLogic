import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Positive real power represented via logarithm/exponential. -/
noncomputable def positiveRealRationalPower (x : ℝ) (num den : ℝ) : ℝ :=
  Real.exp ((num / den) * Real.log x)

/-- Bosonic-string normalization data used in Appendix-A convention tables. -/
structure BosonicNormalizationConventionData where
  genus : ℕ
  externalStates : ℕ
  stringCoupling : ℝ
  gravitationalCoupling : ℝ
  amplitudeNormalization : ℝ
  sphereCurvatureNormalization : ℝ

/-- Bosonic normalization package:
`N_{h,n} = g_s^(n+2h-2)` and `K_{S^2} = 8π/κ^2`. -/
def BosonicNormalizationConventionPackage
    (data : BosonicNormalizationConventionData) : Prop :=
  data.stringCoupling > 0 ∧
  data.gravitationalCoupling > 0 ∧
  data.amplitudeNormalization =
    positiveRealRationalPower data.stringCoupling
      ((data.externalStates : ℝ) + 2 * (data.genus : ℝ) - 2) 1 ∧
  data.sphereCurvatureNormalization =
    8 * Real.pi / data.gravitationalCoupling ^ (2 : ℕ)

/-- Assumed bosonic normalization convention package. -/
theorem bosonic_normalization_convention_package
    (data : BosonicNormalizationConventionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConventionsBosonicNormalizationPackage
      (BosonicNormalizationConventionPackage data)) :
    BosonicNormalizationConventionPackage data := by
  exact h_phys

/-- Cross-theory string/gravitational-coupling conversion data. -/
structure GravitationalCouplingConventionData where
  alphaPrime : ℝ
  bosonicStringCoupling : ℝ
  bosonicGravitationalCoupling : ℝ
  typeIIStringCoupling : ℝ
  typeIIGravitationalCoupling : ℝ
  heteroticStringCoupling : ℝ
  heteroticGravitationalCoupling : ℝ
  heteroticYangMillsCoupling : ℝ

/-- Coupling-convention package:
bosonic `κ = 2π g_s`, type-II `κ = (π/2) g_s`, heterotic `κ = π g_s`,
and heterotic `g_YM = 2π g_s / sqrt(α') = 2κ / sqrt(α')`. -/
def GravitationalCouplingConventionPackage
    (data : GravitationalCouplingConventionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.bosonicStringCoupling > 0 ∧
  data.typeIIStringCoupling > 0 ∧
  data.heteroticStringCoupling > 0 ∧
  data.bosonicGravitationalCoupling =
    2 * Real.pi * data.bosonicStringCoupling ∧
  data.typeIIGravitationalCoupling =
    (Real.pi / 2) * data.typeIIStringCoupling ∧
  data.heteroticGravitationalCoupling =
    Real.pi * data.heteroticStringCoupling ∧
  data.heteroticYangMillsCoupling =
    2 * Real.pi * data.heteroticStringCoupling / Real.sqrt data.alphaPrime ∧
  data.heteroticYangMillsCoupling =
    2 * data.heteroticGravitationalCoupling / Real.sqrt data.alphaPrime

/-- Assumed cross-theory coupling convention package. -/
theorem gravitational_coupling_convention_package
    (data : GravitationalCouplingConventionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConventionsGravitationalCouplingRelations
      (GravitationalCouplingConventionPackage data)) :
    GravitationalCouplingConventionPackage data := by
  exact h_phys

/-- Bosonic open/closed coupling and Dp-brane tension convention data. -/
structure BosonicDbraneTensionConventionData where
  braneDimension : ℕ
  alphaPrime : ℝ
  openStringCoupling : ℝ
  closedStringCoupling : ℝ
  gravitationalCoupling : ℝ
  dbraneTension : ℝ

/-- Bosonic Dp-brane convention package:
`g_s = g_o^2`,
`T_p = 1/(2π^2 α' g_o^2)`,
and `T_p = (sqrt(π)/(16κ))(4π^2 α')^((11-p)/2)`. -/
def BosonicDbraneTensionConventionPackage
    (data : BosonicDbraneTensionConventionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.openStringCoupling > 0 ∧
  data.gravitationalCoupling > 0 ∧
  data.closedStringCoupling = data.openStringCoupling ^ (2 : ℕ) ∧
  data.dbraneTension =
    1 / (2 * Real.pi ^ (2 : ℕ) * data.alphaPrime * data.openStringCoupling ^ (2 : ℕ)) ∧
  data.dbraneTension =
    (Real.sqrt Real.pi / (16 * data.gravitationalCoupling)) *
      positiveRealRationalPower
        (4 * Real.pi ^ (2 : ℕ) * data.alphaPrime)
        (11 - (data.braneDimension : ℝ)) 2

/-- Assumed bosonic open/closed and Dp-tension convention package. -/
theorem bosonic_dbrane_tension_convention_package
    (data : BosonicDbraneTensionConventionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConventionsBosonicDpTensionRelations
      (BosonicDbraneTensionConventionPackage data)) :
    BosonicDbraneTensionConventionPackage data := by
  exact h_phys

/-- Type-II Dp-brane tension convention data. -/
structure TypeIIDbraneTensionConventionData where
  braneDimension : ℕ
  alphaPrime : ℝ
  gravitationalCoupling : ℝ
  dbraneTension : ℝ

/-- Type-II Dp-brane convention package:
`T_p = (sqrt(π)/κ)(4π^2 α')^((3-p)/2)`. -/
def TypeIIDbraneTensionConventionPackage
    (data : TypeIIDbraneTensionConventionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.gravitationalCoupling > 0 ∧
  data.dbraneTension =
    (Real.sqrt Real.pi / data.gravitationalCoupling) *
      positiveRealRationalPower
        (4 * Real.pi ^ (2 : ℕ) * data.alphaPrime)
        (3 - (data.braneDimension : ℝ)) 2

/-- Assumed type-II Dp-brane tension convention package. -/
theorem typeII_dbrane_tension_convention_package
    (data : TypeIIDbraneTensionConventionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConventionsTypeIIDpTensionRelation
      (TypeIIDbraneTensionConventionPackage data)) :
    TypeIIDbraneTensionConventionPackage data := by
  exact h_phys

/-- Type-II dimensionless-coupling conversion data. -/
structure TypeIIDimensionlessCouplingConventionData where
  alphaPrime : ℝ
  gravitationalCoupling : ℝ
  stringCoupling : ℝ
  d1Tension : ℝ
  d0Tension : ℝ
  typeIIBDimensionlessCoupling : ℝ
  typeIIADimensionlessCoupling : ℝ

/-- Type-II dimensionless-coupling package:
`g_B = 1/(2π α' T_1) = κ/(8π^(7/2) α'^2) = g_s/(16π^(5/2) α'^2)` and
`g_A = 1/(sqrt(α') T_0) = g_s/(16π^(5/2) α'^2)`. -/
def TypeIIDimensionlessCouplingConventionPackage
    (data : TypeIIDimensionlessCouplingConventionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.gravitationalCoupling > 0 ∧
  data.stringCoupling > 0 ∧
  data.d1Tension > 0 ∧
  data.d0Tension > 0 ∧
  data.typeIIBDimensionlessCoupling =
    1 / (2 * Real.pi * data.alphaPrime * data.d1Tension) ∧
  data.typeIIBDimensionlessCoupling =
    data.gravitationalCoupling /
      (8 * positiveRealRationalPower Real.pi 7 2 * data.alphaPrime ^ (2 : ℕ)) ∧
  data.typeIIBDimensionlessCoupling =
    data.stringCoupling /
      (16 * positiveRealRationalPower Real.pi 5 2 * data.alphaPrime ^ (2 : ℕ)) ∧
  data.typeIIADimensionlessCoupling =
    1 / (Real.sqrt data.alphaPrime * data.d0Tension) ∧
  data.typeIIADimensionlessCoupling =
    data.stringCoupling /
      (16 * positiveRealRationalPower Real.pi 5 2 * data.alphaPrime ^ (2 : ℕ))

/-- Assumed type-II dimensionless-coupling convention package. -/
theorem typeII_dimensionless_coupling_convention_package
    (data : TypeIIDimensionlessCouplingConventionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConventionsTypeIIDimensionlessCouplings
      (TypeIIDimensionlessCouplingConventionPackage data)) :
    TypeIIDimensionlessCouplingConventionPackage data := by
  exact h_phys

/-- M-theory Planck-scale and brane-tension convention data. -/
structure MTheoryScaleTensionConventionData where
  alphaPrime : ℝ
  stringCouplingIIA : ℝ
  gravitationalCoupling11Squared : ℝ
  planckMass11 : ℝ
  membraneTension : ℝ
  fivebraneTension : ℝ

/-- M-theory convention package:
`κ_11^2 = 2^7 π^8 α'^(9/2) g_A^3 = 2^7 π^8 M_11^(-9)`,
`T_M2 = M_11^3/(2π)^2`, and `T_M5 = M_11^6/(2π)^5`. -/
def MTheoryScaleTensionConventionPackage
    (data : MTheoryScaleTensionConventionData) : Prop :=
  data.alphaPrime > 0 ∧
  data.stringCouplingIIA > 0 ∧
  data.planckMass11 > 0 ∧
  data.gravitationalCoupling11Squared =
    (2 : ℝ) ^ (7 : ℕ) * Real.pi ^ (8 : ℕ) *
      positiveRealRationalPower data.alphaPrime 9 2 *
      data.stringCouplingIIA ^ (3 : ℕ) ∧
  data.gravitationalCoupling11Squared =
    (2 : ℝ) ^ (7 : ℕ) * Real.pi ^ (8 : ℕ) /
      data.planckMass11 ^ (9 : ℕ) ∧
  data.membraneTension =
    data.planckMass11 ^ (3 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) ∧
  data.fivebraneTension =
    data.planckMass11 ^ (6 : ℕ) / (2 * Real.pi) ^ (5 : ℕ)

/-- Assumed M-theory Planck/tension convention package. -/
theorem m_theory_scale_tension_convention_package
    (data : MTheoryScaleTensionConventionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringConventionsMTheoryScaleTensionRelations
      (MTheoryScaleTensionConventionPackage data)) :
    MTheoryScaleTensionConventionPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
