import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.Units

set_option autoImplicit false

/-- Dimensionful scalar quantity.

This is intentionally lightweight: it prevents direct `: ℝ` declarations for
unit-bearing interfaces while still allowing arithmetic-heavy interface formulas. -/
structure Dimful where
  value : ℝ
deriving Inhabited

namespace Dimful

instance : Coe Dimful ℝ := ⟨Dimful.value⟩
instance : CoeTC ℝ Dimful := ⟨fun r => ⟨r⟩⟩

instance : Zero Dimful := ⟨⟨0⟩⟩
instance : One Dimful := ⟨⟨1⟩⟩
instance instOfNat (n : Nat) : OfNat Dimful n := ⟨⟨n⟩⟩
instance : Neg Dimful := ⟨fun q => ⟨-q.value⟩⟩
instance : Add Dimful := ⟨fun q1 q2 => ⟨q1.value + q2.value⟩⟩
instance : Sub Dimful := ⟨fun q1 q2 => ⟨q1.value - q2.value⟩⟩
instance : Mul Dimful := ⟨fun q1 q2 => ⟨q1.value * q2.value⟩⟩
noncomputable instance : Div Dimful := ⟨fun q1 q2 => ⟨q1.value / q2.value⟩⟩
instance : Pow Dimful Nat := ⟨fun q n => ⟨q.value ^ n⟩⟩
instance : LT Dimful := ⟨fun q1 q2 => q1.value < q2.value⟩
instance : LE Dimful := ⟨fun q1 q2 => q1.value ≤ q2.value⟩

@[simp] lemma value_zero : (0 : Dimful).value = 0 := by
  simp [OfNat.ofNat]
@[simp] lemma value_one : (1 : Dimful).value = 1 := by
  simp [OfNat.ofNat]
@[simp] lemma value_add (q1 q2 : Dimful) : (q1 + q2).value = q1.value + q2.value := rfl
@[simp] lemma value_sub (q1 q2 : Dimful) : (q1 - q2).value = q1.value - q2.value := rfl
@[simp] lemma value_mul (q1 q2 : Dimful) : (q1 * q2).value = q1.value * q2.value := rfl
@[simp] lemma value_div (q1 q2 : Dimful) : (q1 / q2).value = q1.value / q2.value := rfl
@[simp] lemma value_pow (q : Dimful) (n : Nat) : (q ^ n).value = q.value ^ n := rfl

end Dimful

/-- Dimensionless scalar quantity (kept distinct from raw `ℝ` for interface clarity). -/
abbrev Dimless := Dimful

/-- Scaling/conformal dimensions are dimensionless real exponents. -/
abbrev ScalingDimension := ℝ
/-- Picture number in NSR superstring quantization (typically integral or half-integral). -/
abbrev PictureNumber := ℚ
abbrev DimensionlessCoupling := ℝ
abbrev DimensionlessMomentum := ℝ
abbrev DimensionlessEnergy := ℝ
abbrev Rapidity := ℝ
abbrev Angle := ℝ
abbrev ThetaAngle := Angle
abbrev ProbabilityWeight := ℝ
abbrev WavefunctionRenormalization := ScalingDimension
abbrev ConformalWeight := ScalingDimension
abbrev OPECoefficient := ScalingDimension
abbrev CentralCharge := ScalingDimension
abbrev FluxQuantum := ScalingDimension
abbrev VelocitySquared := ScalingDimension
abbrev BetaFunctionValue := ScalingDimension
abbrev ComplexDimensionless := ℂ
abbrev ComplexCoupling := ComplexDimensionless
abbrev ComplexMomentumSquaredInvariant := ComplexDimensionless
abbrev ComplexMassSquaredInvariant := ComplexDimensionless
abbrev ComplexEnergy := ComplexDimensionless
abbrev ComplexRapidity := ComplexDimensionless
abbrev ComplexSpectralParameter := ComplexDimensionless
abbrev ComplexAmplitude := ComplexDimensionless
abbrev ComplexActionValue := ComplexDimensionless
abbrev ComplexChemicalPotential := ComplexDimensionless
abbrev SpinorMomentumContraction := ComplexDimensionless

/-- Named aliases used across the repository for unit-bearing fields. -/
abbrev InvariantMass := Dimful
abbrev MassScale := Dimful
abbrev MassSquaredScale := Dimful
abbrev MomentumSquaredScale := Dimful
abbrev Energy := Dimful
abbrev MomentumNorm := Dimful
abbrev LengthScale := Dimful
abbrev TimeScale := Dimful
abbrev FrequencyScale := Dimful
abbrev SurfaceGravityScale := FrequencyScale
abbrev CurvatureScale := Dimful
abbrev CosmologicalConstantScale := CurvatureScale
abbrev TemperatureScale := Dimful
abbrev InverseTemperatureScale := TimeScale
abbrev AreaScale := Dimful
abbrev VolumeScale := Dimful
abbrev ChargeScale := Dimful
abbrev DensityScale := Dimful
abbrev ChargeDensityScale := Dimful
abbrev PotentialScale := Dimful
abbrev EntropyMeasure := ℝ
abbrev ElectricFieldScale := Dimful
abbrev ActionScale := Dimful
abbrev TensionScale := Dimful
abbrev SpeedScale := Dimful
abbrev CouplingScale := Dimful
abbrev GravitationalCouplingScale := CouplingScale
abbrev StringLength := Dimful
abbrev StringSlope := Dimful

/-- Legacy compatibility alias; prefer `MassScale` for generic mass-dimension parameters. -/
abbrev PlanckMass := MassScale

/-- Unit-system data for commonly used conventions. -/
structure UnitSystem where
  speedOfLight : SpeedScale
  reducedPlanckConstant : ActionScale

/-- SI calibration (numerical values in SI base units). -/
noncomputable def siUnitSystem : UnitSystem where
  speedOfLight := (299792458 : Dimful)
  reducedPlanckConstant := (((1054571817 : ℝ) / (10 : ℝ) ^ (43 : Nat)) : Dimful)

/-- Natural-unit calibration used widely in HET (`c = ħ = 1`). -/
def naturalUnitSystem : UnitSystem where
  speedOfLight := (1 : Dimful)
  reducedPlanckConstant := (1 : Dimful)

/-- Marker class for systems calibrated to natural units. -/
class IsNaturalUnits (U : UnitSystem) : Prop where
  speedOfLight_eq_one : U.speedOfLight.value = 1
  reducedPlanck_eq_one : U.reducedPlanckConstant.value = 1

instance : IsNaturalUnits naturalUnitSystem where
  speedOfLight_eq_one := by
    simp [naturalUnitSystem, OfNat.ofNat]
  reducedPlanck_eq_one := by
    simp [naturalUnitSystem, OfNat.ofNat]

/-- Invariant-mass shell relation in `c = 1` normalization:
`E^2 = p^2 + m^2`, where `m` is invariant/rest mass. -/
def InvariantMassShell
    (energy : Energy) (momentumNorm : MomentumNorm) (mass : InvariantMass) : Prop :=
  energy.value ^ (2 : ℕ) = momentumNorm.value ^ (2 : ℕ) + mass.value ^ (2 : ℕ)

/-- Invariant-mass shell relation with explicit light speed `c`:
`E^2 = p^2 c^2 + m^2 c^4`. -/
def InvariantMassShellWithC
    (energy : Energy) (momentumNorm : MomentumNorm)
    (mass : InvariantMass) (c : SpeedScale) : Prop :=
  energy.value ^ (2 : ℕ) =
    momentumNorm.value ^ (2 : ℕ) * c.value ^ (2 : ℕ) +
      mass.value ^ (2 : ℕ) * c.value ^ (4 : ℕ)

/-- Positive-energy branch of the invariant-mass shell in natural units:
`E = sqrt(p^2 + m^2)` with `m` interpreted as invariant mass. -/
def PositiveBranchInvariantMassShell
    (energy : Energy) (momentumNorm : MomentumNorm) (mass : InvariantMass) : Prop :=
  energy.value = Real.sqrt (momentumNorm.value ^ (2 : ℕ) + mass.value ^ (2 : ℕ))

end PhysicsLogic.Units

namespace PhysicsLogic

abbrev Dimful := Units.Dimful
abbrev Dimless := Units.Dimless
abbrev ScalingDimension := Units.ScalingDimension
abbrev PictureNumber := Units.PictureNumber
abbrev DimensionlessCoupling := Units.DimensionlessCoupling
abbrev DimensionlessMomentum := Units.DimensionlessMomentum
abbrev DimensionlessEnergy := Units.DimensionlessEnergy
abbrev Rapidity := Units.Rapidity
abbrev Angle := Units.Angle
abbrev ThetaAngle := Units.ThetaAngle
abbrev ProbabilityWeight := Units.ProbabilityWeight
abbrev WavefunctionRenormalization := Units.WavefunctionRenormalization
abbrev ConformalWeight := Units.ConformalWeight
abbrev OPECoefficient := Units.OPECoefficient
abbrev CentralCharge := Units.CentralCharge
abbrev FluxQuantum := Units.FluxQuantum
abbrev VelocitySquared := Units.VelocitySquared
abbrev BetaFunctionValue := Units.BetaFunctionValue
abbrev ComplexDimensionless := Units.ComplexDimensionless
abbrev ComplexCoupling := Units.ComplexCoupling
abbrev ComplexMomentumSquaredInvariant := Units.ComplexMomentumSquaredInvariant
abbrev ComplexMassSquaredInvariant := Units.ComplexMassSquaredInvariant
abbrev ComplexEnergy := Units.ComplexEnergy
abbrev ComplexRapidity := Units.ComplexRapidity
abbrev ComplexSpectralParameter := Units.ComplexSpectralParameter
abbrev ComplexAmplitude := Units.ComplexAmplitude
abbrev ComplexActionValue := Units.ComplexActionValue
abbrev ComplexChemicalPotential := Units.ComplexChemicalPotential
abbrev SpinorMomentumContraction := Units.SpinorMomentumContraction
abbrev InvariantMass := Units.InvariantMass
abbrev MassScale := Units.MassScale
abbrev MassSquaredScale := Units.MassSquaredScale
abbrev MomentumSquaredScale := Units.MomentumSquaredScale
abbrev Energy := Units.Energy
abbrev MomentumNorm := Units.MomentumNorm
abbrev LengthScale := Units.LengthScale
abbrev TimeScale := Units.TimeScale
abbrev FrequencyScale := Units.FrequencyScale
abbrev SurfaceGravityScale := Units.SurfaceGravityScale
abbrev CurvatureScale := Units.CurvatureScale
abbrev CosmologicalConstantScale := Units.CosmologicalConstantScale
abbrev TemperatureScale := Units.TemperatureScale
abbrev InverseTemperatureScale := Units.InverseTemperatureScale
abbrev AreaScale := Units.AreaScale
abbrev VolumeScale := Units.VolumeScale
abbrev ChargeScale := Units.ChargeScale
abbrev DensityScale := Units.DensityScale
abbrev ChargeDensityScale := Units.ChargeDensityScale
abbrev PotentialScale := Units.PotentialScale
abbrev EntropyMeasure := Units.EntropyMeasure
abbrev ElectricFieldScale := Units.ElectricFieldScale
abbrev ActionScale := Units.ActionScale
abbrev TensionScale := Units.TensionScale
abbrev SpeedScale := Units.SpeedScale
abbrev CouplingScale := Units.CouplingScale
abbrev GravitationalCouplingScale := Units.GravitationalCouplingScale
abbrev StringLength := Units.StringLength
abbrev StringSlope := Units.StringSlope

/-- Legacy compatibility alias; prefer `MassScale` for generic mass-dimension parameters. -/
abbrev PlanckMass := Units.MassScale

abbrev UnitSystem := Units.UnitSystem
abbrev IsNaturalUnits := Units.IsNaturalUnits

noncomputable abbrev siUnitSystem := Units.siUnitSystem
abbrev naturalUnitSystem := Units.naturalUnitSystem

abbrev InvariantMassShell := Units.InvariantMassShell
abbrev InvariantMassShellWithC := Units.InvariantMassShellWithC
abbrev PositiveBranchInvariantMassShell := Units.PositiveBranchInvariantMassShell

end PhysicsLogic
