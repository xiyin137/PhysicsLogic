import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev WilsonConfinementClaim := Prop

/-- Maldacena-Wilson loop saddle-point data at strong coupling. -/
structure MaldacenaWilsonLoopSaddleData where
  adsRadius : LengthScale
  alphaPrime : StringSlope
  cutoff : LengthScale
  contourLength : LengthScale
  WorldsheetConfiguration : Type
  saddleConfiguration : WorldsheetConfiguration
  worldsheetActionFunctional : WorldsheetConfiguration → ComplexActionValue
  expectationValue : ComplexAmplitude

/-- Regulated holographic Wilson-loop saddle package:
`W(C) ~ exp(-(S - (R/(2π α' ε))|C|))`. -/
def MaldacenaWilsonLoopSaddlePackage
    (data : MaldacenaWilsonLoopSaddleData) : Prop :=
  data.adsRadius > 0 ∧
  data.alphaPrime > 0 ∧
  data.cutoff > 0 ∧
  data.contourLength ≥ 0 ∧
  data.expectationValue =
    Complex.exp
      (-(data.worldsheetActionFunctional data.saddleConfiguration -
        (((data.adsRadius / (2 * Real.pi * data.alphaPrime * data.cutoff)) *
            data.contourLength : LengthScale) : ℂ)))

/-- Assumed strong-coupling saddle package for Maldacena-Wilson loops. -/
theorem maldacena_wilson_loop_saddle_package
    (data : MaldacenaWilsonLoopSaddleData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringWilsonMaldacenaLoopSaddle
      (MaldacenaWilsonLoopSaddlePackage data)) :
    MaldacenaWilsonLoopSaddlePackage data := by
  exact h_phys

/-- Rectangular-loop quark-antiquark potential data in AdS5/CFT4. -/
structure RectangularWilsonPotentialData where
  tHooftCoupling : DimensionlessCoupling
  separation : LengthScale
  gammaQuarter : Dimless
  potential : Energy

/-- Strong-coupling rectangular-loop potential package:
`V(L) = -(4π sqrt(λ))/((Gamma(1/4))^4 L)` represented via `gammaQuarter`. -/
def RectangularWilsonPotentialPackage
    (data : RectangularWilsonPotentialData) : Prop :=
  data.tHooftCoupling > 0 ∧
  data.separation > 0 ∧
  data.gammaQuarter > 0 ∧
  data.potential =
    -(4 * Real.pi * Real.sqrt data.tHooftCoupling) /
      (data.gammaQuarter ^ (4 : ℕ) * data.separation)

/-- Assumed strong-coupling quark-antiquark potential package. -/
theorem rectangular_wilson_potential_package
    (data : RectangularWilsonPotentialData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringWilsonQuarkAntiquarkPotentialStrongCoupling
      (RectangularWilsonPotentialPackage data)) :
    RectangularWilsonPotentialPackage data := by
  exact h_phys

/-- Cuspy Wilson-line data in the large Lorentzian-angle regime. -/
structure CuspLargeAngleData where
  tHooftCoupling : DimensionlessCoupling
  lorentzianAngle : Angle
  cuspAnomalousDimension : ScalingDimension
  cuspyLineDimension : ScalingDimension

/-- Large-angle cusp package:
`Gamma_cusp = sqrt(λ)/(2π)` and
`Delta_cusp(π-iC) = (1/2) Gamma_cusp C`. -/
def CuspLargeAnglePackage (data : CuspLargeAngleData) : Prop :=
  data.tHooftCoupling > 0 ∧
  data.lorentzianAngle > 0 ∧
  data.cuspAnomalousDimension =
    Real.sqrt data.tHooftCoupling / (2 * Real.pi) ∧
  data.cuspyLineDimension =
    (1 / 2 : ℝ) * data.cuspAnomalousDimension * data.lorentzianAngle

/-- Assumed large-angle cusp/Wilson-line relation package. -/
theorem cusp_large_angle_package
    (data : CuspLargeAngleData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringWilsonCuspLargeAngleRelation
      (CuspLargeAnglePackage data)) :
    CuspLargeAnglePackage data := by
  exact h_phys

/-- Bremsstrahlung-function data for small-angle cusps and radiation. -/
structure BremsstrahlungFunctionData where
  tHooftCoupling : DimensionlessCoupling
  rankN : ℕ
  smallDeflectionAngle : Angle
  bremsstrahlungFunction : ScalingDimension
  cuspAnomalousDimension : ScalingDimension
  radiationCoefficient : ScalingDimension
  modifiedBesselI : ℕ → ℝ → ℝ

/-- Bremsstrahlung package:
small-angle cusp law, `A = 2π B`, and planar localization formula for `B(λ,N)`. -/
def BremsstrahlungFunctionPackage
    (data : BremsstrahlungFunctionData) : Prop :=
  data.tHooftCoupling > 0 ∧
  data.rankN > 0 ∧
  data.smallDeflectionAngle ≥ 0 ∧
  data.modifiedBesselI 1 (Real.sqrt data.tHooftCoupling) ≠ 0 ∧
  data.bremsstrahlungFunction =
    (Real.sqrt data.tHooftCoupling / (4 * Real.pi ^ (2 : ℕ))) *
      (data.modifiedBesselI 2 (Real.sqrt data.tHooftCoupling) /
        data.modifiedBesselI 1 (Real.sqrt data.tHooftCoupling)) ∧
  data.cuspAnomalousDimension =
    -data.bremsstrahlungFunction * data.smallDeflectionAngle ^ (2 : ℕ) ∧
  data.radiationCoefficient = 2 * Real.pi * data.bremsstrahlungFunction

/-- Assumed bremsstrahlung-function package from cusp/radiation/localization matching. -/
theorem bremsstrahlung_function_package
    (data : BremsstrahlungFunctionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringWilsonBremsstrahlungFunction
      (BremsstrahlungFunctionPackage data)) :
    BremsstrahlungFunctionPackage data := by
  exact h_phys

/-- Witten D4-circle compactification data for holographic confinement. -/
structure WittenCompactificationData where
  adsScale : LengthScale
  capRadius : LengthScale
  circleLength : LengthScale
  gaugeCoupling5d : CouplingScale
  gaugeCoupling4d : DimensionlessCoupling
  kkMass : InvariantMass
  fermionsAreAntiperiodicOnCircle : WilsonConfinementClaim

/-- Witten compactification package:
`L=(4π/3) R^(3/2) r0^(-1/2)`, `g4=g5/sqrt(L)`, `M_KK=2π/L`,
and anti-periodic fermions on the `y`-circle. -/
def WittenCompactificationPackage
    (data : WittenCompactificationData) : Prop :=
  data.adsScale > 0 ∧
  data.capRadius > 0 ∧
  data.circleLength > 0 ∧
  data.circleLength =
    (4 * Real.pi / 3) * data.adsScale * Real.sqrt data.adsScale / Real.sqrt data.capRadius ∧
  data.gaugeCoupling4d = data.gaugeCoupling5d / Real.sqrt data.circleLength ∧
  data.kkMass = 2 * Real.pi / data.circleLength ∧
  data.fermionsAreAntiperiodicOnCircle

/-- Assumed Witten compactification package for the confinement model. -/
theorem witten_compactification_package
    (data : WittenCompactificationData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringWittenConfinementCircleData
      (WittenCompactificationPackage data)) :
    WittenCompactificationPackage data := by
  exact h_phys

/-- Confining-string data in Witten's holographic model. -/
structure WittenConfiningStringData where
  alphaPrime : StringSlope
  capRadius : LengthScale
  adsScale : LengthScale
  separation : LengthScale
  quarkPotential : Energy
  stringTension : TensionScale
  gaugeCoupling4d : DimensionlessCoupling
  rankN : ℕ
  kkMass : InvariantMass

/-- Witten-model confining-string package:
linear potential `V(l)=T l` and the tension relations from the background data. -/
def WittenConfiningStringPackage
    (data : WittenConfiningStringData) : Prop :=
  data.alphaPrime > 0 ∧
  data.capRadius > 0 ∧
  data.adsScale > 0 ∧
  data.separation ≥ 0 ∧
  data.stringTension =
    (1 / (2 * Real.pi * data.alphaPrime)) *
      (data.capRadius / data.adsScale) *
      Real.sqrt (data.capRadius / data.adsScale) ∧
  data.quarkPotential = data.stringTension * data.separation ∧
  data.stringTension =
    (2 * data.gaugeCoupling4d ^ (2 : ℕ) * (data.rankN : ℝ) / (27 * Real.pi)) *
      data.kkMass ^ (2 : ℕ)

/-- Assumed confining-string package in Witten's holographic model. -/
theorem witten_confining_string_package
    (data : WittenConfiningStringData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringWittenConfiningStringTension
      (WittenConfiningStringPackage data)) :
    WittenConfiningStringPackage data := by
  exact h_phys

/-- D8-holonomy data encoding chiral flavor action in Sakai-Sugimoto. -/
structure D8HolonomyChiralData (G : Type*) where
  holonomy : G
  leftBoundaryElement : G
  rightBoundaryElement : G
  transformedHolonomy : G
  hasDiagonalUNfUnbrokenSubgroup : WilsonConfinementClaim

/-- Sakai-Sugimoto chiral package:
`U -> g_+ U g_-^{-1}` and diagonal `U(N_f)` unbroken subgroup tag. -/
def D8HolonomyChiralPackage {G : Type*} [Group G]
    (data : D8HolonomyChiralData G) : Prop :=
  data.transformedHolonomy =
    data.leftBoundaryElement * data.holonomy * data.rightBoundaryElement⁻¹ ∧
  data.hasDiagonalUNfUnbrokenSubgroup

/-- Assumed Sakai-Sugimoto chiral-symmetry breaking package. -/
theorem d8_holonomy_chiral_package
    {G : Type*} [Group G]
    (data : D8HolonomyChiralData G)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSakaiSugimotoChiralSymmetryBreaking
      (D8HolonomyChiralPackage data)) :
    D8HolonomyChiralPackage data := by
  exact h_phys

/-- Pion/Skyrme effective-action coefficient data in Sakai-Sugimoto. -/
structure SakaiSugimotoPionActionData where
  capRadius : LengthScale
  adsScale : LengthScale
  skyrmeBCoefficient : Dimless
  effectivePrefactor : Dimless
  skyrmeA : MassSquaredScale
  skyrmeB : Dimless
  pionDecayConstant : InvariantMass
  kineticCoefficient : MassSquaredScale

/-- Sakai-Sugimoto pion-action package:
`A = 9 r0/(4π)`, `B = c_B R^3` with model-dependent positive `c_B`,
and `kineticCoeff = (1/4) f_pi^2 = prefactor * A`. -/
def SakaiSugimotoPionActionPackage
    (data : SakaiSugimotoPionActionData) : Prop :=
  data.capRadius > 0 ∧
  data.adsScale > 0 ∧
  data.skyrmeBCoefficient > 0 ∧
  data.skyrmeA.value = 9 * data.capRadius.value / (4 * Real.pi) ∧
  data.skyrmeB.value = data.skyrmeBCoefficient.value * data.adsScale.value ^ (3 : ℕ) ∧
  data.kineticCoefficient.value = data.effectivePrefactor.value * data.skyrmeA.value ∧
  data.kineticCoefficient = (1 / 4 : ℝ) * data.pionDecayConstant ^ (2 : ℕ)

/-- Assumed Sakai-Sugimoto pion/Skyrme effective-action package. -/
theorem sakai_sugimoto_pion_action_package
    (data : SakaiSugimotoPionActionData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSakaiSugimotoPionSkyrmeAction
      (SakaiSugimotoPionActionPackage data)) :
    SakaiSugimotoPionActionPackage data := by
  exact h_phys

/-- Eta-prime mass data in Sakai-Sugimoto holographic QCD. -/
structure SakaiSugimotoEtaPrimeMassData where
  tHooftAtMkk : DimensionlessCoupling
  rankN : ℕ
  flavorCount : ℕ
  kkMass : InvariantMass
  etaPrimeMassSq : MassSquaredScale

/-- Sakai-Sugimoto eta-prime package:
`m_eta'^2 = (lambda(M_KK)^2/(216 π^2)) (N_f/N) M_KK^2`. -/
def SakaiSugimotoEtaPrimeMassPackage
    (data : SakaiSugimotoEtaPrimeMassData) : Prop :=
  data.tHooftAtMkk > 0 ∧
  data.rankN > 0 ∧
  data.flavorCount > 0 ∧
  data.kkMass > 0 ∧
  data.etaPrimeMassSq =
    (data.tHooftAtMkk ^ (2 : ℕ) / (216 * Real.pi ^ (2 : ℕ))) *
      ((data.flavorCount : ℝ) / (data.rankN : ℝ)) *
      data.kkMass ^ (2 : ℕ)

/-- Assumed Sakai-Sugimoto eta-prime mass package. -/
theorem sakai_sugimoto_eta_prime_mass_package
    (data : SakaiSugimotoEtaPrimeMassData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSakaiSugimotoEtaPrimeMass
      (SakaiSugimotoEtaPrimeMassPackage data)) :
    SakaiSugimotoEtaPrimeMassPackage data := by
  exact h_phys

/-- Low-lying scalar/vector meson data from D8 fluctuation spectra. -/
structure SakaiSugimotoMesonSpectrumData where
  kkMass : InvariantMass
  scalarMass1Ratio : Dimless
  scalarMass2Ratio : Dimless
  vectorMass1Ratio : Dimless
  vectorMass2Ratio : Dimless
  scalarMass1 : InvariantMass
  scalarMass2 : InvariantMass
  vectorMass1 : InvariantMass
  vectorMass2 : InvariantMass

/-- Sakai-Sugimoto meson-spectrum package:
masses are tied to `M_KK` by dimensionless ratio inputs. -/
def SakaiSugimotoMesonSpectrumPackage
    (data : SakaiSugimotoMesonSpectrumData) : Prop :=
  data.kkMass > 0 ∧
  data.scalarMass1Ratio > 0 ∧
  data.scalarMass2Ratio > 0 ∧
  data.vectorMass1Ratio > 0 ∧
  data.vectorMass2Ratio > 0 ∧
  data.scalarMass1.value = data.scalarMass1Ratio.value * data.kkMass.value ∧
  data.scalarMass2.value = data.scalarMass2Ratio.value * data.kkMass.value ∧
  data.vectorMass1.value = data.vectorMass1Ratio.value * data.kkMass.value ∧
  data.vectorMass2.value = data.vectorMass2Ratio.value * data.kkMass.value

/-- Assumed Sakai-Sugimoto hadron-spectrum package. -/
theorem sakai_sugimoto_meson_spectrum_package
    (data : SakaiSugimotoMesonSpectrumData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSakaiSugimotoMesonSpectrum
      (SakaiSugimotoMesonSpectrumPackage data)) :
    SakaiSugimotoMesonSpectrumPackage data := by
  exact h_phys

/-- Klebanov-Witten SCFT fixed-point data on the conifold branch. -/
structure KlebanovWittenConifoldData where
  anomalousDimensionAB : ScalingDimension
  operatorScalingDimension : ScalingDimension
  superpotentialRCharge : ScalingDimension
  superpotentialScalingDimension : ScalingDimension
  liesOnKlebanovWittenExactlyMarginalFamily : WilsonConfinementClaim

/-- Klebanov-Witten fixed-point package:
`gamma_AB = -1/2`, quartic chiral operator dimension `3`, and exact marginality. -/
def KlebanovWittenConifoldPackage
    (data : KlebanovWittenConifoldData) : Prop :=
  data.anomalousDimensionAB = -(1 / 2 : ℝ) ∧
  data.operatorScalingDimension = 3 ∧
  data.superpotentialRCharge = 2 ∧
  data.superpotentialScalingDimension = 3 ∧
  data.liesOnKlebanovWittenExactlyMarginalFamily

/-- Assumed Klebanov-Witten conifold fixed-point package. -/
theorem klebanov_witten_conifold_package
    (data : KlebanovWittenConifoldData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringKlebanovWittenMarginalConifoldData
      (KlebanovWittenConifoldPackage data)) :
    KlebanovWittenConifoldPackage data := by
  exact h_phys

/-- AdS5 x T^{1,1} dual-geometry data for Klebanov-Witten theory. -/
structure KlebanovWittenAdSDualData where
  volumeT11 : Dimless
  stringCoupling : DimensionlessCoupling
  rankN : ℕ
  alphaPrime : StringSlope
  adsRadius : LengthScale

/-- Klebanov-Witten AdS dual package:
`vol(T11)=16π^3/27` and
`R^4 = 4π g_s N α'^2 π^3/vol(T11)`. -/
def KlebanovWittenAdSDualPackage
    (data : KlebanovWittenAdSDualData) : Prop :=
  data.volumeT11.value = (16 / 27 : ℝ) * Real.pi ^ (3 : ℕ) ∧
  data.stringCoupling > 0 ∧
  data.alphaPrime > 0 ∧
  data.adsRadius ^ (4 : ℕ) =
    4 * Real.pi * data.stringCoupling * (data.rankN : ℝ) *
      data.alphaPrime ^ (2 : ℕ) *
      (Real.pi ^ (3 : ℕ) / data.volumeT11.value)

/-- Assumed AdS5 x T^{1,1} geometric dictionary package. -/
theorem klebanov_witten_ads_dual_package
    (data : KlebanovWittenAdSDualData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringKlebanovWittenAdS5T11Duality
      (KlebanovWittenAdSDualPackage data)) :
    KlebanovWittenAdSDualPackage data := by
  exact h_phys

/-- Klebanov-Tseytlin logarithmic effective-rank running data. -/
structure KlebanovTseytlinRunningData where
  rankN : ℕ
  fluxM : FluxQuantum
  stringCoupling : DimensionlessCoupling
  radialScale : LengthScale
  referenceScale : LengthScale
  effectiveRank : ScalingDimension

/-- KT running package:
`N_eff = N + (3/(2π)) g_s M^2 log(r/r0)`. -/
def KlebanovTseytlinRunningPackage
    (data : KlebanovTseytlinRunningData) : Prop :=
  data.referenceScale > 0 ∧
  data.radialScale > 0 ∧
  data.effectiveRank =
    (data.rankN : ℝ) +
      (3 / (2 * Real.pi)) * data.stringCoupling * data.fluxM ^ (2 : ℕ) *
        Real.log (data.radialScale / data.referenceScale)

/-- Assumed Klebanov-Tseytlin effective-rank running package. -/
theorem klebanov_tseytlin_running_package
    (data : KlebanovTseytlinRunningData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringKlebanovTseytlinFluxRunning
      (KlebanovTseytlinRunningPackage data)) :
    KlebanovTseytlinRunningPackage data := by
  exact h_phys

/-- One cascade step of Seiberg-dual rank flow in conifold gauge theories. -/
structure CascadeSeibergDualStepData where
  initialLargeRank : ℕ
  initialSmallRank : ℕ
  rankShift : ℕ
  uvTheoryHasRankPairNplusMAndN : WilsonConfinementClaim
  irTheoryHasRankPairNAndNminusM : WilsonConfinementClaim

/-- Cascade-step package:
rank map `(N+M,N) -> (N,N-M)` with `N>M`, encoded at label/rank level. -/
def CascadeSeibergDualStepPackage
    (data : CascadeSeibergDualStepData) : Prop :=
  data.rankShift > 0 ∧
  data.initialSmallRank > data.rankShift ∧
  data.initialLargeRank = data.initialSmallRank + data.rankShift ∧
  data.uvTheoryHasRankPairNplusMAndN ∧
  data.irTheoryHasRankPairNAndNminusM

/-- Assumed Seiberg-dual step package for the RG cascade. -/
theorem cascade_seiberg_dual_step_package
    (data : CascadeSeibergDualStepData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringKlebanovCascadeSeibergDualStep
      (CascadeSeibergDualStepPackage data)) :
    CascadeSeibergDualStepPackage data := by
  exact h_phys

/-- Warped-deformed-conifold confinement-scale data. -/
structure KlebanovStrasslerConfinementData where
  warpFactorAtTip : Dimless
  alphaPrime : StringSlope
  tipRadius : LengthScale
  tension : TensionScale
  kkMass : InvariantMass
  a0 : Dimless
  stringCoupling : DimensionlessCoupling
  fluxM : FluxQuantum
  kkMassToTensionFactor : Dimless

/-- KS confinement package:
`T = (1/(2π α')) H(0)^(-1/2)`,
`M_KK = H(0)^(-1/4) R0^{-1}`,
and the proportionality `M_KK^2 = c * T` with quoted coefficient `c`. -/
def KlebanovStrasslerConfinementPackage
    (data : KlebanovStrasslerConfinementData) : Prop :=
  data.warpFactorAtTip > 0 ∧
  data.alphaPrime > 0 ∧
  data.tipRadius > 0 ∧
  data.a0 > 0 ∧
  data.stringCoupling > 0 ∧
  data.fluxM > 0 ∧
  data.tension =
    (1 / (2 * Real.pi * data.alphaPrime)) * (1 / Real.sqrt data.warpFactorAtTip.value) ∧
  data.kkMass =
    (1 / Real.sqrt (Real.sqrt data.warpFactorAtTip.value)) / data.tipRadius ∧
  data.kkMassToTensionFactor =
    (Real.exp (Real.log 6 / 3) * Real.pi) /
      (Real.sqrt data.a0.value * data.stringCoupling * data.fluxM) ∧
  data.kkMass ^ (2 : ℕ) = data.kkMassToTensionFactor * data.tension

/-- Assumed KS warped-conifold confinement package. -/
theorem klebanov_strassler_confinement_package
    (data : KlebanovStrasslerConfinementData)
    (h_phys : PhysicsAssumption
      AssumptionId.stringKlebanovStrasslerConfinement
      (KlebanovStrasslerConfinementPackage data)) :
    KlebanovStrasslerConfinementPackage data := by
  exact h_phys

end PhysicsLogic.StringTheory
