import PhysicsLogic.Assumptions
import PhysicsLogic.StringTheory.GeometricSingularities
import PhysicsLogic.QFT.CFT.TwoDimensional.ConformalManifolds

namespace PhysicsLogic.StringTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Cross-lane interface data tying orbifold singularity structure to 2D CFT orbifold axioms. -/
structure OrbifoldSingularityCftBridgeData where
  orbifoldOrder : Nat
  stringOrbifoldTwistMarginalInputUsed : Bool
  qftOrbifoldModularInvariantInputUsed : Bool

/-- Orbifold bridge package:
Section-19 twisted-marginal orbifold input + 2D-CFT modular-orbifold input. -/
def OrbifoldSingularityCftBridgePackage
    (data : OrbifoldSingularityCftBridgeData) : Prop :=
  data.orbifoldOrder > 1 /\
  data.stringOrbifoldTwistMarginalInputUsed = true /\
  data.qftOrbifoldModularInvariantInputUsed = true

/-- Assumed orbifold bridge package combining StringTheory-Section19 and QFT-2D orbifold inputs. -/
theorem orbifold_singularity_cft_bridge_package
    (data : OrbifoldSingularityCftBridgeData)
    (h_order : data.orbifoldOrder > 1)
    (h_string : PhysicsAssumption
      AssumptionId.stringSingularityOrbifoldNFourTwistMarginal
      (data.stringOrbifoldTwistMarginalInputUsed = true))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dOrbifoldConstructionModularInvariant
      (data.qftOrbifoldModularInvariantInputUsed = true)) :
    OrbifoldSingularityCftBridgePackage data := by
  exact ⟨h_order, h_string, h_qft⟩

/-- Cross-lane data tying Section-19 orbifold conformal-manifold structure
to QFT 2D-CFT conformal-manifold packages. -/
structure OrbifoldConformalManifoldBridgeData where
  stringData : OrbifoldConformalManifoldData
  qftCountData : PhysicsLogic.QFT.CFT.TwoDimensional.OrbifoldConformalManifoldData
  qftKTwoData : PhysicsLogic.QFT.CFT.TwoDimensional.OrbifoldKTwoConformalManifoldData

/-- Bridge package for orbifold conformal manifolds:
Section-19 package + QFT counting package + `k=2` fixed-point distinction. -/
def OrbifoldConformalManifoldBridgePackage
    (data : OrbifoldConformalManifoldBridgeData) : Prop :=
  OrbifoldConformalManifoldPackage data.stringData /\
  data.stringData.orbifoldOrder = data.qftCountData.orbifoldOrder /\
  data.qftCountData.exactlyMarginalCount =
    4 * (data.stringData.orbifoldOrder - 1) /\
  (data.stringData.orbifoldOrder = 2 ->
    data.qftKTwoData.z2FixedPointCount = 2 /\
    data.qftKTwoData.regularFixedPointCount = 1 /\
    data.qftKTwoData.singularFixedPointCount = 1)

/-- Assumed orbifold conformal-manifold bridge:
string-theory orbifold package matched to QFT conformal-manifold counting and `k=2` fixed points. -/
theorem orbifold_conformal_manifold_bridge_package
    (data : OrbifoldConformalManifoldBridgeData)
    (h_orbifold_order_sync :
      data.stringData.orbifoldOrder = data.qftCountData.orbifoldOrder)
    (h_string : PhysicsAssumption
      AssumptionId.stringSingularityOrbifoldConformalManifoldSingularPoints
      (OrbifoldConformalManifoldPackage data.stringData))
    (h_qft_count : PhysicsAssumption
      AssumptionId.cft2dOrbifoldConformalManifoldDimensionFormula
      (PhysicsLogic.QFT.CFT.TwoDimensional.OrbifoldConformalManifoldDimensionFormula
        data.qftCountData))
    (h_qft_k2 : PhysicsAssumption
      AssumptionId.cft2dOrbifoldKTwoModuliFixedPointDistinction
      (PhysicsLogic.QFT.CFT.TwoDimensional.OrbifoldKTwoModuliFixedPointDistinction
        data.qftKTwoData)) :
    OrbifoldConformalManifoldBridgePackage data := by
  have h_string_pkg : OrbifoldConformalManifoldPackage data.stringData :=
    orbifold_conformal_manifold_package data.stringData h_string
  have h_qft_count_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.OrbifoldConformalManifoldDimensionFormula
        data.qftCountData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.orbifold_conformal_manifold_dimension_formula
      data.qftCountData h_qft_count
  have h_qft_k2_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.OrbifoldKTwoModuliFixedPointDistinction
        data.qftKTwoData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.orbifold_k_two_moduli_fixed_point_distinction
      data.qftKTwoData h_qft_k2
  rcases h_qft_count_pkg with ⟨_, h_twisted, h_exact⟩
  rcases h_qft_k2_pkg with ⟨_, h_fixed, h_regular, h_singular, _, _⟩
  refine ⟨h_string_pkg, h_orbifold_order_sync, ?_, ?_⟩
  · have h_exact_from_order :
      data.qftCountData.exactlyMarginalCount =
        4 * (data.qftCountData.orbifoldOrder - 1) := by
      simpa [h_twisted] using h_exact
    simpa [h_orbifold_order_sync] using h_exact_from_order
  · intro _
    exact ⟨h_fixed, h_regular, h_singular⟩

/-- Cross-lane interface data for DSLST coset construction and gauged-WZW/coset flow. -/
structure DslstCosetCftBridgeData where
  cosetLevel : Nat
  stringDslstCosetBackgroundInputUsed : Bool
  qftGaugedWzwCosetFlowInputUsed : Bool

/-- DSLST coset bridge package:
exact DSLST coset background + QFT gauged-WZW/coset-flow assumption. -/
def DslstCosetCftBridgePackage (data : DslstCosetCftBridgeData) : Prop :=
  data.cosetLevel > 1 /\
  data.stringDslstCosetBackgroundInputUsed = true /\
  data.qftGaugedWzwCosetFlowInputUsed = true

/-- Assumed DSLST coset bridge package combining StringTheory and QFT coset inputs. -/
theorem dslst_coset_cft_bridge_package
    (data : DslstCosetCftBridgeData)
    (h_level : data.cosetLevel > 1)
    (h_string : PhysicsAssumption
      AssumptionId.stringDslstDoubleScalingCosetBackground
      (data.stringDslstCosetBackgroundInputUsed = true))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dGaugedWzwCosetFlow
      (data.qftGaugedWzwCosetFlowInputUsed = true)) :
    DslstCosetCftBridgePackage data := by
  exact ⟨h_level, h_string, h_qft⟩

/-- Cross-lane interface data for cigar/Liouville mirror structure. -/
structure CigarLiouvilleMirrorBridgeData where
  stringMirrorInputUsed : Bool
  qftMirrorInputUsed : Bool

/-- Mirror bridge package:
string-theory cigar/Liouville mirror input + 2D-CFT mirror-duality input. -/
def CigarLiouvilleMirrorBridgePackage
    (data : CigarLiouvilleMirrorBridgeData) : Prop :=
  data.stringMirrorInputUsed = true /\
  data.qftMirrorInputUsed = true

/-- Assumed cigar/Liouville mirror bridge package. -/
theorem cigar_liouville_mirror_bridge_package
    (data : CigarLiouvilleMirrorBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringDslstCigarLiouvilleMirrorDuality
      (data.stringMirrorInputUsed = true))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dCigarLiouvilleMirrorDuality
      (data.qftMirrorInputUsed = true)) :
    CigarLiouvilleMirrorBridgePackage data := by
  exact ⟨h_string, h_qft⟩

/-- Cross-lane interface data for conifold worldsheet instantons and 2D NLSM conformality assumptions. -/
structure ConifoldInstantonNlsmBridgeData where
  stringConifoldInstantonInputUsed : Bool
  qftNlsmConformalInputUsed : Bool

/-- Conifold/NLSM bridge package:
worldsheet-instanton conifold input + 2D NLSM Weyl-anomaly-vanishing input. -/
def ConifoldInstantonNlsmBridgePackage
    (data : ConifoldInstantonNlsmBridgeData) : Prop :=
  data.stringConifoldInstantonInputUsed = true /\
  data.qftNlsmConformalInputUsed = true

/-- Assumed conifold/NLSM bridge package. -/
theorem conifold_instanton_nlsm_bridge_package
    (data : ConifoldInstantonNlsmBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringConifoldWorldsheetInstantonExpansion
      (data.stringConifoldInstantonInputUsed = true))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dNlsmWeylAnomalyVanishing
      (data.qftNlsmConformalInputUsed = true)) :
    ConifoldInstantonNlsmBridgePackage data := by
  exact ⟨h_string, h_qft⟩

end PhysicsLogic.StringTheory
