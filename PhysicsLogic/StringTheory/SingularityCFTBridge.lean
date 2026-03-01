import PhysicsLogic.Assumptions
import PhysicsLogic.StringTheory.GeometricSingularities

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
