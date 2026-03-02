import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.QFT.CFT.TwoDimensional

set_option autoImplicit false
set_option linter.unusedVariables false

abbrev SuperstringVertexClaim := Prop

/-- NSNS picture-raising data expressed as CFT state/operator relations.
This captures the Section-08 relations around `\label{raisedfixedvop}` and
`\label{ccgunfix}` in the stringbook tex source. -/
structure NsnsPictureRaisingStateOperatorData (H : Type*) [SMul ℂ H] where
  pco : H → H
  pcoBar : H → H
  bMinusOne : H → H
  bBarMinusOne : H → H
  matterSupercurrentMinusHalf : H → H
  matterSupercurrentBarMinusHalf : H → H
  vertexMinusOneMinusOne : H
  vertexZeroZero : H
  matterPrimaryState : H
  pcoCollisionRegular : SuperstringVertexClaim
  etaXiTermsDropOutInSphereCorrelator : SuperstringVertexClaim

/-- Picture-raised NSNS vertex relation:
`V^(0,0) = lim X X̃ V^(-1,-1)` at the insertion. -/
def NsnsPictureRaisedVertexEquation {H : Type*} [SMul ℂ H]
    (data : NsnsPictureRaisingStateOperatorData H) : Prop :=
  data.pcoCollisionRegular ∧
    data.vertexZeroZero = data.pcoBar (data.pco data.vertexMinusOneMinusOne)

/-- Integrated-vertex conversion relation from `b_{-1}\tilde b_{-1}` insertion:
`\tilde b_{-1} b_{-1} V^(0,0) = (1/4) G^m_{-1/2}\tilde G^m_{-1/2} V^m`. -/
def NsnsIntegratedVertexConversionEquation {H : Type*} [SMul ℂ H]
    (data : NsnsPictureRaisingStateOperatorData H) : Prop :=
  data.bBarMinusOne (data.bMinusOne data.vertexZeroZero) =
    (1 / 4 : ℂ) •
      data.matterSupercurrentMinusHalf
        (data.matterSupercurrentBarMinusHalf data.matterPrimaryState)

/-- Combined CFT package for NSNS picture raising and integrated-vertex conversion. -/
def NsnsPictureRaisingStateOperatorPackage {H : Type*} [SMul ℂ H]
    (data : NsnsPictureRaisingStateOperatorData H) : Prop :=
  NsnsPictureRaisedVertexEquation data ∧
    NsnsIntegratedVertexConversionEquation data ∧
    data.etaXiTermsDropOutInSphereCorrelator

/-- Assumed Section-08 NSNS picture-raising package in state/operator form. -/
theorem nsns_picture_raising_state_operator_package
    {H : Type*} [SMul ℂ H]
    (data : NsnsPictureRaisingStateOperatorData H)
    (h_phys : PhysicsAssumption
      AssumptionId.stringSuperExplicitNsnsPictureRaising
      (NsnsPictureRaisingStateOperatorPackage data)) :
    NsnsPictureRaisingStateOperatorPackage data := by
  exact h_phys

end PhysicsLogic.QFT.CFT.TwoDimensional
