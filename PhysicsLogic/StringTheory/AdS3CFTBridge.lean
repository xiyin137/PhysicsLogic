import PhysicsLogic.Assumptions
import PhysicsLogic.StringTheory.AdS3CFT2
import PhysicsLogic.QFT.CFT.TwoDimensional.ConformalManifolds

namespace PhysicsLogic.StringTheory

set_option autoImplicit false

/-- Cross-lane data for D1-D5 conformal-manifold geometry. -/
structure D1D5ConformalGeometryBridgeData where
  stringData : D1D5ConformalManifoldData
  qftData : PhysicsLogic.QFT.CFT.TwoDimensional.D1D5ConformalManifoldGeometryData

/-- Bridge package:
string-side D1-D5 conformal-manifold data aligned with QFT-side geometry data. -/
def D1D5ConformalGeometryBridgePackage
    (data : D1D5ConformalGeometryBridgeData) : Prop :=
  D1D5ConformalManifoldPackage data.stringData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.D1D5ConformalManifoldGeometryPackage
    data.qftData /\
  data.stringData.q1 = data.qftData.q1 /\
  data.stringData.q5 = data.qftData.q5 /\
  data.stringData.gcdCharge = data.qftData.gcdCharge /\
  data.stringData.invariantK = data.qftData.invariantK

/-- Assumed bridge package for D1-D5 conformal-manifold geometry data. -/
theorem d1_d5_conformal_geometry_bridge_package
    (data : D1D5ConformalGeometryBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3D1D5ConformalManifoldUduality
      (D1D5ConformalManifoldPackage data.stringData))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dD1D5ConformalManifoldQuaternionicQuotient
      (PhysicsLogic.QFT.CFT.TwoDimensional.D1D5ConformalManifoldGeometryPackage
        data.qftData))
    (h_q1 : data.stringData.q1 = data.qftData.q1)
    (h_q5 : data.stringData.q5 = data.qftData.q5)
    (h_gcd : data.stringData.gcdCharge = data.qftData.gcdCharge)
    (h_k : data.stringData.invariantK = data.qftData.invariantK) :
    D1D5ConformalGeometryBridgePackage data := by
  have h_string_pkg : D1D5ConformalManifoldPackage data.stringData :=
    d1_d5_conformal_manifold_package data.stringData h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.D1D5ConformalManifoldGeometryPackage
        data.qftData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.d1_d5_conformal_manifold_geometry_package
      data.qftData h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_q1, h_q5, h_gcd, h_k⟩

/-- Cross-lane data for the D1-D5 attractor/U-duality subspace. -/
structure D1D5AttractorBridgeData where
  stringData : D1D5ConformalManifoldData
  qftData : PhysicsLogic.QFT.CFT.TwoDimensional.D1D5AttractorTauData

/-- Bridge package:
string-side D1-D5 attractor relation aligned with QFT-side `tau` package. -/
def D1D5AttractorBridgePackage
    (data : D1D5AttractorBridgeData) : Prop :=
  D1D5ConformalManifoldPackage data.stringData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.D1D5AttractorTauGamma0Package
    data.qftData /\
  data.stringData.q1 = data.qftData.q1 /\
  data.stringData.q5 = data.qftData.q5 /\
  data.stringData.gcdCharge = data.qftData.gcdCharge /\
  data.stringData.invariantK = data.qftData.gamma0Level /\
  data.stringData.tau = data.qftData.tau /\
  data.stringData.tauTilde = data.qftData.tauTilde

/-- Assumed bridge package for D1-D5 attractor/U-duality data. -/
theorem d1_d5_attractor_bridge_package
    (data : D1D5AttractorBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3D1D5ConformalManifoldUduality
      (D1D5ConformalManifoldPackage data.stringData))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dD1D5AttractorTauGamma0Level
      (PhysicsLogic.QFT.CFT.TwoDimensional.D1D5AttractorTauGamma0Package
        data.qftData))
    (h_q1 : data.stringData.q1 = data.qftData.q1)
    (h_q5 : data.stringData.q5 = data.qftData.q5)
    (h_gcd : data.stringData.gcdCharge = data.qftData.gcdCharge)
    (h_level : data.stringData.invariantK = data.qftData.gamma0Level)
    (h_tau : data.stringData.tau = data.qftData.tau)
    (h_tau_tilde : data.stringData.tauTilde = data.qftData.tauTilde) :
    D1D5AttractorBridgePackage data := by
  have h_string_pkg : D1D5ConformalManifoldPackage data.stringData :=
    d1_d5_conformal_manifold_package data.stringData h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.D1D5AttractorTauGamma0Package
        data.qftData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.d1_d5_attractor_tau_gamma0_package
      data.qftData h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_q1, h_q5, h_gcd, h_level, h_tau, h_tau_tilde⟩

/-- Cross-lane data for the D1-D5 symmetric-product-orbifold locus. -/
structure D1D5SymmetricOrbifoldBridgeData where
  stringData : D1D5SymmetricOrbifoldData
  qftData : PhysicsLogic.QFT.CFT.TwoDimensional.D1D5SymmetricProductOrbifoldData

/-- Bridge package:
string-side symmetric-orbifold locus aligned with QFT-side arithmetic locus constraints. -/
def D1D5SymmetricOrbifoldBridgePackage
    (data : D1D5SymmetricOrbifoldBridgeData) : Prop :=
  D1D5SymmetricOrbifoldPackage data.stringData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.D1D5SymmetricProductOrbifoldLocusPackage
    data.qftData /\
  data.stringData.q1 = data.qftData.q1 /\
  data.stringData.q5 = data.qftData.q5 /\
  data.stringData.parityLocusTag = "Re(tau)=1/2 orbifold-symmetric locus" /\
  data.qftData.singularLocusReTau = 0 /\
  data.qftData.symmetricOrbifoldReTau = (1 / 2 : ℝ)

/-- Assumed bridge package for symmetric-product-orbifold data. -/
theorem d1_d5_symmetric_orbifold_bridge_package
    (data : D1D5SymmetricOrbifoldBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3D1D5SymmetricOrbifoldLocus
      (D1D5SymmetricOrbifoldPackage data.stringData))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dD1D5SymmetricProductOrbifoldLocus
      (PhysicsLogic.QFT.CFT.TwoDimensional.D1D5SymmetricProductOrbifoldLocusPackage
        data.qftData))
    (h_q1 : data.stringData.q1 = data.qftData.q1)
    (h_q5 : data.stringData.q5 = data.qftData.q5) :
    D1D5SymmetricOrbifoldBridgePackage data := by
  have h_string_pkg : D1D5SymmetricOrbifoldPackage data.stringData :=
    d1_d5_symmetric_orbifold_package data.stringData h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.D1D5SymmetricProductOrbifoldLocusPackage
        data.qftData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.d1_d5_symmetric_product_orbifold_locus_package
      data.qftData h_qft
  have h_string_pkg_full : D1D5SymmetricOrbifoldPackage data.stringData := h_string_pkg
  have h_qft_pkg_full :
      PhysicsLogic.QFT.CFT.TwoDimensional.D1D5SymmetricProductOrbifoldLocusPackage
        data.qftData := h_qft_pkg
  rcases h_string_pkg with ⟨_, _, _, h_parity_tag, _⟩
  rcases h_qft_pkg with ⟨_, _, _, _, h_qft_singular_re, h_qft_orbifold_re, _, _, _, _⟩
  exact ⟨h_string_pkg_full, h_qft_pkg_full, h_q1, h_q5, h_parity_tag, h_qft_singular_re, h_qft_orbifold_re⟩

end PhysicsLogic.StringTheory
