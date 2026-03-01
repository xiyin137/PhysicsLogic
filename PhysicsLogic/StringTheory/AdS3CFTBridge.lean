import PhysicsLogic.Assumptions
import PhysicsLogic.StringTheory.AdS3CFT2
import PhysicsLogic.QFT.CFT.TwoDimensional.ConformalManifolds
import PhysicsLogic.QFT.CFT.TwoDimensional.CurrentAlgebras

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

/-- Cross-lane data for bosonic AdS3 WZW level/radius matching. -/
structure AdS3BosonicWzwBridgeData where
  stringData : AdS3BosonicWZWData
  qftData : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2BosonicWzwData

/-- Bridge package:
string-side bosonic AdS3 WZW level/radius relation aligned with QFT-side current-algebra data. -/
def AdS3BosonicWzwBridgePackage
    (data : AdS3BosonicWzwBridgeData) : Prop :=
  AdS3BosonicWZWLevelRadiusRelation data.stringData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2BosonicWzwLevelRadiusRelation data.qftData /\
  data.stringData.levelK = data.qftData.levelK /\
  data.stringData.radius = data.qftData.radius /\
  data.stringData.alphaPrime = data.qftData.alphaPrime

/-- Assumed bridge package for bosonic AdS3 WZW level/radius data. -/
theorem ads3_bosonic_wzw_bridge_package
    (data : AdS3BosonicWzwBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3BosonicWzwLevelRadius
      (AdS3BosonicWZWLevelRadiusRelation data.stringData))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3BosonicWzwLevelRadius
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2BosonicWzwLevelRadiusRelation data.qftData))
    (h_level : data.stringData.levelK = data.qftData.levelK)
    (h_radius : data.stringData.radius = data.qftData.radius)
    (h_alpha : data.stringData.alphaPrime = data.qftData.alphaPrime) :
    AdS3BosonicWzwBridgePackage data := by
  have h_string_pkg : AdS3BosonicWZWLevelRadiusRelation data.stringData :=
    ads3_bosonic_wzw_level_radius_relation data.stringData h_string
  have h_qft_pkg : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2BosonicWzwLevelRadiusRelation data.qftData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_sl2_bosonic_wzw_level_radius_relation data.qftData h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_level, h_radius, h_alpha⟩

/-- Cross-lane data for AdS3 spectral-flow and mass-shell matching. -/
structure AdS3SpectralMassShellBridgeData where
  stringSpectral : AdS3BosonicSpectralFlowData
  stringMassShell : AdS3BosonicMassShellData
  qftSpectral : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2SpectralFlowData
  qftMassShell : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2MassShellData

/-- Bridge package:
string-side AdS3 spectral-flow/mass-shell packages aligned with QFT-side current-algebra constraints. -/
def AdS3SpectralMassShellBridgePackage
    (data : AdS3SpectralMassShellBridgeData) : Prop :=
  AdS3BosonicSpectralFlowPackage data.stringSpectral /\
  AdS3BosonicMassShellPackage data.stringMassShell /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2SpectralFlowAutomorphism data.qftSpectral /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2MassShellEnergyRelation data.qftMassShell /\
  data.stringSpectral.levelK = data.qftSpectral.levelK /\
  data.stringMassShell.levelK = data.qftMassShell.levelK /\
  data.stringSpectral.flowW = data.qftSpectral.flowW /\
  data.stringMassShell.flowW = data.qftMassShell.flowW /\
  data.stringMassShell.j0Three = data.qftMassShell.j0Three

/-- Assumed bridge package for AdS3 spectral-flow and mass-shell data. -/
theorem ads3_spectral_mass_shell_bridge_package
    (data : AdS3SpectralMassShellBridgeData)
    (h_string_spectral : PhysicsAssumption
      AssumptionId.stringAdS3BosonicSpectralFlow
      (AdS3BosonicSpectralFlowPackage data.stringSpectral))
    (h_string_mass : PhysicsAssumption
      AssumptionId.stringAdS3BosonicMassShell
      (AdS3BosonicMassShellPackage data.stringMassShell))
    (h_qft_spectral : PhysicsAssumption
      AssumptionId.cft2dAds3Sl2SpectralFlowAutomorphism
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2SpectralFlowAutomorphism data.qftSpectral))
    (h_qft_mass : PhysicsAssumption
      AssumptionId.cft2dAds3Sl2MassShellEnergyRelation
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2MassShellEnergyRelation data.qftMassShell))
    (h_k_spectral : data.stringSpectral.levelK = data.qftSpectral.levelK)
    (h_k_mass : data.stringMassShell.levelK = data.qftMassShell.levelK)
    (h_w_spectral : data.stringSpectral.flowW = data.qftSpectral.flowW)
    (h_w_mass : data.stringMassShell.flowW = data.qftMassShell.flowW)
    (h_j0 : data.stringMassShell.j0Three = data.qftMassShell.j0Three) :
    AdS3SpectralMassShellBridgePackage data := by
  have h_string_spectral_pkg : AdS3BosonicSpectralFlowPackage data.stringSpectral :=
    ads3_bosonic_spectral_flow_package data.stringSpectral h_string_spectral
  have h_string_mass_pkg : AdS3BosonicMassShellPackage data.stringMassShell :=
    ads3_bosonic_mass_shell_package data.stringMassShell h_string_mass
  have h_qft_spectral_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2SpectralFlowAutomorphism data.qftSpectral :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_sl2_spectral_flow_automorphism data.qftSpectral h_qft_spectral
  have h_qft_mass_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3Sl2MassShellEnergyRelation data.qftMassShell :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_sl2_mass_shell_energy_relation data.qftMassShell h_qft_mass
  exact ⟨h_string_spectral_pkg, h_string_mass_pkg, h_qft_spectral_pkg, h_qft_mass_pkg,
    h_k_spectral, h_k_mass, h_w_spectral, h_w_mass, h_j0⟩

/-- Cross-lane data for purely `(NS,NS)` AdS3xS3xM4 worldsheet matching. -/
structure AdS3NsnsWorldsheetBridgeData where
  stringData : AdS3NSNSSuperstringBackgroundData
  qftData : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterData

/-- Bridge package:
string-side `(NS,NS)` worldsheet background package aligned with QFT-side matter-SCFT package. -/
def AdS3NsnsWorldsheetBridgePackage
    (data : AdS3NsnsWorldsheetBridgeData) : Prop :=
  AdS3NSNSSuperstringBackgroundPackage data.stringData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterScftPackage data.qftData /\
  data.stringData.levelK = data.qftData.levelK /\
  data.stringData.radius = data.qftData.radius /\
  data.stringData.alphaPrime = data.qftData.alphaPrime /\
  data.stringData.matterCentralCharge = data.qftData.totalMatterCentralCharge

/-- Assumed bridge package for purely `(NS,NS)` AdS3 worldsheet data. -/
theorem ads3_nsns_worldsheet_bridge_package
    (data : AdS3NsnsWorldsheetBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3NsnsSuperstringWorldsheet
      (AdS3NSNSSuperstringBackgroundPackage data.stringData))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsWorldsheetMatterScft
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterScftPackage data.qftData))
    (h_level : data.stringData.levelK = data.qftData.levelK)
    (h_radius : data.stringData.radius = data.qftData.radius)
    (h_alpha : data.stringData.alphaPrime = data.qftData.alphaPrime)
    (h_c : data.stringData.matterCentralCharge = data.qftData.totalMatterCentralCharge) :
    AdS3NsnsWorldsheetBridgePackage data := by
  have h_string_pkg : AdS3NSNSSuperstringBackgroundPackage data.stringData :=
    ads3_nsns_superstring_background_package data.stringData h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterScftPackage data.qftData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_nsns_worldsheet_matter_scft_package data.qftData h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_level, h_radius, h_alpha, h_c⟩

/-- Cross-lane data for `(NS,NS)` AdS3 worldsheet affine-shift and spin-field/GSO constraints. -/
structure AdS3NsnsGsoBridgeData where
  stringData : AdS3NSNSSuperstringBackgroundData
  qftMatterData : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterData
  qftAffineData : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsAffineLevelShiftData
  qftGsoData : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSpinFieldGsoData

/-- Bridge package:
string-side `(NS,NS)` AdS3 worldsheet background aligned with QFT-side matter,
affine-level shifts, and spin-field/GSO constraints. -/
def AdS3NsnsGsoBridgePackage
    (data : AdS3NsnsGsoBridgeData) : Prop :=
  AdS3NSNSSuperstringBackgroundPackage data.stringData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterScftPackage data.qftMatterData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsAffineLevelShiftPackage data.qftAffineData /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSpinFieldGsoConstraintPackage data.qftGsoData /\
  data.stringData.levelK = data.qftMatterData.levelK /\
  data.stringData.levelK = data.qftAffineData.levelK /\
  data.stringData.matterCentralCharge = data.qftMatterData.totalMatterCentralCharge /\
  data.qftGsoData.supersymmetryCurrentCount = 16

/-- Assumed bridge package for `(NS,NS)` AdS3 worldsheet and spin-field/GSO constraints. -/
theorem ads3_nsns_gso_bridge_package
    (data : AdS3NsnsGsoBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3NsnsSuperstringWorldsheet
      (AdS3NSNSSuperstringBackgroundPackage data.stringData))
    (h_qft_matter : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsWorldsheetMatterScft
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterScftPackage data.qftMatterData))
    (h_qft_affine : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsAffineLevelShift
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsAffineLevelShiftPackage data.qftAffineData))
    (h_qft_gso : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsSpinFieldGsoConstraints
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSpinFieldGsoConstraintPackage data.qftGsoData))
    (h_level_matter : data.stringData.levelK = data.qftMatterData.levelK)
    (h_level_affine : data.stringData.levelK = data.qftAffineData.levelK)
    (h_c : data.stringData.matterCentralCharge = data.qftMatterData.totalMatterCentralCharge) :
    AdS3NsnsGsoBridgePackage data := by
  have h_string_pkg : AdS3NSNSSuperstringBackgroundPackage data.stringData :=
    ads3_nsns_superstring_background_package data.stringData h_string
  have h_qft_matter_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsWorldsheetMatterScftPackage data.qftMatterData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_nsns_worldsheet_matter_scft_package data.qftMatterData h_qft_matter
  have h_qft_affine_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsAffineLevelShiftPackage data.qftAffineData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_nsns_affine_level_shift_package data.qftAffineData h_qft_affine
  have h_qft_gso_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSpinFieldGsoConstraintPackage data.qftGsoData :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_nsns_spin_field_gso_constraint_package data.qftGsoData h_qft_gso
  have h_qft_gso_pkg_full :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSpinFieldGsoConstraintPackage data.qftGsoData := h_qft_gso_pkg
  rcases h_qft_gso_pkg with ⟨_, _, _, _, _, _, _, h_susy_count⟩
  exact ⟨h_string_pkg, h_qft_matter_pkg, h_qft_affine_pkg, h_qft_gso_pkg_full,
    h_level_matter, h_level_affine, h_c, h_susy_count⟩

/-- Cross-lane data for `(NS,NS)` AdS3 supersymmetric spectral flow and superstring mass shell. -/
structure AdS3NsnsMassShellBridgeData where
  stringMassShell : AdS3NSNSSuperstringMassShellData
  qftSpectral : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSl2SpectralFlowData
  qftMassShell : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSuperstringMassShellData

/-- Bridge package:
string-side `(NS,NS)` AdS3 superstring mass-shell/BPS data aligned with QFT-side
supersymmetric `hatSL(2)_k` spectral-flow and mass-shell constraints. -/
def AdS3NsnsMassShellBridgePackage
    (data : AdS3NsnsMassShellBridgeData) : Prop :=
  AdS3NSNSSuperstringMassShellPackage data.stringMassShell /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSl2SpectralFlowAutomorphism data.qftSpectral /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSuperstringMassShellBpsPackage data.qftMassShell /\
  data.stringMassShell.levelK = data.qftMassShell.levelK /\
  data.stringMassShell.levelK = data.qftSpectral.levelK /\
  data.stringMassShell.flowW = data.qftMassShell.flowW /\
  data.stringMassShell.flowW = data.qftSpectral.flowW /\
  data.stringMassShell.spinJ = data.qftMassShell.spinJ /\
  data.stringMassShell.mQuantum = data.qftMassShell.mQuantum /\
  data.stringMassShell.adsDescendantLevel = data.qftMassShell.adsDescendantLevel /\
  data.stringMassShell.suDescendantLevel = data.qftMassShell.suDescendantLevel /\
  data.stringMassShell.internalWeight = data.qftMassShell.internalWeight /\
  data.stringMassShell.suSpin = data.qftMassShell.suSpin /\
  data.stringMassShell.j0Three = data.qftMassShell.j0Three

/-- Assumed bridge package for `(NS,NS)` AdS3 supersymmetric spectral-flow/mass-shell data. -/
theorem ads3_nsns_mass_shell_bridge_package
    (data : AdS3NsnsMassShellBridgeData)
    (h_string_mass : PhysicsAssumption
      AssumptionId.stringAdS3NsnsSuperstringMassShell
      (AdS3NSNSSuperstringMassShellPackage data.stringMassShell))
    (h_qft_spectral : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsSl2SpectralFlowAutomorphism
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSl2SpectralFlowAutomorphism data.qftSpectral))
    (h_qft_mass : PhysicsAssumption
      AssumptionId.cft2dAds3NsnsSuperstringMassShellBps
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSuperstringMassShellBpsPackage data.qftMassShell))
    (h_k_mass : data.stringMassShell.levelK = data.qftMassShell.levelK)
    (h_k_spectral : data.stringMassShell.levelK = data.qftSpectral.levelK)
    (h_w_mass : data.stringMassShell.flowW = data.qftMassShell.flowW)
    (h_w_spectral : data.stringMassShell.flowW = data.qftSpectral.flowW)
    (h_j : data.stringMassShell.spinJ = data.qftMassShell.spinJ)
    (h_m : data.stringMassShell.mQuantum = data.qftMassShell.mQuantum)
    (h_n : data.stringMassShell.adsDescendantLevel = data.qftMassShell.adsDescendantLevel)
    (h_nsu : data.stringMassShell.suDescendantLevel = data.qftMassShell.suDescendantLevel)
    (h_hint : data.stringMassShell.internalWeight = data.qftMassShell.internalWeight)
    (h_jprime : data.stringMassShell.suSpin = data.qftMassShell.suSpin)
    (h_j0 : data.stringMassShell.j0Three = data.qftMassShell.j0Three) :
    AdS3NsnsMassShellBridgePackage data := by
  have h_string_mass_pkg : AdS3NSNSSuperstringMassShellPackage data.stringMassShell :=
    ads3_nsns_superstring_mass_shell_package data.stringMassShell h_string_mass
  have h_qft_spectral_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSl2SpectralFlowAutomorphism data.qftSpectral :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_nsns_sl2_spectral_flow_automorphism
      data.qftSpectral h_qft_spectral
  have h_qft_mass_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3NsnsSuperstringMassShellBpsPackage data.qftMassShell :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_nsns_superstring_mass_shell_bps_package
      data.qftMassShell h_qft_mass
  exact ⟨h_string_mass_pkg, h_qft_spectral_pkg, h_qft_mass_pkg, h_k_mass, h_k_spectral,
    h_w_mass, h_w_spectral, h_j, h_m, h_n, h_nsu, h_hint, h_jprime, h_j0⟩

/-- Cross-lane data for AdS3 mixed-flux worldsheet deformation and pulsating spectrum. -/
structure AdS3MixedFluxBridgeData where
  stringFlux : AdS3MixedFluxData
  stringPulsating : AdS3MixedFluxPulsatingData
  qftFlux : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetData
  qftPulsating : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingSpectrumData

/-- Bridge package:
string-side mixed-flux parameter/spectrum packages aligned with QFT-side
worldsheet-deformation and pulsating-spectrum constraints. -/
def AdS3MixedFluxBridgePackage
    (data : AdS3MixedFluxBridgeData) : Prop :=
  AdS3MixedFluxPackage data.stringFlux /\
  AdS3MixedFluxPulsatingPackage data.stringPulsating /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetDeformationPackage data.qftFlux /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingSpectrumPackage data.qftPulsating /\
  data.stringFlux.stringCoupling = data.qftFlux.stringCoupling /\
  data.stringFlux.alphaPrime = data.qftFlux.alphaPrime /\
  data.stringFlux.nsFluxK5 = data.qftFlux.nsFluxK5 /\
  data.stringFlux.rrFluxQ5 = data.qftFlux.rrFluxQ5 /\
  data.stringFlux.radius = data.qftFlux.radius /\
  data.stringFlux.mu = data.qftFlux.mu /\
  data.stringPulsating.n = data.qftPulsating.excitationNumber /\
  data.stringPulsating.k = data.qftPulsating.levelK /\
  data.stringPulsating.mu = data.qftPulsating.mu /\
  data.stringPulsating.delta = data.qftPulsating.delta

/-- Assumed bridge package for AdS3 mixed-flux worldsheet and pulsating-spectrum data. -/
theorem ads3_mixed_flux_bridge_package
    (data : AdS3MixedFluxBridgeData)
    (h_string_flux : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxParameterization
      (AdS3MixedFluxPackage data.stringFlux))
    (h_string_pulsating : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxPulsatingShift
      (AdS3MixedFluxPulsatingPackage data.stringPulsating))
    (h_qft_flux : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxWorldsheetDeformation
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetDeformationPackage data.qftFlux))
    (h_qft_pulsating : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingSpectrumShift
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingSpectrumPackage data.qftPulsating))
    (h_g : data.stringFlux.stringCoupling = data.qftFlux.stringCoupling)
    (h_alpha : data.stringFlux.alphaPrime = data.qftFlux.alphaPrime)
    (h_k5 : data.stringFlux.nsFluxK5 = data.qftFlux.nsFluxK5)
    (h_q5 : data.stringFlux.rrFluxQ5 = data.qftFlux.rrFluxQ5)
    (h_r : data.stringFlux.radius = data.qftFlux.radius)
    (h_mu_flux : data.stringFlux.mu = data.qftFlux.mu)
    (h_n : data.stringPulsating.n = data.qftPulsating.excitationNumber)
    (h_k : data.stringPulsating.k = data.qftPulsating.levelK)
    (h_mu_pulsating : data.stringPulsating.mu = data.qftPulsating.mu)
    (h_delta : data.stringPulsating.delta = data.qftPulsating.delta) :
    AdS3MixedFluxBridgePackage data := by
  have h_string_flux_pkg : AdS3MixedFluxPackage data.stringFlux :=
    ads3_mixed_flux_package data.stringFlux h_string_flux
  have h_string_pulsating_pkg : AdS3MixedFluxPulsatingPackage data.stringPulsating :=
    ads3_mixed_flux_pulsating_package data.stringPulsating h_string_pulsating
  have h_qft_flux_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetDeformationPackage data.qftFlux :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_worldsheet_deformation_package
      data.qftFlux h_qft_flux
  have h_qft_pulsating_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingSpectrumPackage data.qftPulsating :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_pulsating_spectrum_package
      data.qftPulsating h_qft_pulsating
  exact ⟨h_string_flux_pkg, h_string_pulsating_pkg, h_qft_flux_pkg, h_qft_pulsating_pkg,
    h_g, h_alpha, h_k5, h_q5, h_r, h_mu_flux, h_n, h_k, h_mu_pulsating, h_delta⟩

end PhysicsLogic.StringTheory
