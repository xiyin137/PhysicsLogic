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

/-- Cross-lane data for the mixed-flux parameter-definition block `mu = g_B Q5 / K5`,
`k = K5`. -/
structure AdS3MixedFluxMuKDefinitionBridgeData where
  stringMuK : AdS3MixedFluxMuKDefinitionData
  qftMuK : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMuKDefinitionCftData

/-- Bridge package:
string-side and QFT-side mixed-flux `mu`/`k` definition data aligned
field-by-field. -/
def AdS3MixedFluxMuKDefinitionBridgePackage
    (data : AdS3MixedFluxMuKDefinitionBridgeData) : Prop :=
  AdS3MixedFluxMuKDefinitionPackage data.stringMuK /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMuKDefinitionCftPackage data.qftMuK /\
  data.stringMuK.stringCoupling = data.qftMuK.stringCoupling /\
  data.stringMuK.rrFluxQ5 = data.qftMuK.rrFluxQ5 /\
  data.stringMuK.nsFluxK5 = data.qftMuK.nsFluxK5 /\
  data.stringMuK.mu = data.qftMuK.mu /\
  data.stringMuK.levelK = data.qftMuK.levelK

/-- Assumed bridge package for mixed-flux `mu`/`k` definition data. -/
theorem ads3_mixed_flux_mu_k_definition_bridge_package
    (data : AdS3MixedFluxMuKDefinitionBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxMuKDefinition
      (AdS3MixedFluxMuKDefinitionPackage data.stringMuK))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxMuKDefinition
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMuKDefinitionCftPackage
        data.qftMuK))
    (h_g : data.stringMuK.stringCoupling = data.qftMuK.stringCoupling)
    (h_q5 : data.stringMuK.rrFluxQ5 = data.qftMuK.rrFluxQ5)
    (h_k5 : data.stringMuK.nsFluxK5 = data.qftMuK.nsFluxK5)
    (h_mu : data.stringMuK.mu = data.qftMuK.mu)
    (h_k : data.stringMuK.levelK = data.qftMuK.levelK) :
    AdS3MixedFluxMuKDefinitionBridgePackage data := by
  have h_string_pkg : AdS3MixedFluxMuKDefinitionPackage data.stringMuK :=
    ads3_mixed_flux_mu_k_definition_package data.stringMuK h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMuKDefinitionCftPackage
        data.qftMuK :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_mu_k_definition_cft_package
      data.qftMuK h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_g, h_q5, h_k5, h_mu, h_k⟩

/-- Cross-lane data for the mixed-flux pulsating turning-point relation. -/
structure AdS3MixedFluxPulsatingTurningPointBridgeData where
  stringTurningPoint : AdS3MixedFluxPulsatingTurningPointData
  qftTurningPoint :
    PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingTurningPointCftData

/-- Bridge package:
string-side and QFT-side mixed-flux pulsating turning-point data aligned
field-by-field. -/
def AdS3MixedFluxPulsatingTurningPointBridgePackage
    (data : AdS3MixedFluxPulsatingTurningPointBridgeData) : Prop :=
  AdS3MixedFluxPulsatingTurningPointPackage data.stringTurningPoint /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingTurningPointCftPackage
    data.qftTurningPoint /\
  data.stringTurningPoint.alphaPrime = data.qftTurningPoint.alphaPrime /\
  data.stringTurningPoint.radiusSquared = data.qftTurningPoint.radiusSquared /\
  data.stringTurningPoint.k5Flux = data.qftTurningPoint.k5Flux /\
  data.stringTurningPoint.maximalRadius = data.qftTurningPoint.maximalRadius /\
  data.stringTurningPoint.turningPointEnergy = data.qftTurningPoint.turningPointEnergy /\
  data.stringTurningPoint.radialVelocityAtTurningPoint =
    data.qftTurningPoint.radialVelocityAtTurningPoint /\
  data.stringTurningPoint.maximalRadiusIsTurningPoint =
    data.qftTurningPoint.maximalRadiusIsTurningPoint

/-- Assumed bridge package for mixed-flux pulsating turning-point data. -/
theorem ads3_mixed_flux_pulsating_turning_point_bridge_package
    (data : AdS3MixedFluxPulsatingTurningPointBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxPulsatingTurningPoint
      (AdS3MixedFluxPulsatingTurningPointPackage data.stringTurningPoint))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingTurningPoint
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingTurningPointCftPackage
        data.qftTurningPoint))
    (h_alpha : data.stringTurningPoint.alphaPrime = data.qftTurningPoint.alphaPrime)
    (h_r2 : data.stringTurningPoint.radiusSquared = data.qftTurningPoint.radiusSquared)
    (h_k5 : data.stringTurningPoint.k5Flux = data.qftTurningPoint.k5Flux)
    (h_r0 : data.stringTurningPoint.maximalRadius = data.qftTurningPoint.maximalRadius)
    (h_delta : data.stringTurningPoint.turningPointEnergy = data.qftTurningPoint.turningPointEnergy)
    (h_rdot :
      data.stringTurningPoint.radialVelocityAtTurningPoint =
        data.qftTurningPoint.radialVelocityAtTurningPoint)
    (h_turning :
      data.stringTurningPoint.maximalRadiusIsTurningPoint =
        data.qftTurningPoint.maximalRadiusIsTurningPoint) :
    AdS3MixedFluxPulsatingTurningPointBridgePackage data := by
  have h_string_pkg :
      AdS3MixedFluxPulsatingTurningPointPackage data.stringTurningPoint :=
    ads3_mixed_flux_pulsating_turning_point_package data.stringTurningPoint h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingTurningPointCftPackage
        data.qftTurningPoint :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_pulsating_turning_point_cft_package
      data.qftTurningPoint h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_alpha, h_r2, h_k5, h_r0, h_delta, h_rdot, h_turning⟩

/-- Cross-lane data for mixed-flux pulsating Bohr-Sommerfeld quantization. -/
structure AdS3MixedFluxPulsatingBohrSommerfeldBridgeData where
  stringBohr : AdS3MixedFluxPulsatingBohrSommerfeldData
  qftBohr : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingBohrSommerfeldCftData

/-- Bridge package:
string-side and QFT-side mixed-flux pulsating Bohr-Sommerfeld data aligned
field-by-field. -/
def AdS3MixedFluxPulsatingBohrSommerfeldBridgePackage
    (data : AdS3MixedFluxPulsatingBohrSommerfeldBridgeData) : Prop :=
  AdS3MixedFluxPulsatingBohrSommerfeldPackage data.stringBohr /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingBohrSommerfeldCftPackage
    data.qftBohr /\
  data.stringBohr.alphaPrime = data.qftBohr.alphaPrime /\
  data.stringBohr.radiusSquared = data.qftBohr.radiusSquared /\
  data.stringBohr.k5Flux = data.qftBohr.k5Flux /\
  data.stringBohr.excitationNumber = data.qftBohr.excitationNumber /\
  data.stringBohr.maximalRadius = data.qftBohr.maximalRadius /\
  data.stringBohr.bohrSommerfeldPeriod = data.qftBohr.bohrSommerfeldPeriod /\
  data.stringBohr.bohrSommerfeldPeriodRepresentsTwoPi =
    data.qftBohr.bohrSommerfeldPeriodRepresentsTwoPi /\
  data.stringBohr.bohrSommerfeldIntegral = data.qftBohr.bohrSommerfeldIntegral /\
  data.stringBohr.turningPointEnergy = data.qftBohr.turningPointEnergy

/-- Assumed bridge package for mixed-flux pulsating Bohr-Sommerfeld data. -/
theorem ads3_mixed_flux_pulsating_bohr_sommerfeld_bridge_package
    (data : AdS3MixedFluxPulsatingBohrSommerfeldBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxPulsatingBohrSommerfeld
      (AdS3MixedFluxPulsatingBohrSommerfeldPackage data.stringBohr))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingBohrSommerfeld
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingBohrSommerfeldCftPackage
        data.qftBohr))
    (h_alpha : data.stringBohr.alphaPrime = data.qftBohr.alphaPrime)
    (h_r2 : data.stringBohr.radiusSquared = data.qftBohr.radiusSquared)
    (h_k5 : data.stringBohr.k5Flux = data.qftBohr.k5Flux)
    (h_n : data.stringBohr.excitationNumber = data.qftBohr.excitationNumber)
    (h_r0 : data.stringBohr.maximalRadius = data.qftBohr.maximalRadius)
    (h_period : data.stringBohr.bohrSommerfeldPeriod = data.qftBohr.bohrSommerfeldPeriod)
    (h_period_two_pi :
      data.stringBohr.bohrSommerfeldPeriodRepresentsTwoPi =
        data.qftBohr.bohrSommerfeldPeriodRepresentsTwoPi)
    (h_integral : data.stringBohr.bohrSommerfeldIntegral = data.qftBohr.bohrSommerfeldIntegral)
    (h_delta : data.stringBohr.turningPointEnergy = data.qftBohr.turningPointEnergy) :
    AdS3MixedFluxPulsatingBohrSommerfeldBridgePackage data := by
  have h_string_pkg : AdS3MixedFluxPulsatingBohrSommerfeldPackage data.stringBohr :=
    ads3_mixed_flux_pulsating_bohr_sommerfeld_package data.stringBohr h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingBohrSommerfeldCftPackage
        data.qftBohr :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_pulsating_bohr_sommerfeld_cft_package
      data.qftBohr h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_alpha, h_r2, h_k5, h_n, h_r0, h_period, h_period_two_pi,
    h_integral, h_delta⟩

/-- Cross-lane data for the mixed-flux pulsating-threshold relation. -/
structure AdS3MixedFluxPulsatingThresholdBridgeData where
  stringThreshold : AdS3MixedFluxPulsatingThresholdData
  qftThreshold : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingThresholdCftData

/-- Bridge package:
string-side and QFT-side mixed-flux pulsating-threshold data aligned
field-by-field. -/
def AdS3MixedFluxPulsatingThresholdBridgePackage
    (data : AdS3MixedFluxPulsatingThresholdBridgeData) : Prop :=
  AdS3MixedFluxPulsatingThresholdPackage data.stringThreshold /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingThresholdCftPackage
    data.qftThreshold /\
  data.stringThreshold.excitationNumber = data.qftThreshold.excitationNumber /\
  data.stringThreshold.levelK = data.qftThreshold.levelK /\
  data.stringThreshold.poleExcitationNumber = data.qftThreshold.poleExcitationNumber /\
  data.stringThreshold.muOrderTwoCorrectionDenominator =
    data.qftThreshold.muOrderTwoCorrectionDenominator /\
  data.stringThreshold.shortStringEnergyAtPole = data.qftThreshold.shortStringEnergyAtPole /\
  data.stringThreshold.nsnsLongStringThresholdDimension =
    data.qftThreshold.nsnsLongStringThresholdDimension

/-- Assumed bridge package for mixed-flux pulsating-threshold data. -/
theorem ads3_mixed_flux_pulsating_threshold_bridge_package
    (data : AdS3MixedFluxPulsatingThresholdBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxPulsatingThresholdPole
      (AdS3MixedFluxPulsatingThresholdPackage data.stringThreshold))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxPulsatingThresholdPole
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingThresholdCftPackage
        data.qftThreshold))
    (h_n : data.stringThreshold.excitationNumber = data.qftThreshold.excitationNumber)
    (h_k : data.stringThreshold.levelK = data.qftThreshold.levelK)
    (h_npole :
      data.stringThreshold.poleExcitationNumber = data.qftThreshold.poleExcitationNumber)
    (h_den :
      data.stringThreshold.muOrderTwoCorrectionDenominator =
        data.qftThreshold.muOrderTwoCorrectionDenominator)
    (h_energy :
      data.stringThreshold.shortStringEnergyAtPole = data.qftThreshold.shortStringEnergyAtPole)
    (h_threshold :
      data.stringThreshold.nsnsLongStringThresholdDimension =
        data.qftThreshold.nsnsLongStringThresholdDimension) :
    AdS3MixedFluxPulsatingThresholdBridgePackage data := by
  have h_string_pkg :
      AdS3MixedFluxPulsatingThresholdPackage data.stringThreshold :=
    ads3_mixed_flux_pulsating_threshold_package data.stringThreshold h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxPulsatingThresholdCftPackage
        data.qftThreshold :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_pulsating_threshold_cft_package
      data.qftThreshold h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_n, h_k, h_npole, h_den, h_energy, h_threshold⟩

/-- Cross-lane data for mixed-flux long-string threshold/discretization transition. -/
structure AdS3MixedFluxLongStringTransitionBridgeData where
  stringTransition : AdS3MixedFluxLongStringTransitionData
  qftFlux : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetData

/-- Bridge package:
string-side and QFT-side mixed-flux long-string transition data aligned across
threshold, continuum/discrete behavior, and boundary-reaching conditions. -/
def AdS3MixedFluxLongStringTransitionBridgePackage
    (data : AdS3MixedFluxLongStringTransitionBridgeData) : Prop :=
  AdS3MixedFluxLongStringTransitionPackage data.stringTransition /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetDeformationPackage data.qftFlux /\
  data.stringTransition.nsFluxK5 = data.qftFlux.nsFluxK5 /\
  data.stringTransition.mu = data.qftFlux.mu /\
  data.stringTransition.longStringContinuumPresent = data.qftFlux.longStringContinuumPresent /\
  data.stringTransition.longStringSpectrumDiscrete = data.qftFlux.longStringSpectrumDiscrete /\
  data.stringTransition.shortLongDistinctionSharp = data.qftFlux.shortLongDistinctionSharp /\
  data.stringTransition.longStringsReachBoundaryAtFiniteEnergy =
    data.qftFlux.longStringsReachBoundaryAtFiniteEnergy /\
  data.stringTransition.nsnsLongStringThresholdDimension =
    data.qftFlux.nsnsLongStringThresholdDimension

/-- Assumed bridge package for mixed-flux long-string transition data. -/
theorem ads3_mixed_flux_long_string_transition_bridge_package
    (data : AdS3MixedFluxLongStringTransitionBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxLongStringSpectrumTransition
      (AdS3MixedFluxLongStringTransitionPackage data.stringTransition))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxWorldsheetDeformation
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetDeformationPackage
        data.qftFlux))
    (h_k5 : data.stringTransition.nsFluxK5 = data.qftFlux.nsFluxK5)
    (h_mu : data.stringTransition.mu = data.qftFlux.mu)
    (h_cont :
      data.stringTransition.longStringContinuumPresent = data.qftFlux.longStringContinuumPresent)
    (h_disc :
      data.stringTransition.longStringSpectrumDiscrete = data.qftFlux.longStringSpectrumDiscrete)
    (h_sharp :
      data.stringTransition.shortLongDistinctionSharp = data.qftFlux.shortLongDistinctionSharp)
    (h_boundary :
      data.stringTransition.longStringsReachBoundaryAtFiniteEnergy =
        data.qftFlux.longStringsReachBoundaryAtFiniteEnergy)
    (h_threshold :
      data.stringTransition.nsnsLongStringThresholdDimension =
        data.qftFlux.nsnsLongStringThresholdDimension) :
    AdS3MixedFluxLongStringTransitionBridgePackage data := by
  have h_string_pkg :
      AdS3MixedFluxLongStringTransitionPackage data.stringTransition :=
    ads3_mixed_flux_long_string_transition_package data.stringTransition h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWorldsheetDeformationPackage
        data.qftFlux :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_worldsheet_deformation_package
      data.qftFlux h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_k5, h_mu, h_cont, h_disc, h_sharp, h_boundary,
    h_threshold⟩

/-- Cross-lane data for mixed-flux RR-deformation SFT recursion and mass-shift packages. -/
structure AdS3MixedFluxSftMassShiftBridgeData where
  stringSft : AdS3MixedFluxSftRrDeformationData
  stringMassShift : AdS3MixedFluxMassShiftFromFourPointData
  qftSft : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxSftRrDeformationCftData
  qftMassShift :
    PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMassShiftFromFourPointCftData

/-- Bridge package:
string-side mixed-flux RR-deformation SFT/mass-shift packages aligned with
QFT-side worldsheet-CFT/SFT abstractions of the same data. -/
def AdS3MixedFluxSftMassShiftBridgePackage
    (data : AdS3MixedFluxSftMassShiftBridgeData) : Prop :=
  AdS3MixedFluxSftRrDeformationPackage data.stringSft /\
  AdS3MixedFluxMassShiftFromFourPointPackage data.stringMassShift /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxSftRrDeformationCftPackage data.qftSft /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMassShiftFromFourPointCftPackage
    data.qftMassShift /\
  data.stringSft.mu = data.qftSft.mu /\
  data.stringSft.levelK = data.qftSft.levelK /\
  data.stringSft.secondOrderEquationCoefficient = data.qftSft.secondOrderEquationCoefficient /\
  data.stringMassShift.mu = data.qftMassShift.mu /\
  data.stringMassShift.alphaPrime = data.qftMassShift.alphaPrime /\
  data.stringMassShift.scalingDimensionMu = data.qftMassShift.scalingDimensionMu /\
  data.stringMassShift.scalingDimensionZero = data.qftMassShift.scalingDimensionZero /\
  data.stringMassShift.massSquaredShift = data.qftMassShift.massSquaredShift /\
  data.stringMassShift.fourPointAmplitude = data.qftMassShift.fourPointAmplitude

/-- Assumed bridge package for mixed-flux RR-deformation SFT recursion and mass-shift data. -/
theorem ads3_mixed_flux_sft_mass_shift_bridge_package
    (data : AdS3MixedFluxSftMassShiftBridgeData)
    (h_string_sft : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxSftRrDeformation
      (AdS3MixedFluxSftRrDeformationPackage data.stringSft))
    (h_string_mass : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxMassShiftFromFourPoint
      (AdS3MixedFluxMassShiftFromFourPointPackage data.stringMassShift))
    (h_qft_sft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxSftRrDeformation
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxSftRrDeformationCftPackage
        data.qftSft))
    (h_qft_mass : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxMassShiftFromFourPoint
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMassShiftFromFourPointCftPackage
        data.qftMassShift))
    (h_mu_sft : data.stringSft.mu = data.qftSft.mu)
    (h_k_sft : data.stringSft.levelK = data.qftSft.levelK)
    (h_coeff :
      data.stringSft.secondOrderEquationCoefficient = data.qftSft.secondOrderEquationCoefficient)
    (h_mu_mass : data.stringMassShift.mu = data.qftMassShift.mu)
    (h_alpha : data.stringMassShift.alphaPrime = data.qftMassShift.alphaPrime)
    (h_delta_mu :
      data.stringMassShift.scalingDimensionMu = data.qftMassShift.scalingDimensionMu)
    (h_delta_zero :
      data.stringMassShift.scalingDimensionZero = data.qftMassShift.scalingDimensionZero)
    (h_dm2 : data.stringMassShift.massSquaredShift = data.qftMassShift.massSquaredShift)
    (h_a04 : data.stringMassShift.fourPointAmplitude = data.qftMassShift.fourPointAmplitude) :
    AdS3MixedFluxSftMassShiftBridgePackage data := by
  have h_string_sft_pkg : AdS3MixedFluxSftRrDeformationPackage data.stringSft :=
    ads3_mixed_flux_sft_rr_deformation_package data.stringSft h_string_sft
  have h_string_mass_pkg : AdS3MixedFluxMassShiftFromFourPointPackage data.stringMassShift :=
    ads3_mixed_flux_mass_shift_from_four_point_package data.stringMassShift h_string_mass
  have h_qft_sft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxSftRrDeformationCftPackage data.qftSft :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_sft_rr_deformation_cft_package
      data.qftSft h_qft_sft
  have h_qft_mass_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxMassShiftFromFourPointCftPackage
        data.qftMassShift :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_mass_shift_from_four_point_cft_package
      data.qftMassShift h_qft_mass
  exact ⟨h_string_sft_pkg, h_string_mass_pkg, h_qft_sft_pkg, h_qft_mass_pkg,
    h_mu_sft, h_k_sft, h_coeff, h_mu_mass, h_alpha, h_delta_mu, h_delta_zero, h_dm2, h_a04⟩

/-- Cross-lane data for finite-`k` WZW four-point reduction in mixed-flux AdS3. -/
structure AdS3MixedFluxFiniteKWzwReductionBridgeData where
  stringReduction : AdS3MixedFluxFiniteKWzwFourPointReductionData
  qftReduction :
    PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxFiniteKWzwFourPointReductionCftData

/-- Bridge package:
string-side finite-`k` mixed-flux WZW four-point reduction aligned with
QFT-side finite-`k` reduction package. -/
def AdS3MixedFluxFiniteKWzwReductionBridgePackage
    (data : AdS3MixedFluxFiniteKWzwReductionBridgeData) : Prop :=
  AdS3MixedFluxFiniteKWzwFourPointReductionPackage data.stringReduction /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage
    data.qftReduction /\
  data.stringReduction.levelK = data.qftReduction.levelK /\
  data.stringReduction.mu = data.qftReduction.mu /\
  data.stringReduction.slBosonicLevel = data.qftReduction.slBosonicLevel /\
  data.stringReduction.suBosonicLevel = data.qftReduction.suBosonicLevel /\
  data.stringReduction.largeKFiniteNOverKAgreementWithSemiclassical =
    data.qftReduction.largeKFiniteNOverKAgreementWithSemiclassical

/-- Assumed bridge package for finite-`k` WZW four-point reduction data. -/
theorem ads3_mixed_flux_finite_k_wzw_reduction_bridge_package
    (data : AdS3MixedFluxFiniteKWzwReductionBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxFiniteKWzwFourPointReduction
      (AdS3MixedFluxFiniteKWzwFourPointReductionPackage data.stringReduction))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxFiniteKWzwFourPointReduction
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage
        data.qftReduction))
    (h_k : data.stringReduction.levelK = data.qftReduction.levelK)
    (h_mu : data.stringReduction.mu = data.qftReduction.mu)
    (h_sl : data.stringReduction.slBosonicLevel = data.qftReduction.slBosonicLevel)
    (h_su : data.stringReduction.suBosonicLevel = data.qftReduction.suBosonicLevel)
    (h_largek :
      data.stringReduction.largeKFiniteNOverKAgreementWithSemiclassical =
        data.qftReduction.largeKFiniteNOverKAgreementWithSemiclassical) :
    AdS3MixedFluxFiniteKWzwReductionBridgePackage data := by
  have h_string_pkg : AdS3MixedFluxFiniteKWzwFourPointReductionPackage data.stringReduction :=
    ads3_mixed_flux_finite_k_wzw_four_point_reduction_package data.stringReduction h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxFiniteKWzwFourPointReductionCftPackage
        data.qftReduction :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_finite_k_wzw_four_point_reduction_cft_package
      data.qftReduction h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_k, h_mu, h_sl, h_su, h_largek⟩

/-- Cross-lane data for finite-`k` mixed-flux WZW OPE-constant normalization. -/
structure AdS3MixedFluxWzwOpeConstantBridgeData where
  stringOpe : AdS3MixedFluxWzwOpeStructureConstantData
  qftOpe : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWzwOpeStructureConstantCftData

/-- Bridge package:
string-side finite-`k` mixed-flux WZW OPE constants aligned with QFT-side
finite-`k` OPE-constant package. -/
def AdS3MixedFluxWzwOpeConstantBridgePackage
    (data : AdS3MixedFluxWzwOpeConstantBridgeData) : Prop :=
  AdS3MixedFluxWzwOpeStructureConstantPackage data.stringOpe /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWzwOpeStructureConstantCftPackage data.qftOpe /\
  data.stringOpe.levelK = data.qftOpe.levelK /\
  data.stringOpe.cSuHalfHalfOne = data.qftOpe.cSuHalfHalfOne /\
  data.stringOpe.cSlMinusHalfMinusHalfMinusOne = data.qftOpe.cSlMinusHalfMinusHalfMinusOne /\
  data.stringOpe.suIdentityOpeCoefficient = data.qftOpe.suIdentityOpeCoefficient /\
  data.stringOpe.slIdentityOpeCoefficient = data.qftOpe.slIdentityOpeCoefficient /\
  data.stringOpe.cSuLargeKAsymptoticValue = data.qftOpe.cSuLargeKAsymptoticValue /\
  data.stringOpe.cSlLargeKAsymptoticValue = data.qftOpe.cSlLargeKAsymptoticValue

/-- Assumed bridge package for finite-`k` mixed-flux WZW OPE-constant data. -/
theorem ads3_mixed_flux_wzw_ope_constant_bridge_package
    (data : AdS3MixedFluxWzwOpeConstantBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxWzwOpeStructureConstants
      (AdS3MixedFluxWzwOpeStructureConstantPackage data.stringOpe))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxWzwOpeStructureConstants
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWzwOpeStructureConstantCftPackage
        data.qftOpe))
    (h_k : data.stringOpe.levelK = data.qftOpe.levelK)
    (h_c_su : data.stringOpe.cSuHalfHalfOne = data.qftOpe.cSuHalfHalfOne)
    (h_c_sl :
      data.stringOpe.cSlMinusHalfMinusHalfMinusOne = data.qftOpe.cSlMinusHalfMinusHalfMinusOne)
    (h_su_id :
      data.stringOpe.suIdentityOpeCoefficient = data.qftOpe.suIdentityOpeCoefficient)
    (h_sl_id :
      data.stringOpe.slIdentityOpeCoefficient = data.qftOpe.slIdentityOpeCoefficient)
    (h_asym_su :
      data.stringOpe.cSuLargeKAsymptoticValue = data.qftOpe.cSuLargeKAsymptoticValue)
    (h_asym_sl :
      data.stringOpe.cSlLargeKAsymptoticValue = data.qftOpe.cSlLargeKAsymptoticValue) :
    AdS3MixedFluxWzwOpeConstantBridgePackage data := by
  have h_string_pkg : AdS3MixedFluxWzwOpeStructureConstantPackage data.stringOpe :=
    ads3_mixed_flux_wzw_ope_structure_constant_package data.stringOpe h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxWzwOpeStructureConstantCftPackage
        data.qftOpe :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_wzw_ope_structure_constant_cft_package
      data.qftOpe h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_k, h_c_su, h_c_sl, h_su_id, h_sl_id, h_asym_su, h_asym_sl⟩

/-- Cross-lane data for mixed-flux RR-deformation two-string bracket structure. -/
structure AdS3MixedFluxRrTwoStringBracketBridgeData where
  stringBracket : AdS3MixedFluxRrTwoStringBracketData
  qftBracket : PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxRrTwoStringBracketCftData

/-- Bridge package:
string-side and QFT-side explicit mixed-flux RR-deformation two-string-bracket
structures aligned field-by-field. -/
def AdS3MixedFluxRrTwoStringBracketBridgePackage
    (data : AdS3MixedFluxRrTwoStringBracketBridgeData) : Prop :=
  AdS3MixedFluxRrTwoStringBracketPackage data.stringBracket /\
  PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxRrTwoStringBracketCftPackage data.qftBracket /\
  data.stringBracket.levelK = data.qftBracket.levelK /\
  data.stringBracket.mu = data.qftBracket.mu /\
  data.stringBracket.z0Abs = data.qftBracket.z0Abs /\
  data.stringBracket.normalizationN1 = data.qftBracket.normalizationN1 /\
  data.stringBracket.overallCoefficient = data.qftBracket.overallCoefficient /\
  data.stringBracket.cSlMinusHalfMinusHalfMinusOne = data.qftBracket.cSlMinusHalfMinusHalfMinusOne /\
  data.stringBracket.cSuHalfHalfOne = data.qftBracket.cSuHalfHalfOne /\
  data.stringBracket.slPower = data.qftBracket.slPower /\
  data.stringBracket.suPower = data.qftBracket.suPower /\
  data.stringBracket.slRelativeSign = data.qftBracket.slRelativeSign /\
  data.stringBracket.suRelativeSign = data.qftBracket.suRelativeSign /\
  data.stringBracket.projectedZeroWeightVanishesAtFiniteK =
    data.qftBracket.projectedZeroWeightVanishesAtFiniteK

/-- Assumed bridge package for mixed-flux RR-deformation two-string-bracket data. -/
theorem ads3_mixed_flux_rr_two_string_bracket_bridge_package
    (data : AdS3MixedFluxRrTwoStringBracketBridgeData)
    (h_string : PhysicsAssumption
      AssumptionId.stringAdS3MixedFluxRrTwoStringBracketStructure
      (AdS3MixedFluxRrTwoStringBracketPackage data.stringBracket))
    (h_qft : PhysicsAssumption
      AssumptionId.cft2dAds3MixedFluxRrTwoStringBracketStructure
      (PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxRrTwoStringBracketCftPackage
        data.qftBracket))
    (h_k : data.stringBracket.levelK = data.qftBracket.levelK)
    (h_mu : data.stringBracket.mu = data.qftBracket.mu)
    (h_z0 : data.stringBracket.z0Abs = data.qftBracket.z0Abs)
    (h_n1 : data.stringBracket.normalizationN1 = data.qftBracket.normalizationN1)
    (h_coeff : data.stringBracket.overallCoefficient = data.qftBracket.overallCoefficient)
    (h_c_sl :
      data.stringBracket.cSlMinusHalfMinusHalfMinusOne = data.qftBracket.cSlMinusHalfMinusHalfMinusOne)
    (h_c_su : data.stringBracket.cSuHalfHalfOne = data.qftBracket.cSuHalfHalfOne)
    (h_pow_sl : data.stringBracket.slPower = data.qftBracket.slPower)
    (h_pow_su : data.stringBracket.suPower = data.qftBracket.suPower)
    (h_sign_sl : data.stringBracket.slRelativeSign = data.qftBracket.slRelativeSign)
    (h_sign_su : data.stringBracket.suRelativeSign = data.qftBracket.suRelativeSign)
    (h_proj :
      data.stringBracket.projectedZeroWeightVanishesAtFiniteK =
        data.qftBracket.projectedZeroWeightVanishesAtFiniteK) :
    AdS3MixedFluxRrTwoStringBracketBridgePackage data := by
  have h_string_pkg : AdS3MixedFluxRrTwoStringBracketPackage data.stringBracket :=
    ads3_mixed_flux_rr_two_string_bracket_package data.stringBracket h_string
  have h_qft_pkg :
      PhysicsLogic.QFT.CFT.TwoDimensional.AdS3MixedFluxRrTwoStringBracketCftPackage
        data.qftBracket :=
    PhysicsLogic.QFT.CFT.TwoDimensional.ads3_mixed_flux_rr_two_string_bracket_cft_package
      data.qftBracket h_qft
  exact ⟨h_string_pkg, h_qft_pkg, h_k, h_mu, h_z0, h_n1, h_coeff, h_c_sl, h_c_su,
    h_pow_sl, h_pow_su, h_sign_sl, h_sign_su, h_proj⟩

end PhysicsLogic.StringTheory
