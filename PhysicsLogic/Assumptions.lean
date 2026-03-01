namespace PhysicsLogic

/-- Explicit, labeled physics assumption.

`PhysicsAssumption id P` carries no extra proof power; it is definitionally `P`.
Its role is traceability: every non-derived physical premise should have a stable id. -/
abbrev PhysicsAssumption (_id : String) (P : Prop) : Prop := P

/- Stable identifiers for project-level physical assumptions.
   Keep these ids stable so grep/CI history stays meaningful. -/
namespace AssumptionId

def bianchiImpliesConservation : String := "gr.bianchi_implies_conservation"
def perfectFluidEnergyConditions : String := "gr.perfect_fluid_energy_conditions"
def holevoBound : String := "qi.holevo_bound"
def qiArakiLieb : String := "qi.araki_lieb"
def qiKleinInequality : String := "qi.klein_inequality"
def qiSeparableDiscordNonzero : String := "qi.separable_discord_nonzero"
def qiDistillationLessThanFormation : String := "qi.distillation_le_formation"
def qiLoccMonotone : String := "qi.locc_monotone"
def qiLoccPreservesSeparability : String := "qi.locc_preserves_separability"
def qiStrongSubadditivity : String := "qi.strong_subadditivity"
def qiNoCloning : String := "qi.no_cloning"
def qiNoDeleting : String := "qi.no_deleting"
def qiNoBroadcasting : String := "qi.no_broadcasting"
def quantumPureToDensityAxioms : String := "quantum.pure_to_density_axioms"
def quantumUnitaryPreservesNorm : String := "quantum.unitary_preserves_norm"
def quantumExpectationReal : String := "quantum.expectation_real"
def quantumPauliDirectionObservable : String := "quantum.pauli_direction_observable"
def quantumSingletPauliCorrelation : String := "quantum.singlet_pauli_correlation"
def brstExactImpliesClosed : String := "qft.bv.brst.exact_implies_closed"
def brstGaugeFixedInvariant : String := "qft.bv.brst.gauge_fixed_invariant"
def brstGaugeFixingDifferenceExact : String := "qft.bv.brst.gauge_fixing_difference_exact"
def pathIntegralDiscretizedContinuumLimit : String :=
  "qft.path_integral.discretized_continuum_limit"
def pathIntegralInstantonSemiclassicalWeight : String :=
  "qft.path_integral.instanton_semiclassical_weight"
def pathIntegralWittenIndexMorseComplex : String :=
  "qft.path_integral.witten_index_morse_complex"
def pathIntegralBorelSokalWatsonCriterion : String :=
  "qft.path_integral.borel_sokal_watson_criterion"
def pathIntegralLefschetzThimbleExpansion : String :=
  "qft.path_integral.lefschetz_thimble_expansion"
def qftAnomalyAxial2dCurrentDivergence : String :=
  "qft.anomaly.axial_2d_current_divergence"
def qftAnomalyAxial4dCurrentDivergence : String :=
  "qft.anomaly.axial_4d_current_divergence"
def qftAnomalyGaugeU1ChiralVariation : String :=
  "qft.anomaly.gauge_u1_chiral_variation"
def qftAnomalyGaugeU1CubicCoefficient : String :=
  "qft.anomaly.gauge_u1_cubic_coefficient"
def qftAnomalyGaugeU1CountertermShift : String :=
  "qft.anomaly.gauge_u1_counterterm_shift"
def qftAnomalyGaugeDescentRelations : String :=
  "qft.anomaly.gauge_descent_relations"
def qftAnomalyGaugeChiralFermionPolynomial : String :=
  "qft.anomaly.gauge_chiral_fermion_polynomial"
def qftAnomalyGravitationalDescent4kPlus2 : String :=
  "qft.anomaly.gravitational_descent_4k_plus_2"
def qftAnomalyGravitationalAhatPolynomial : String :=
  "qft.anomaly.gravitational_ahat_polynomial"
def qftAnomalyGravitationalD10MwPolynomial : String :=
  "qft.anomaly.gravitational_d10_mw_polynomial"
def bvDifferentialNilpotent : String := "qft.bv.differential_nilpotent"
def bvDifferentialNZero : String := "qft.bv.differential_n_zero"
def bvGaugeIndependence : String := "qft.bv.gauge_independence"
def bvFaddeevPopovGaugeSliceRegular : String :=
  "qft.bv.faddeev_popov_gauge_slice_regular"
def bvMasterEquationClosureHierarchy : String :=
  "qft.bv.master_equation_closure_hierarchy"
def bvGaugeFixingFermionRecoversBrst : String :=
  "qft.bv.gauge_fixing_fermion_recovers_brst"
def bvWilsonianMasterEquationPreserved : String :=
  "qft.bv.wilsonian_master_equation_preserved"
def tqftModularRelation : String := "qft.tqft.modular_relation"
def tqftZ3ModularAxioms : String := "qft.tqft.z3_modular_axioms"
def tqftSu24FusionAxioms : String := "qft.tqft.su24_fusion_axioms"
def tqftSu24RibbonAxioms : String := "qft.tqft.su24_ribbon_axioms"
def tqftIsingModularAxioms : String := "qft.tqft.ising_modular_axioms"
def osReconstruction : String := "euclidean.os_reconstruction"
def ghsInequality : String := "euclidean.ghs_inequality"
def qftEuclideanMqmCanonicalCommutation : String :=
  "qft.euclidean.mqm.canonical_commutation"
def qftEuclideanMqmSingletReduction : String :=
  "qft.euclidean.mqm.singlet_reduction"
def qftEuclideanMqmCOneInvertedPotential : String :=
  "qft.euclidean.mqm.c1_inverted_potential"
def qftEuclideanMqmFermiSeaProfile : String :=
  "qft.euclidean.mqm.fermi_sea_profile"
def qftEuclideanMqmCollectiveTauHamiltonian : String :=
  "qft.euclidean.mqm.collective_tau_hamiltonian"
def qftEuclideanMqmCollectiveBornOneToTwo : String :=
  "qft.euclidean.mqm.collective_born_1to2"
def qftEuclideanMqmReflectionHoleRelation : String :=
  "qft.euclidean.mqm.reflection_hole_relation"
def qftEuclideanMqmInstantonOneToN : String :=
  "qft.euclidean.mqm.instanton_1ton"
def qftEuclideanMqmLongStringRenormalizedEnergy : String :=
  "qft.euclidean.mqm.long_string_renormalized_energy"
def qftEuclideanMqmLongStringIntegralEquation : String :=
  "qft.euclidean.mqm.long_string_integral_equation"
def wilsonianIrrelevantSuppression : String := "rg.wilsonian.irrelevant_suppression"
def qcdAsymptoticFreedom : String := "rg.gellmannlow.qcd_asymptotic_freedom"
def lorentzPreservesTimelike : String := "spacetime.lorentz_preserves_timelike"
def lorentzPreservesSpacelike : String := "spacetime.lorentz_preserves_spacelike"
def lorentzPreservesLightlike : String := "spacetime.lorentz_preserves_lightlike"
def lorentzBoostPreservesMetric : String := "spacetime.lorentz_boost_preserves_metric"
def spatialRotationPreservesMetric : String := "spacetime.spatial_rotation_preserves_metric"
def metricPerturbationWellFormed : String := "gr.metric_perturbation_well_formed"
def reissnerNordstromMetricWellFormed : String := "gr.reissner_nordstrom_metric_well_formed"
def flrwMetricWellFormed : String := "gr.flrw_metric_well_formed"
def lorentzComposePreservesMetric : String := "sym.lorentz.compose_preserves_metric"
def lorentzInversePreservesMetric : String := "sym.lorentz.inverse_preserves_metric"
def lorentzGroupMulAssoc : String := "sym.lorentz.group.mul_assoc"
def lorentzGroupOneMul : String := "sym.lorentz.group.one_mul"
def lorentzGroupMulOne : String := "sym.lorentz.group.mul_one"
def lorentzGroupInvMulCancel : String := "sym.lorentz.group.inv_mul_cancel"
def poincareGroupMulAssoc : String := "sym.poincare.group.mul_assoc"
def poincareGroupOneMul : String := "sym.poincare.group.one_mul"
def poincareGroupMulOne : String := "sym.poincare.group.mul_one"
def poincareGroupInvMulCancel : String := "sym.poincare.group.inv_mul_cancel"
def symSpinorCliffordAlgebraRelation : String := "sym.spinor.clifford_algebra_relation"
def symSpinorEvenCliffordFockRelation : String := "sym.spinor.even_clifford_fock_relation"
def symSpinorChiralityEigenspaceDimensions : String :=
  "sym.spinor.chirality_eigenspace_dimensions"
def symSpinorMajoranaAdmissibleEven : String := "sym.spinor.majorana_admissible_even"
def symSpinorMajoranaWeylAdmissible : String := "sym.spinor.majorana_weyl_admissible"
def symSpinorChargeConjugationRelation : String :=
  "sym.spinor.charge_conjugation_relation"
def symSpinorSo19ConventionPackage : String := "sym.spinor.so19_convention_package"
def symSpinorSo13ConventionPackage : String := "sym.spinor.so13_convention_package"
def symSpinorSo12ConventionPackage : String := "sym.spinor.so12_convention_package"
def symSpinorEuclideanD8TrialityRelations : String :=
  "sym.spinor.euclidean_d8_triality_relations"
def symSpinorEuclideanD6Su4GammaIdentity : String :=
  "sym.spinor.euclidean_d6_su4_gamma_identity"
def symSuperPoincareAlgebra : String := "sym.super_poincare.algebra"
def symSuperPoincareMasslessMultipletDimension : String :=
  "sym.super_poincare.massless_multiplet_dimension"
def symSuperPoincareBpsBound : String := "sym.super_poincare.bps_bound"
def symSuperspaceN1Algebra4d : String := "sym.superspace.n1_algebra_4d"
def symSuperspaceN1ChiralConstraint : String := "sym.superspace.n1_chiral_constraint"
def symSuperspaceN1VectorFieldStrengthGaugeInvariant : String :=
  "sym.superspace.n1_vector_field_strength_gauge_invariant"
def qftSusyN1HolomorphicOneLoopBeta : String := "qft.susy.n1.holomorphic_one_loop_beta"
def qftSusyN1NsvzBetaRelation : String := "qft.susy.n1.nsvz_beta_relation"
def qftSusyN2PrepotentialConstraints : String := "qft.susy.n2.prepotential_constraints"
def qftSusy3dN2SigmaDtermRelation : String := "qft.susy.3d.n2.sigma_dterm_relation"
def qftSusy3dN3QuarticSuperpotential : String :=
  "qft.susy.3d.n3.quartic_superpotential"
def schwarzschildMetricWellFormed : String := "gr.schwarzschild_metric_well_formed"
def conformalPreservesNull : String := "spacetime.conformal_preserves_null"
def conformalPreservesCausalStructure : String := "spacetime.conformal_preserves_causal_structure"
def cftCrossRatiosPositiveFromPoints : String := "qft.cft.cross_ratios_positive_from_points"
def cftTDualWeightSymmetry : String := "qft.cft.2d.t_dual_weight_symmetry"
def cft2dIsingSigmaFourPointCrossing : String :=
  "qft.cft.2d.ising_sigma_four_point_crossing"
def cft2dDefectFusionPentagon : String := "qft.cft.2d.defect_fusion_pentagon"
def cft2dOrbifoldConstructionModularInvariant : String :=
  "qft.cft.2d.orbifold_construction_modular_invariant"
def cft2dNarainEvenSelfDualModularInvariant : String :=
  "qft.cft.2d.narain_even_self_dual_modular_invariant"
def cft2dNarainCocycleAssociative : String :=
  "qft.cft.2d.narain_cocycle_associative"
def cft2dNlsmWeylAnomalyVanishing : String :=
  "qft.cft.2d.nlsm_weyl_anomaly_vanishing"
def cft2dBuscherRules : String := "qft.cft.2d.buscher_rules"
def cft2dGaugedWzwCosetFlow : String := "qft.cft.2d.gauged_wzw_coset_flow"
def cft2dLiouvilleMarginality : String := "qft.cft.2d.liouville_marginality"
def cft2dLiouvilleDozzRecursion : String := "qft.cft.2d.liouville_dozz_recursion"
def cft2dSuperspace11DerivativeAlgebra : String :=
  "qft.cft.2d.superspace_11_derivative_algebra"
def cft2dN1SuperconformalAlgebra : String :=
  "qft.cft.2d.n1_superconformal_algebra"
def cft2dSuperspace22ChiralReduction : String :=
  "qft.cft.2d.superspace_22_chiral_reduction"
def cft2dN2SuperconformalAlgebra : String :=
  "qft.cft.2d.n2_superconformal_algebra"
def cft2dN2SpectralFlowAutomorphism : String :=
  "qft.cft.2d.n2_spectral_flow_automorphism"
def cft2dN4SmallSuperconformalAlgebra : String :=
  "qft.cft.2d.n4_small_superconformal_algebra"
def cft2dN4SpectralFlowInnerAutomorphism : String :=
  "qft.cft.2d.n4_spectral_flow_inner_automorphism"
def cft2dLandauGinzburgMinimalModelFlow : String :=
  "qft.cft.2d.landau_ginzburg_minimal_model_flow"
def cft2dN2LandauGinzburgNonRenormalization : String :=
  "qft.cft.2d.n2_landau_ginzburg_nonrenormalization"
def cft2dGlsmAxialAnomalyThetaShift : String :=
  "qft.cft.2d.glsm_axial_anomaly_theta_shift"
def cft2dGlsmTwistedSuperpotentialOneLoop : String :=
  "qft.cft.2d.glsm_twisted_superpotential_one_loop"
def cft2dCalabiYauLandauGinzburgPhaseFlow : String :=
  "qft.cft.2d.calabi_yau_landau_ginzburg_phase_flow"
def cft2dAbelianDualityTwistedSuperpotentialMatch : String :=
  "qft.cft.2d.abelian_duality_twisted_superpotential_match"
def cft2dCigarLiouvilleMirrorDuality : String :=
  "qft.cft.2d.cigar_liouville_mirror_duality"
def cft2dBoundaryConformalInvariance : String :=
  "qft.cft.2d.boundary_conformal_invariance"
def cft2dBoundaryCorrelatorKinematics : String :=
  "qft.cft.2d.boundary_correlator_kinematics"
def cft2dBoundaryStateIshibashiGluing : String :=
  "qft.cft.2d.boundary_state_ishibashi_gluing"
def cft2dBoundaryBulkBoundaryOnePoint : String :=
  "qft.cft.2d.boundary_bulk_boundary_one_point"
def cft2dBoundaryCylinderModularDuality : String :=
  "qft.cft.2d.boundary_cylinder_modular_duality"
def cft2dBoundaryChanPatonFactorization : String :=
  "qft.cft.2d.boundary_chan_paton_factorization"
def cft2dBoundaryFreeBosonNdConditions : String :=
  "qft.cft.2d.boundary_free_boson_nd_conditions"
def cft2dBoundaryFreeBosonNormalization : String :=
  "qft.cft.2d.boundary_free_boson_normalization"
def cft2dBoundaryFreeFermionNdConditions : String :=
  "qft.cft.2d.boundary_free_fermion_nd_conditions"
def cft2dBoundaryFreeFermionCoefficients : String :=
  "qft.cft.2d.boundary_free_fermion_coefficients"
def cft2dBoundaryFreeFermionSectorIdentification : String :=
  "qft.cft.2d.boundary_free_fermion_sector_identification"
def grSupergravityCurvedSpinorGeometry : String := "gr.supergravity.curved_spinor_geometry"
def grSupergravity11dCorePackage : String := "gr.supergravity.11d_core_package"
def stringSupergravityTypeIIAFormRelations : String :=
  "string.supergravity.type_iia_form_relations"
def stringSupergravityTypeIIBPseudoActionConstraints : String :=
  "string.supergravity.type_iib_pseudo_action_constraints"
def stringSupergravityTypeIGreenSchwarzHatH : String :=
  "string.supergravity.type_i_green_schwarz_hat_h"
def grSupergravityN2SpecialKahlerPotential : String :=
  "gr.supergravity.n2.special_kahler_potential"
def grSupergravityN2QuaternionicRicciRelation : String :=
  "gr.supergravity.n2.quaternionic_ricci_relation"
def grSupergravityN2GaugedScalarPotential : String :=
  "gr.supergravity.n2.gauged_scalar_potential"
def grSupergravityN1GaugeAndPotentialPackage : String :=
  "gr.supergravity.n1.gauge_and_potential_package"
def lszKleinGordonOperatorExists : String := "qft.smatrix.lsz.klein_gordon_operator_exists"
def lszReductionFormula : String := "qft.smatrix.lsz.reduction_formula"
def haagRuelleEqualsLsz : String := "qft.smatrix.haag_ruelle_equals_lsz"
def wightmanPctTheorem : String := "qft.wightman.pct_theorem"
def wightmanSpinStatistics : String := "qft.wightman.spin_statistics"
def wightmanHaagTheorem : String := "qft.wightman.haag_theorem"
def wightmanReehSchlieder : String := "qft.wightman.reeh_schlieder"
def wightmanTemperedness : String := "qft.wightman.temperedness"
def aqftGnsExistence : String := "qft.aqft.gns_existence"
def aqftReehSchlieder : String := "qft.aqft.reeh_schlieder"
def aqftHaagTheorem : String := "qft.aqft.haag_theorem"
def aqftTomitaTakesaki : String := "qft.aqft.tomita_takesaki"
def aqftBisognanoWichmann : String := "qft.aqft.bisognano_wichmann"
def aqftBoseFermiAlternative : String := "qft.aqft.bose_fermi_alternative"
def aqftAnyonsIn3d : String := "qft.aqft.anyons_in_3d"
def aqftDoplicherRobertsReconstruction : String := "qft.aqft.doplicher_roberts_reconstruction"
def aqftSpinStatistics : String := "qft.aqft.spin_statistics"
def stringPrologueWeinbergWittenNoLocalStressTensor : String :=
  "string.prologue.weinberg_witten_no_local_stress_tensor"
def stringPrologueLargeNYmWeaklyCoupledFluxStrings : String :=
  "string.prologue.large_n_ym_weakly_coupled_flux_strings"
def stringEffectiveNgPolyakovEquivalence : String := "string.effective.ng_polyakov_equivalence"
def stringEffectiveReggeTrajectory : String := "string.effective.regge_trajectory"
def stringBosonicCriticalDimension : String := "string.bosonic.critical_dimension_26"
def stringBosonicBrstPhysicalStatesCohomology : String :=
  "string.bosonic.brst_physical_states_cohomology"
def stringBosonicSiegelImpliesLevelMatching : String :=
  "string.bosonic.siegel_implies_level_matching"
def stringBosonicMassSpectrumFormula : String := "string.bosonic.mass_spectrum_formula"
def stringSuperstringPolyakovGaugePackage : String := "string.superstring.polyakov_gauge_package"
def stringSuperstringGhostSystemPackage : String := "string.superstring.ghost_system_package"
def stringSuperstringPictureNumberPackage : String := "string.superstring.picture_number_package"
def stringSuperstringTypeIIGsoProjection : String := "string.superstring.type_ii_gso_projection"
def stringSuperstringBrstCurrentPackage : String := "string.superstring.brst_current_package"
def stringSuperstringBrstNilpotencyCritical : String := "string.superstring.brst_nilpotency_critical"
def stringSuperstringSiegelConstraintPackage : String := "string.superstring.siegel_constraint_package"
def stringSuperstringPhysicalCohomologyPackage : String := "string.superstring.physical_cohomology_package"
def stringSuperstringOcqRepresentativePackage : String := "string.superstring.ocq_representative_package"
def stringSuperstringMassSpectrumPackage : String := "string.superstring.mass_spectrum_package"
def stringSuperstringMasslessSectorPackage : String := "string.superstring.massless_sector_package"
def stringSuperstringSpacetimeSusyAlgebra : String := "string.superstring.spacetime_susy_algebra"
def stringBackgroundWeylBetaVanishing : String := "string.background.weyl_beta_vanishing"
def stringBackgroundBetaToSpacetimeEom : String := "string.background.beta_to_spacetime_eom"
def stringBackgroundCOneTachyonMassless : String := "string.background.c1_tachyon_massless"
def stringSuperBackgroundNsrHilbertGsoDecomposition : String :=
  "string.super_background.nsr_hilbert_gso_decomposition"
def stringSuperBackgroundNsnsScftDeformation : String :=
  "string.super_background.nsns_scft_deformation"
def stringSuperBackgroundNsnsNlsmSuperspaceAction : String :=
  "string.super_background.nsns_nlsm_superspace_action"
def stringSuperBackgroundNsnsTreeEffectiveAction : String :=
  "string.super_background.nsns_tree_effective_action"
def stringSuperBackgroundCalabiYau22Structure : String :=
  "string.super_background.calabi_yau_22_structure"
def stringSuperBackgroundCalabiYauRicciFlatTopForm : String :=
  "string.super_background.calabi_yau_ricci_flat_top_form"
def stringSuperBackgroundCalabiYauInstantonBFieldPhase : String :=
  "string.super_background.calabi_yau_instanton_bfield_phase"
def stringSuperBackgroundGreenSchwarzKappaSymmetry : String :=
  "string.super_background.green_schwarz_kappa_symmetry"
def stringSuperBackgroundLightConeGaugeSpectrum : String :=
  "string.super_background.light_cone_gauge_spectrum"
def stringSuperBackgroundSuperspaceTorsionHConstraints : String :=
  "string.super_background.superspace_torsion_h_constraints"
def stringAnomalyTypeIibCancellation : String :=
  "string.anomaly.type_iib_cancellation"
def stringAnomalyTypeIHeteroticFactorization : String :=
  "string.anomaly.type_i_heterotic_factorization"
def stringAnomalyGreenSchwarzCancellation : String :=
  "string.anomaly.green_schwarz_cancellation"
def stringHolographyScalarBoundaryCondition : String :=
  "string.holography.scalar_boundary_condition"
def stringHolographyScalarTwoPointFunction : String :=
  "string.holography.scalar_two_point_function"
def stringHolographyGaugeCurrentDictionary : String :=
  "string.holography.gauge_current_dictionary"
def stringHolographyGravityStressTensorDictionary : String :=
  "string.holography.gravity_stress_tensor_dictionary"
def stringHolographyRegulatedGravityAction : String :=
  "string.holography.regulated_gravity_action"
def stringHolographyWittenCubicThreePoint : String :=
  "string.holography.witten_cubic_three_point"
def stringHolographyMellinConstraints : String :=
  "string.holography.mellin_constraints"
def stringHolographyMellinContactAmplitudeUnity : String :=
  "string.holography.mellin_contact_amplitude_unity"
def stringHolographyMellinExchangePoleSeries : String :=
  "string.holography.mellin_exchange_pole_series"
def stringHolographyMellinFlatSpaceLimit : String :=
  "string.holography.mellin_flat_space_limit"
def stringAdSCftD3DecouplingLimit : String := "string.adscft.d3_decoupling_limit"
def stringAdSCftParameterMap : String := "string.adscft.parameter_map"
def stringAdSCftN4SymConformalPackage : String :=
  "string.adscft.n4sym_conformal_package"
def stringAdSCftCoulombBranchVacuumPackage : String :=
  "string.adscft.coulomb_branch_vacuum_package"
def stringAdSCftProbeD3CoulombMatching : String :=
  "string.adscft.probe_d3_coulomb_matching"
def stringAdSCftPoincareGlobalCoordinateMap : String :=
  "string.adscft.poincare_global_coordinate_map"
def stringAdSCftStateOperatorMap : String := "string.adscft.state_operator_map"
def stringAdSCftDictionary : String := "string.adscft.dictionary"
def stringAdSCftSupergravitonChiralPrimaries : String :=
  "string.adscft.supergraviton_chiral_primaries"
def stringAdSCftMassiveStringScaling : String :=
  "string.adscft.massive_string_scaling"
def stringAdSCftSpinningStringTwist : String :=
  "string.adscft.spinning_string_twist"
def stringAdSCftGiantGravitonDuality : String :=
  "string.adscft.giant_graviton_duality"
def stringAdSCftHawkingPageTransition : String :=
  "string.adscft.hawking_page_transition"
def stringAdSCftThermalStrongCoupling : String :=
  "string.adscft.thermal_strong_coupling"
def stringMTheoryM2NearHorizonPackage : String :=
  "string.mtheory.m2_near_horizon_package"
def stringMTheoryM5NearHorizonPackage : String :=
  "string.mtheory.m5_near_horizon_package"
def stringMTheoryD2GaugeCouplingRelation : String :=
  "string.mtheory.d2_gauge_coupling_relation"
def stringMTheoryN8SymIrFixedPointPackage : String :=
  "string.mtheory.n8sym_ir_fixed_point_package"
def stringMTheoryN8SymCoulombBranchSU2 : String :=
  "string.mtheory.n8sym_coulomb_branch_su2"
def stringMTheoryN8SymCoulombBranchUN : String :=
  "string.mtheory.n8sym_coulomb_branch_un"
def stringMTheoryAbjmLevelQuantization : String :=
  "string.mtheory.abjm_level_quantization"
def stringMTheoryAbjmAdS4OrbifoldDuality : String :=
  "string.mtheory.abjm_ads4_orbifold_duality"
def stringMTheoryAbjmVacuumModuliSpace : String :=
  "string.mtheory.abjm_vacuum_moduli_space"
def stringMTheoryAbjmKOneTwoEnhancement : String :=
  "string.mtheory.abjm_k1_k2_enhancement"
def stringMTheorySixD02SuperconformalMultiplets : String :=
  "string.mtheory.6d_02_superconformal_multiplets"
def stringMTheorySixD02ToFiveDCompactification : String :=
  "string.mtheory.6d_02_to_5d_compactification"
def stringMTheorySixD02VacuumModuli : String :=
  "string.mtheory.6d_02_vacuum_moduli"
def stringAdS3D1D5InstantonChargeMap : String :=
  "string.ads3.d1d5_instanton_charge_map"
def stringAdS3D1D5BranchStructure : String :=
  "string.ads3.d1d5_branch_structure"
def stringAdS3D1D5InstantonModuliDimension : String :=
  "string.ads3.d1d5_instanton_moduli_dimension"
def stringAdS3D1D5NearHorizonGeometry : String :=
  "string.ads3.d1d5_near_horizon_geometry"
def stringAdS3D1D5CentralCharge : String :=
  "string.ads3.d1d5_central_charge"
def stringAdS3D1D5ConformalManifoldUduality : String :=
  "string.ads3.d1d5_conformal_manifold_uduality"
def stringAdS3D1D5SymmetricOrbifoldLocus : String :=
  "string.ads3.d1d5_symmetric_orbifold_locus"
def stringAdS3BosonicWzwLevelRadius : String :=
  "string.ads3.bosonic_wzw_level_radius"
def stringAdS3BosonicSpectralFlow : String :=
  "string.ads3.bosonic_spectral_flow"
def stringAdS3BosonicPhysicalSpectrum : String :=
  "string.ads3.bosonic_physical_spectrum"
def stringAdS3BosonicMassShell : String :=
  "string.ads3.bosonic_mass_shell"
def stringAdS3NsnsSuperstringWorldsheet : String :=
  "string.ads3.nsns_superstring_worldsheet"
def stringAdS3NsnsSuperstringMassShell : String :=
  "string.ads3.nsns_superstring_mass_shell"
def stringAdS3MixedFluxParameterization : String :=
  "string.ads3.mixed_flux_parameterization"
def stringAdS3MixedFluxPulsatingShift : String :=
  "string.ads3.mixed_flux_pulsating_shift"
def stringAdS5IntegrabilityOneLoopSpinChain : String :=
  "string.ads5_integrability.one_loop_spin_chain"
def stringAdS5IntegrabilitySingleMagnonDispersion : String :=
  "string.ads5_integrability.single_magnon_dispersion"
def stringAdS5IntegrabilityHeisenbergBetheRoots : String :=
  "string.ads5_integrability.heisenberg_bethe_roots"
def stringAdS5IntegrabilityBmnPpWaveMap : String :=
  "string.ads5_integrability.bmn_pp_wave_map"
def stringAdS5IntegrabilityPpWaveSpectrum : String :=
  "string.ads5_integrability.pp_wave_spectrum"
def stringAdS5IntegrabilityMagnonDispersion : String :=
  "string.ads5_integrability.magnon_dispersion"
def stringAdS5IntegrabilityWeakCouplingMap : String :=
  "string.ads5_integrability.weak_coupling_map"
def stringAdS5IntegrabilityZhukovskyVariables : String :=
  "string.ads5_integrability.zhukovsky_variables"
def stringAdS5IntegrabilitySMatrixConsistency : String :=
  "string.ads5_integrability.s_matrix_consistency"
def stringAdS5IntegrabilityCuspBesEquation : String :=
  "string.ads5_integrability.cusp_bes_equation"
def stringAdS5IntegrabilityCuspStrongCoupling : String :=
  "string.ads5_integrability.cusp_strong_coupling"
def stringAdS5IntegrabilityBetheYangSystem : String :=
  "string.ads5_integrability.bethe_yang_system"
def stringAdS5IntegrabilityBoundStateDispersion : String :=
  "string.ads5_integrability.bound_state_dispersion"
def stringAdS5MirrorDoubleWickMap : String :=
  "string.ads5_mirror.double_wick_map"
def stringAdS5MirrorMagnonDispersion : String :=
  "string.ads5_mirror.magnon_dispersion"
def stringAdS5MirrorSingleSpeciesTba : String :=
  "string.ads5_mirror.single_species_tba"
def stringAdS5MirrorExcitedStateQuantization : String :=
  "string.ads5_mirror.excited_state_quantization"
def stringAdS5MirrorBetheYangSystem : String :=
  "string.ads5_mirror.bethe_yang_system"
def stringAdS5MirrorBetheStrings : String :=
  "string.ads5_mirror.bethe_strings"
def stringAdS5MirrorTbaEquationSystem : String :=
  "string.ads5_mirror.tba_equation_system"
def stringAdS5MirrorYSystemHirota : String :=
  "string.ads5_mirror.y_system_hirota"
def stringAdS5MirrorFiniteVolumeEnergy : String :=
  "string.ads5_mirror.finite_volume_energy"
def stringAdS5MirrorKonishiWrapping : String :=
  "string.ads5_mirror.konishi_wrapping"
def stringAdS5MirrorQuantumSpectralCurvePMu : String :=
  "string.ads5_mirror.quantum_spectral_curve_pmu"
def stringAdS5MirrorPMuAsymptotics : String :=
  "string.ads5_mirror.pmu_asymptotics"
def stringAdS5MirrorWeakCouplingBaxter : String :=
  "string.ads5_mirror.weak_coupling_baxter"
def stringAdS5MirrorSmallSpinExpansion : String :=
  "string.ads5_mirror.small_spin_expansion"
def stringWilsonMaldacenaLoopSaddle : String :=
  "string.wilson.maldacena_loop_saddle"
def stringWilsonQuarkAntiquarkPotentialStrongCoupling : String :=
  "string.wilson.quark_antiquark_potential_strong_coupling"
def stringWilsonCuspLargeAngleRelation : String :=
  "string.wilson.cusp_large_angle_relation"
def stringWilsonBremsstrahlungFunction : String :=
  "string.wilson.bremsstrahlung_function"
def stringWittenConfinementCircleData : String :=
  "string.holo_qcd.witten_confinement_circle_data"
def stringWittenConfiningStringTension : String :=
  "string.holo_qcd.witten_confining_string_tension"
def stringSakaiSugimotoChiralSymmetryBreaking : String :=
  "string.holo_qcd.sakai_sugimoto_chiral_symmetry_breaking"
def stringSakaiSugimotoPionSkyrmeAction : String :=
  "string.holo_qcd.sakai_sugimoto_pion_skyrme_action"
def stringSakaiSugimotoEtaPrimeMass : String :=
  "string.holo_qcd.sakai_sugimoto_eta_prime_mass"
def stringSakaiSugimotoMesonSpectrum : String :=
  "string.holo_qcd.sakai_sugimoto_meson_spectrum"
def stringKlebanovWittenMarginalConifoldData : String :=
  "string.conifold.klebanov_witten_marginal_conifold_data"
def stringKlebanovWittenAdS5T11Duality : String :=
  "string.conifold.klebanov_witten_ads5_t11_duality"
def stringKlebanovTseytlinFluxRunning : String :=
  "string.conifold.klebanov_tseytlin_flux_running"
def stringKlebanovCascadeSeibergDualStep : String :=
  "string.conifold.klebanov_cascade_seiberg_dual_step"
def stringKlebanovStrasslerConfinement : String :=
  "string.conifold.klebanov_strassler_confinement"
def stringMatrixBfssUpliftParameters : String :=
  "string.matrix.bfss_uplift_parameters"
def stringMatrixBfssNearHorizonDuality : String :=
  "string.matrix.bfss_near_horizon_duality"
def stringMatrixBfssBlackHoleThermodynamics : String :=
  "string.matrix.bfss_black_hole_thermodynamics"
def stringMatrixBfssMicrocanonicalEntropyScaling : String :=
  "string.matrix.bfss_microcanonical_entropy_scaling"
def stringMatrixBfssMomentumMap : String :=
  "string.matrix.bfss_momentum_map"
def stringMatrixBfssSmatrixConjecture : String :=
  "string.matrix.bfss_smatrix_conjecture"
def stringMatrixGaugeCouplingDuality : String := "string.matrix.gauge_coupling_duality"
def stringMatrixSymmetricOrbifoldIrLimit : String := "string.matrix.symmetric_orbifold_ir_limit"
def stringMatrixDvvTwistDeformation : String := "string.matrix.dvv_twist_deformation"
def stringMatrixDvvCoefficientNormalization : String := "string.matrix.dvv_coefficient_normalization"
def stringMatrixTreeAmplitudeMatching : String := "string.matrix.tree_amplitude_matching"
def stringMatrixStringConjectureLargeN : String := "string.matrix.string_conjecture_large_n"
def stringConventionsBosonicNormalizationPackage : String := "string.conventions.bosonic_normalization_package"
def stringConventionsGravitationalCouplingRelations : String := "string.conventions.gravitational_coupling_relations"
def stringConventionsBosonicDpTensionRelations : String := "string.conventions.bosonic_dp_tension_relations"
def stringConventionsTypeIIDpTensionRelation : String := "string.conventions.type_ii_dp_tension_relation"
def stringConventionsTypeIIDimensionlessCouplings : String := "string.conventions.type_ii_dimensionless_couplings"
def stringConventionsMTheoryScaleTensionRelations : String := "string.conventions.m_theory_scale_tension_relations"
def stringPerturbativeGaugeFixedModuliAmplitude : String := "string.perturbative.gauge_fixed_moduli_amplitude"
def stringPerturbativeBeltramiBInsertion : String := "string.perturbative.beltrami_b_insertion"
def stringPerturbativeGhostNumberAnomaly : String := "string.perturbative.ghost_number_anomaly"
def stringPerturbativeBrstBoundaryVariation : String := "string.perturbative.brst_boundary_variation"
def stringPerturbativePlumbingFixtureDegeneration : String := "string.perturbative.plumbing_fixture_degeneration"
def stringPerturbativeTreeUnitarityFactorization : String := "string.perturbative.tree_unitarity_factorization"
def stringPerturbativeNormalizationRecursion : String := "string.perturbative.normalization_recursion"
def stringPerturbativeVirasoroShapiroKernel : String := "string.perturbative.virasoro_shapiro_kernel"
def stringPerturbativeOneLoopTorusMeasure : String := "string.perturbative.one_loop_torus_measure"
def stringPerturbativeCOneThermalDuality : String := "string.perturbative.c_one_thermal_duality"
def stringSuperPerturbativeGaugeFixingSupermoduli : String :=
  "string.super_perturbative.gauge_fixing_supermoduli"
def stringSuperPerturbativeSrsReparameterization : String :=
  "string.super_perturbative.srs_reparameterization"
def stringSuperPerturbativeOddModuliCounting : String :=
  "string.super_perturbative.odd_moduli_counting"
def stringSuperPerturbativeBerezinianIntegration : String :=
  "string.super_perturbative.berezinian_integration"
def stringSuperPerturbativePlumbingFactorization : String :=
  "string.super_perturbative.plumbing_factorization"
def stringSuperPerturbativePcoFormalism : String :=
  "string.super_perturbative.pco_formalism"
def stringSuperPerturbativeSpuriousSingularityControl : String :=
  "string.super_perturbative.spurious_singularity_control"
def stringSuperPerturbativeVerticalIntegration : String :=
  "string.super_perturbative.vertical_integration"
def stringSuperExplicitTreeLevelPcoAmplitude : String :=
  "string.super_explicit.tree_level_pco_amplitude"
def stringSuperExplicitNsnsPictureRaising : String :=
  "string.super_explicit.nsns_picture_raising"
def stringSuperExplicitNsnsThreePointSupergravity : String :=
  "string.super_explicit.nsns_three_point_supergravity"
def stringSuperExplicitNsnsFourPointTreeKernel : String :=
  "string.super_explicit.nsns_four_point_tree_kernel"
def stringSuperExplicitFourPointLowEnergyExpansion : String :=
  "string.super_explicit.four_point_low_energy_expansion"
def stringSuperExplicitRrFourPointTreeKernel : String :=
  "string.super_explicit.rr_four_point_tree_kernel"
def stringSuperExplicitOneLoopNsnsSpinStructure : String :=
  "string.super_explicit.one_loop_nsns_spin_structure"
def stringSuperExplicitOneLoopNsnsVanishingLowMultiplicity : String :=
  "string.super_explicit.one_loop_nsns_vanishing_low_multiplicity"
def stringSuperExplicitOneLoopNsnsFourPointLeading : String :=
  "string.super_explicit.one_loop_nsns_four_point_leading"
def stringSuperExplicitOneLoopRrFourPoint : String :=
  "string.super_explicit.one_loop_rr_four_point"
def stringSuperExplicitHigherGenusGhostCorrelators : String :=
  "string.super_explicit.higher_genus_ghost_correlators"
def stringSuperExplicitHigherLoopVacuumVanishing : String :=
  "string.super_explicit.higher_loop_vacuum_vanishing"
def stringSuperExplicitFourGravitonCouplingFunction : String :=
  "string.super_explicit.four_graviton_coupling_function"
def stringSftClosedFieldSpaceHZero : String := "string.sft.closed_field_space_h_zero"
def stringSftOffShellAmplitudeCycle : String := "string.sft.off_shell_amplitude_cycle"
def stringSftBrstExteriorDerivativeIdentity : String := "string.sft.brst_exterior_derivative_identity"
def stringSftPlumbingCycleCompatibility : String := "string.sft.plumbing_cycle_compatibility"
def stringSftSiegelGaugePropagator : String := "string.sft.siegel_gauge_propagator"
def stringSftOnePiEffectiveActionSiegel : String := "string.sft.one_pi_effective_action_siegel"
def stringSftClassicalEquationWithBrackets : String := "string.sft.classical_equation_with_brackets"
def stringSftStringBracketDuality : String := "string.sft.string_bracket_duality"
def stringSftLInfinityHomotopyIdentity : String := "string.sft.l_infinity_homotopy_identity"
def stringSftMasslessFieldDictionary : String := "string.sft.massless_field_dictionary"
def stringSftBackgroundIndependenceMap : String := "string.sft.background_independence_map"
def stringSuperSftFieldSpaceNsrAuxiliary : String :=
  "string.super_sft.field_space_nsr_auxiliary"
def stringSuperSftOffShellAmplitudeChain : String :=
  "string.super_sft.off_shell_amplitude_chain"
def stringSuperSftRamondPlumbingPcoCompatibility : String :=
  "string.super_sft.ramond_plumbing_pco_compatibility"
def stringSuperSftOnePiPictureAdjustedPropagator : String :=
  "string.super_sft.one_pi_picture_adjusted_propagator"
def stringSuperSftRamondTowerRegularization : String :=
  "string.super_sft.ramond_tower_regularization"
def stringSuperSftBvQuantumMasterEquation : String :=
  "string.super_sft.bv_quantum_master_equation"
def stringSuperSftRrKineticTermMatching : String :=
  "string.super_sft.rr_kinetic_term_matching"
def stringSuperSftFieldEquationBracketPackage : String :=
  "string.super_sft.field_equation_bracket_package"
def stringSuperSftFlatBracketVerticalCorrection : String :=
  "string.super_sft.flat_bracket_vertical_correction"
def stringSuperSftPpWaveSolutionPackage : String :=
  "string.super_sft.pp_wave_solution_package"
def stringHeteroticWorldsheetChiralSupersymmetry : String :=
  "string.heterotic.worldsheet_chiral_supersymmetry"
def stringHeteroticLambdaGsoCurrentAlgebras : String :=
  "string.heterotic.lambda_gso_current_algebras"
def stringHeteroticPhysicalSpectrumCohomology : String :=
  "string.heterotic.physical_spectrum_cohomology"
def stringHeteroticPerturbativeAmplitudePrescription : String :=
  "string.heterotic.perturbative_amplitude_prescription"
def stringHeteroticTreeLevelEffectiveCouplings : String :=
  "string.heterotic.tree_level_effective_couplings"
def stringHeteroticGreenSchwarzAnomalyCoupling : String :=
  "string.heterotic.green_schwarz_anomaly_coupling"
def stringHeteroticNonBpsSpinorMassRenormalization : String :=
  "string.heterotic.non_bps_spinor_mass_renormalization"
def stringHeteroticBackgroundNlsmGaugeLorentzAnomaly : String :=
  "string.heterotic.background_nlsm_gauge_lorentz_anomaly"
def stringHeteroticCalabiYauStandardEmbedding : String :=
  "string.heterotic.calabi_yau_standard_embedding"
def stringHeteroticStromingerSystem : String :=
  "string.heterotic.strominger_system"
def stringHeteroticFourDEffectiveFiPotential : String :=
  "string.heterotic.four_d_effective_fi_potential"
def stringHeteroticOneLoopFiMassTerm : String :=
  "string.heterotic.one_loop_fi_mass_term"
def stringHeteroticTwoLoopVacuumEnergyFromBoundary : String :=
  "string.heterotic.two_loop_vacuum_energy_from_boundary"
def stringHeteroticShiftedVacuumSupersymmetryRestoration : String :=
  "string.heterotic.shifted_vacuum_supersymmetry_restoration"
def stringDbraneBosonicBoundaryConditions : String := "string.dbrane.bosonic_boundary_conditions"
def stringDbraneBosonicBoundaryStateNormalization : String := "string.dbrane.bosonic_boundary_state_normalization"
def stringDbraneOpenBosonicSpectrum : String := "string.dbrane.open_bosonic_spectrum"
def stringDbraneBoundaryMarginalDeformations : String := "string.dbrane.boundary_marginal_deformations"
def stringDbraneChanPatonGaugeEnhancement : String := "string.dbrane.chan_paton_gauge_enhancement"
def stringDbraneTypeIIBpsBoundarySupersymmetry : String := "string.dbrane.type_ii_bps_boundary_supersymmetry"
def stringDbraneOpenSuperstringSpectrum : String := "string.dbrane.open_superstring_spectrum"
def stringDbraneBpsBoundaryStateRrCharge : String := "string.dbrane.bps_boundary_state_rr_charge"
def stringDbraneNonBpsConstruction : String := "string.dbrane.non_bps_construction"
def stringDbraneIntersectingNdSpectrum : String := "string.dbrane.intersecting_nd_spectrum"
def stringDbraneAtAnglesStabilityBpsCondition : String := "string.dbrane.at_angles_stability_bps_condition"
def stringDbraneDynamicsBosonicOpenClosedPerturbation : String := "string.dbrane_dynamics_bosonic.open_closed_perturbation"
def stringDbraneDynamicsBosonicDiscTachyonAmplitudes : String := "string.dbrane_dynamics_bosonic.disc_tachyon_amplitudes"
def stringDbraneDynamicsBosonicDiscChanPatonGaugeStructure : String := "string.dbrane_dynamics_bosonic.disc_chan_paton_gauge_structure"
def stringDbraneDynamicsBosonicCylinderOpenClosedDuality : String := "string.dbrane_dynamics_bosonic.cylinder_open_closed_duality"
def stringDbraneDynamicsBosonicNambuGotoTensionMatching : String := "string.dbrane_dynamics_bosonic.nambu_goto_tension_matching"
def stringDbraneDynamicsBosonicDilatonTDualityRelations : String := "string.dbrane_dynamics_bosonic.dilaton_t_duality_relations"
def stringDbraneDynamicsBosonicBornInfeldGaugeInvariance : String := "string.dbrane_dynamics_bosonic.born_infeld_gauge_invariance"
def stringDbraneDynamicsBosonicGravitonDilatonExchange : String := "string.dbrane_dynamics_bosonic.graviton_dilaton_exchange"
def stringDbraneDynamicsBosonicCOneZzRollingTachyon : String := "string.dbrane_dynamics_bosonic.c_one_zz_rolling_tachyon"
def stringDbraneDynamicsBosonicCOneFzztLongStrings : String := "string.dbrane_dynamics_bosonic.c_one_fzzt_long_strings"
def stringDbraneDynamicsTypeIIOpenClosedPerturbation : String := "string.dbrane_dynamics_type_ii.open_closed_perturbation"
def stringDbraneDynamicsTypeIIDiscOpenGaugeAmplitudes : String := "string.dbrane_dynamics_type_ii.disc_open_gauge_amplitudes"
def stringDbraneDynamicsTypeIIDiscOpenClosedRrCouplings : String := "string.dbrane_dynamics_type_ii.disc_open_closed_rr_couplings"
def stringDbraneDynamicsTypeIICylinderNsnsRrCancellation : String := "string.dbrane_dynamics_type_ii.cylinder_nsns_rr_cancellation"
def stringDbraneDynamicsTypeIIBpsKappaSymmetricAction : String := "string.dbrane_dynamics_type_ii.bps_kappa_symmetric_action"
def stringDbraneDynamicsTypeIIBpsBackgroundCouplings : String := "string.dbrane_dynamics_type_ii.bps_background_couplings"
def stringDbraneDynamicsTypeIIRrChargeDiracQuantization : String := "string.dbrane_dynamics_type_ii.rr_charge_dirac_quantization"
def stringDbraneDynamicsTypeIIWrappedBraneSupersymmetry : String := "string.dbrane_dynamics_type_ii.wrapped_brane_supersymmetry"
def stringDbraneDynamicsTypeIID2HolomorphicCurveBps : String := "string.dbrane_dynamics_type_ii.d2_holomorphic_curve_bps"
def stringDbraneDynamicsTypeIID3SpecialLagrangianBps : String := "string.dbrane_dynamics_type_ii.d3_special_lagrangian_bps"
def stringDbraneDynamicsTypeIIWorldvolumeFluxBion : String := "string.dbrane_dynamics_type_ii.worldvolume_flux_bion"
def stringDbraneDynamicsTypeIINonAbelianStackedEffectiveTheory : String := "string.dbrane_dynamics_type_ii.non_abelian_stacked_effective_theory"
def stringDbraneDynamicsTypeIID0ScatteringBfssMatrixQM : String := "string.dbrane_dynamics_type_ii.d0_scattering_bfss_matrix_qm"
def stringOsftClassicalBvAInfinityStructure : String := "string.osft.classical_bv_a_infinity_structure"
def stringOsftEquationGaugeAInfinityRelations : String := "string.osft.equation_gauge_a_infinity_relations"
def stringOsftWittenCubicStarAlgebra : String := "string.osft.witten_cubic_star_algebra"
def stringOsftTachyonCondensationLevelTruncation : String := "string.osft.tachyon_condensation_level_truncation"
def stringOsftKbcAlgebraWedgeStates : String := "string.osft.kbc_algebra_wedge_states"
def stringOsftTachyonVacuumExactSolution : String := "string.osft.tachyon_vacuum_exact_solution"
def stringOsftMarginalDeformationKiermaierOkawa : String := "string.osft.marginal_deformation_kiermaier_okawa"
def stringOsftRollingTachyonCovariantPhaseSpace : String := "string.osft.rolling_tachyon_covariant_phase_space"
def stringOsftErlerMaccaferriIntertwiningSolution : String := "string.osft.erler_maccaferri_intertwining_solution"
def stringOsftQuantumOpenClosedBvVertices : String := "string.osft.quantum_open_closed_bv_vertices"
def stringOsftOpenClosedSuperBvActionAndTadpoles : String := "string.osft.open_closed_super_bv_action_and_tadpoles"
def stringDinstantonTransseriesAndModuliIntegral : String :=
  "string.dinstanton.transseries_and_moduli_integral"
def stringDinstantonCOneZzContributionAndNormalization : String :=
  "string.dinstanton.c_one_zz_contribution_and_normalization"
def stringDinstantonTypeIIBAxioDilatonExpansion : String :=
  "string.dinstanton.type_iib_axio_dilaton_expansion"
def stringDinstantonOpenClosedSftZeroModeGaugeFixing : String :=
  "string.dinstanton.open_closed_sft_zero_mode_gauge_fixing"
def stringDinstantonNormalizationFromZeroModeMeasure : String :=
  "string.dinstanton.normalization_from_zero_mode_measure"
def stringDinstantonMultipleIkktIntegralScaling : String :=
  "string.dinstanton.multiple_ikkt_integral_scaling"
def stringTypeIUnorientedWorldsheetParityProjection : String :=
  "string.type_i.unoriented_worldsheet_parity_projection"
def stringTypeICrosscapStateAndKleinBottleDuality : String :=
  "string.type_i.crosscap_state_and_klein_bottle_duality"
def stringTypeIClosedOpenOmegaProjectionSpectrum : String :=
  "string.type_i.closed_open_omega_projection_spectrum"
def stringTypeITadpoleCancellationSO32 : String :=
  "string.type_i.tadpole_cancellation_so32"
def stringTypeIAmplitudeNormalizationUnorientedOpenClosed : String :=
  "string.type_i.amplitude_normalization_unoriented_open_closed"
def stringTypeIVacuumAmplitudeTopologyAndCancellation : String :=
  "string.type_i.vacuum_amplitude_topology_and_cancellation"
def stringTypeIEffectiveActionGaugeGravityCouplings : String :=
  "string.type_i.effective_action_gauge_gravity_couplings"
def stringTypeIBpsD1D5BraneSpectrum : String :=
  "string.type_i.bps_d1_d5_brane_spectrum"
def stringTypeINonBpsD0StabilityAndFermions : String :=
  "string.type_i.non_bps_d0_stability_and_fermions"
def stringOrientifoldPlaneCrosscapChargeDictionary : String :=
  "string.orientifold_plane.crosscap_charge_dictionary"
def stringDualityHeteroticTypeIStrongWeak : String :=
  "string.duality.heterotic_type_i_strong_weak"
def stringDualityTypeIINS5BpsSoliton : String :=
  "string.duality.type_ii_ns5_bps_soliton"
def stringDualityNS5ThroatLittleStringScft : String :=
  "string.duality.ns5_throat_little_string_scft"
def stringDualityHeteroticNS5GaugeInstantonSmallInstanton : String :=
  "string.duality.heterotic_ns5_gauge_instanton_small_instanton"
def stringDualityTypeIIBSdualityModularInvariantCouplings : String :=
  "string.duality.type_iib_s_duality_modular_invariant_couplings"
def stringDualityPQStringsAndFiveBranes : String :=
  "string.duality.pq_strings_and_five_branes"
def stringDualityBlackPBraneSupergravityDictionary : String :=
  "string.duality.black_p_brane_supergravity_dictionary"
def stringDualityD7BraneFTheoryEllipticMonodromy : String :=
  "string.duality.d7_brane_f_theory_elliptic_monodromy"
def stringDualityMTheoryTypeIIACircleRelation : String :=
  "string.duality.m_theory_type_iia_circle_relation"
def stringDualityM2M5BraneTensionDictionary : String :=
  "string.duality.m2_m5_brane_tension_dictionary"
def stringDualityD6KaluzaKleinMonopoleUplift : String :=
  "string.duality.d6_kaluza_klein_monopole_uplift"
def stringDualityMTheoryHigherDerivativeProtectedTerms : String :=
  "string.duality.m_theory_higher_derivative_protected_terms"
def stringDualityHeteroticE8SO32CircleTduality : String :=
  "string.duality.heterotic_e8_so32_circle_t_duality"
def stringDualityHeteroticStrongCouplingMTheoryInterval : String :=
  "string.duality.heterotic_strong_coupling_m_theory_interval"
def stringDualityHoravaWittenBoundaryAnomalyInflow : String :=
  "string.duality.horava_witten_boundary_anomaly_inflow"
def stringDualityMassiveIIARomansD8System : String :=
  "string.duality.massive_iia_romans_d8_system"

end AssumptionId

/-- Registry entry for a tracked physical assumption. -/
structure AssumptionEntry where
  id : String
  description : String

/-- Central registry for tracked physical assumptions used in non-Papers modules. -/
def assumptionRegistry : List AssumptionEntry :=
  [ ⟨AssumptionId.bianchiImpliesConservation,
      "Contracted Bianchi identity implies covariant stress-energy conservation in this abstraction layer."⟩
  , ⟨AssumptionId.perfectFluidEnergyConditions,
      "Perfect-fluid stress tensor satisfies WEC and NEC under the declared equation-of-state bounds."⟩
  , ⟨AssumptionId.holevoBound,
      "Classical capacity of the identity channel is bounded by log(dim) in this abstract channel model."⟩
  , ⟨AssumptionId.qiArakiLieb,
      "Araki-Lieb entropy triangle inequality is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiKleinInequality,
      "Klein inequality equality condition for relative entropy is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiSeparableDiscordNonzero,
      "Existence of separable states with nonzero quantum discord is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiDistillationLessThanFormation,
      "Distillable entanglement is bounded above by entanglement of formation in this abstraction layer."⟩
  , ⟨AssumptionId.qiLoccMonotone,
      "LOCC monotonicity of entanglement of formation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiLoccPreservesSeparability,
      "LOCC operations preserve separability in this abstraction layer."⟩
  , ⟨AssumptionId.qiStrongSubadditivity,
      "Strong subadditivity inequality is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiNoCloning,
      "No-cloning impossibility statement is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiNoDeleting,
      "No-deleting impossibility statement is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qiNoBroadcasting,
      "No-broadcasting impossibility statement is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.quantumPureToDensityAxioms,
      "Self-adjointness/positivity/trace-one proof obligations for the pure-state density operator construction are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.quantumUnitaryPreservesNorm,
      "Unitary norm preservation is assumed in this abstraction layer's quantum operator model."⟩
  , ⟨AssumptionId.quantumExpectationReal,
      "Reality of expectation values for Hermitian observables is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.quantumPauliDirectionObservable,
      "Linearity and Hermiticity proof obligations for Bloch-sphere directional Pauli observables are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.quantumSingletPauliCorrelation,
      "Singlet-state Pauli correlation formula is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.brstExactImpliesClosed,
      "BRST exact implies BRST closed is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.brstGaugeFixedInvariant,
      "BRST invariance of the gauge-fixed action is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.brstGaugeFixingDifferenceExact,
      "BRST exactness of differences between gauge-fixed actions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.pathIntegralDiscretizedContinuumLimit,
      "Convergence from discretized path-integral regulators to a continuum amplitude is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.pathIntegralInstantonSemiclassicalWeight,
      "Leading semiclassical instanton amplitude weight with one-loop prefactor is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.pathIntegralWittenIndexMorseComplex,
      "Identification of the Witten index with Morse-complex alternating data is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.pathIntegralBorelSokalWatsonCriterion,
      "Sokal-Watson style Borel-summability criterion is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.pathIntegralLefschetzThimbleExpansion,
      "Decomposition of path integrals into Lefschetz-thimble sectors is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyAxial2dCurrentDivergence,
      "The 2D axial-current divergence relation ∂_μ j_A^μ = (1/2π) ε^{μν} F_{μν} is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyAxial4dCurrentDivergence,
      "The 4D axial-current divergence relation ∂_μ j_A^μ = (1/16π^2) ε^{μνρσ} F_{μν}F_{ρσ} is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGaugeU1ChiralVariation,
      "The chiral 4D U(1) gauge-anomaly variation coefficient relation for δ_ζ Γ is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGaugeU1CubicCoefficient,
      "The multi-U(1) cubic anomaly coefficients d_{abc} = Σ_j q_j^(a) q_j^(b) q_j^(c) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGaugeU1CountertermShift,
      "The local-counterterm shift relation d'_{abc} = d_{abc} + 1/2(h_{ab,c} + h_{ac,b}) with h_{ab,c} antisymmetric in a,b is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGaugeDescentRelations,
      "Gauge-anomaly descent relations δ_ζ Γ = -∫I_d, dI_d = δ_ζ I_{d+1}, and dI_{d+1} = I_{d+2} are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGaugeChiralFermionPolynomial,
      "The chiral-fermion gauge-anomaly-polynomial normalization I_{d+2} ~ tr_R(F^{(d+2)/2}) with the standard factorial/(2π) prefactor is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGravitationalDescent4kPlus2,
      "Gravitational-anomaly descent relations in dimensions d = 4k+2 are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGravitationalAhatPolynomial,
      "The complex-Weyl gravitational anomaly-polynomial relation to the A-hat genus top-form component is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftAnomalyGravitationalD10MwPolynomial,
      "The explicit 10D Majorana-Weyl gravitational-anomaly polynomial coefficients are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvDifferentialNilpotent,
      "Nilpotency of the BV differential under the classical master equation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvDifferentialNZero,
      "Vanishing of higher BV differential iterates (n >= 2) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvGaugeIndependence,
      "Gauge-fixing independence in BV via BV-exact variation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvFaddeevPopovGaugeSliceRegular,
      "Regularity/non-degeneracy of the Faddeev-Popov gauge slice is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvMasterEquationClosureHierarchy,
      "Gauge-invariance, closure, and Jacobi-type hierarchy constraints from BV master-equation expansion are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvGaugeFixingFermionRecoversBrst,
      "Recovery of a BRST gauge-fixed action from BV gauge-fixing-fermion data is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvWilsonianMasterEquationPreserved,
      "Preservation of the BV quantum master equation along Wilsonian coarse-graining is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.tqftModularRelation,
      "The modular relation connecting S and T matrices is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.tqftZ3ModularAxioms,
      "Coherence and modularity proof obligations for the explicit Z3 modular-category instance are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.tqftSu24FusionAxioms,
      "Coherence proof obligations for the explicit SU(2)_4 fusion-category instance are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.tqftSu24RibbonAxioms,
      "Braiding/twist coherence proof obligations for the explicit SU(2)_4 ribbon-category instance are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.tqftIsingModularAxioms,
      "Coherence and modularity proof obligations for the explicit Ising modular-category instance are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.osReconstruction,
      "OS axioms provide analytic continuation to Wightman data in this abstract reconstruction interface."⟩
  , ⟨AssumptionId.ghsInequality,
      "Ferromagnetic Euclidean theories satisfy the stated GHS-type correlation inequality."⟩
  , ⟨AssumptionId.qftEuclideanMqmCanonicalCommutation,
      "Canonical matrix-coordinate/momentum commutation relations for one-matrix quantum mechanics are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmSingletReduction,
      "Reduction of the gauged one-matrix model singlet sector to non-interacting fermions after Vandermonde redefinition is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmCOneInvertedPotential,
      "The `c=1` matrix-model inverted-harmonic potential relation `V(λ) = -1/2 λ^2` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmFermiSeaProfile,
      "Semiclassical `c=1` Fermi-sea profile and eigenvalue-density relations are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmCollectiveTauHamiltonian,
      "Collective-field coordinate map `λ = sqrt(2μ) cosh τ` and the `1/(μ sinh^2 τ)` interaction-prefactor structure are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmCollectiveBornOneToTwo,
      "Born-level collective-field `1 -> 2` amplitude relation proportional to `i ω ω1 ω2 / μ` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmReflectionHoleRelation,
      "Non-perturbative particle/hole reflection-amplitude inverse relation in `c=1` matrix quantum mechanics is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmInstantonOneToN,
      "Leading instanton correction formula for `1 -> n` amplitudes in `c=1` matrix quantum mechanics is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmLongStringRenormalizedEnergy,
      "Non-singlet long-string renormalized-energy relation `ε = E - (L-1)/π` with boundary profile condition is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftEuclideanMqmLongStringIntegralEquation,
      "Non-singlet long-string integral-equation interface relation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.wilsonianIrrelevantSuppression,
      "Irrelevant operators are power-law suppressed along Wilsonian RG flow in this abstraction layer."⟩
  , ⟨AssumptionId.qcdAsymptoticFreedom,
      "One-loop QCD coefficient has the asymptotic-freedom sign in the Nf < 17 regime under the chosen convention."⟩
  , ⟨AssumptionId.lorentzPreservesTimelike,
      "Lorentz transformations preserve timelike separation in the Minkowski model."⟩
  , ⟨AssumptionId.lorentzPreservesSpacelike,
      "Lorentz transformations preserve spacelike separation in the Minkowski model."⟩
  , ⟨AssumptionId.lorentzPreservesLightlike,
      "Lorentz transformations preserve lightlike separation in the Minkowski model."⟩
  , ⟨AssumptionId.lorentzBoostPreservesMetric,
      "The explicit x-direction boost matrix preserves the Minkowski inner product."⟩
  , ⟨AssumptionId.spatialRotationPreservesMetric,
      "The explicit spatial z-rotation matrix preserves the Minkowski inner product."⟩
  , ⟨AssumptionId.metricPerturbationWellFormed,
      "First-order perturbed metric data is treated as a valid Lorentzian metric package in this linearized model."⟩
  , ⟨AssumptionId.reissnerNordstromMetricWellFormed,
      "Reissner-Nordstrom metric data is treated as a valid Lorentzian metric package in this abstraction layer."⟩
  , ⟨AssumptionId.flrwMetricWellFormed,
      "FLRW metric data is treated as a valid Lorentzian metric package in this abstraction layer."⟩
  , ⟨AssumptionId.lorentzComposePreservesMetric,
      "Composition of Lorentz transformations preserves the Minkowski inner product."⟩
  , ⟨AssumptionId.lorentzInversePreservesMetric,
      "The explicit Lorentz inverse construction preserves the Minkowski inner product."⟩
  , ⟨AssumptionId.lorentzGroupMulAssoc,
      "Lorentz multiplication is associative in the chosen abstraction."⟩
  , ⟨AssumptionId.lorentzGroupOneMul,
      "Lorentz identity is a left unit in the chosen abstraction."⟩
  , ⟨AssumptionId.lorentzGroupMulOne,
      "Lorentz identity is a right unit in the chosen abstraction."⟩
  , ⟨AssumptionId.lorentzGroupInvMulCancel,
      "Lorentz inverse is a left inverse in the chosen abstraction."⟩
  , ⟨AssumptionId.poincareGroupMulAssoc,
      "Poincare multiplication is associative in the chosen abstraction."⟩
  , ⟨AssumptionId.poincareGroupOneMul,
      "Poincare identity is a left unit in the chosen abstraction."⟩
  , ⟨AssumptionId.poincareGroupMulOne,
      "Poincare identity is a right unit in the chosen abstraction."⟩
  , ⟨AssumptionId.poincareGroupInvMulCancel,
      "Poincare inverse is a left inverse in the chosen abstraction."⟩
  , ⟨AssumptionId.symSpinorCliffordAlgebraRelation,
      "The spinor gamma-matrix Clifford algebra anticommutator relation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorEvenCliffordFockRelation,
      "Even-dimensional spinor construction via fermionic-oscillator (creation/annihilation) relations is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorChiralityEigenspaceDimensions,
      "The chiral/anti-chiral eigenspace dimension split for even-dimensional spinor representations is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorMajoranaAdmissibleEven,
      "Mod-8 admissibility of Majorana reality conditions in even dimensions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorMajoranaWeylAdmissible,
      "Mod-8 admissibility condition for simultaneous Majorana-Weyl constraints is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorChargeConjugationRelation,
      "Charge-conjugation transformation relation for gamma matrices is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorSo19ConventionPackage,
      "The `so(1,9)` spinor index-raising/lowering and cyclic gamma-identity convention package is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorSo13ConventionPackage,
      "The `so(1,3)` Weyl/Majorana gamma-contraction and bilinear-decomposition convention package is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorSo12ConventionPackage,
      "The `so(1,2)` real-gamma and symmetric-index convention package is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorEuclideanD8TrialityRelations,
      "Euclidean `d=8` triality/Clifford gamma-index relations are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSpinorEuclideanD6Su4GammaIdentity,
      "Euclidean `d=6` `su(4) ~= so(6)` gamma-index contraction identity is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSuperPoincareAlgebra,
      "The `d`-dimensional extended super-Poincare algebra anticommutator relation with momentum and central-charge terms is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSuperPoincareMasslessMultipletDimension,
      "Massless supermultiplet state-count relation in terms of supersymmetry count and minimal spinor dimension is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSuperPoincareBpsBound,
      "BPS bound and saturation-implied preserved-supercharge condition are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSuperspaceN1Algebra4d,
      "The 4D N=1 superspace supercharge/superderivative anticommutator algebra is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSuperspaceN1ChiralConstraint,
      "The 4D N=1 chiral/anti-chiral superfield constraints are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.symSuperspaceN1VectorFieldStrengthGaugeInvariant,
      "Gauge transformation and field-strength invariance/chirality relations for 4D N=1 vector superfields are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftSusyN1HolomorphicOneLoopBeta,
      "Holomorphic one-loop exact Wilsonian beta-function structure for 4D N=1 gauge coupling is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftSusyN1NsvzBetaRelation,
      "The NSVZ beta-function relation for canonically normalized 4D N=1 gauge coupling is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftSusyN2PrepotentialConstraints,
      "The N=2 prepotential constraints determining Kahler potential and gauge kinetic matrix are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftSusy3dN2SigmaDtermRelation,
      "The 3D N=2 Chern-Simons-matter D-term elimination relation for sigma is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.qftSusy3dN3QuarticSuperpotential,
      "The 3D N=3 quartic superpotential relation after integrating out auxiliary adjoint chiral multiplet is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.schwarzschildMetricWellFormed,
      "Schwarzschild metric data is treated as a valid Lorentzian metric package in this abstraction layer."⟩
  , ⟨AssumptionId.conformalPreservesNull,
      "Conformal rescaling preserves null separation in the current abstraction layer."⟩
  , ⟨AssumptionId.conformalPreservesCausalStructure,
      "Conformal rescaling preserves causal classification (timelike/spacelike/lightlike) in the current abstraction layer."⟩
  , ⟨AssumptionId.cftCrossRatiosPositiveFromPoints,
      "Computed CFT cross-ratios from the selected point configuration are in the positive region used by the bootstrap layer."⟩
  , ⟨AssumptionId.cftTDualWeightSymmetry,
      "Free-boson momentum/winding conformal weights obey the T-duality swap symmetry used in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dIsingSigmaFourPointCrossing,
      "Crossing consistency of the Ising spin-field four-point decomposition (including the sigma-sigma-epsilon structure-constant value in this abstraction layer) is assumed."⟩
  , ⟨AssumptionId.cft2dDefectFusionPentagon,
      "Topological-defect fusion/junction data is assumed to satisfy pentagon-type consistency in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dOrbifoldConstructionModularInvariant,
      "The orbifold Hilbert-space construction from symmetry-line sectors is assumed to produce modular-invariant partition data in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dNarainEvenSelfDualModularInvariant,
      "Even/self-dual Narain-lattice conditions are assumed sufficient for modular-invariant torus partition data in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dNarainCocycleAssociative,
      "Associative 2-cocycle structure for Narain vertex-operator phases is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dNlsmWeylAnomalyVanishing,
      "Vanishing of hatted nonlinear-sigma-model Weyl-anomaly coefficients at conformal points is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBuscherRules,
      "Buscher T-duality transformation rules (including dilaton shift) are assumed valid in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dGaugedWzwCosetFlow,
      "The gauged-WZW to coset/nonlinear-sigma-model correspondence in the IR is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dLiouvilleMarginality,
      "Marginality condition Q = b + 1/b for Liouville interaction and associated conformal fixed-point interpretation are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dLiouvilleDozzRecursion,
      "Degenerate-field bootstrap recursion constraints leading to DOZZ-type Liouville structure constants are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dSuperspace11DerivativeAlgebra,
      "The (1,1) superspace derivative/supercharge algebra (including anticommutation relations and D^2 identities) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dN1SuperconformalAlgebra,
      "The Appendix-J N=1 superconformal mode algebra package (including Ramond zero-mode relation on the cylinder) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dSuperspace22ChiralReduction,
      "The (2,2) chiral-superspace constraint and its reduction interface to (1,1) superspace variables are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dN2SuperconformalAlgebra,
      "The Appendix-J N=2 superconformal mode algebra relations among T, G^±, and U(1)_R current modes are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dN2SpectralFlowAutomorphism,
      "The N=2 spectral-flow transformation rules for modes and charges are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dN4SmallSuperconformalAlgebra,
      "Selected small N=4 superconformal mode relations (including c = 6k' and SU(2)_R current algebra pieces) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dN4SpectralFlowInnerAutomorphism,
      "Small N=4 spectral-flow inner-automorphism transformation rules are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dLandauGinzburgMinimalModelFlow,
      "Flow of even polynomial 2D Landau-Ginzburg deformations to Virasoro minimal-model IR fixed points (with the stated central-charge relation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dN2LandauGinzburgNonRenormalization,
      "In a supersymmetric Wilsonian scheme, non-renormalization of the N=2 LG superpotential and associated minimal-model IR central-charge relation are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dGlsmAxialAnomalyThetaShift,
      "The GLSM axial-anomaly induced theta-angle shift relation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dGlsmTwistedSuperpotentialOneLoop,
      "One-loop coefficient constraints for the GLSM twisted effective superpotential are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dCalabiYauLandauGinzburgPhaseFlow,
      "The Calabi-Yau/Landau-Ginzburg phase-flow package (including FI-sign phase assignment and central-charge matching) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dAbelianDualityTwistedSuperpotentialMatch,
      "Matching of abelian-dual twisted superpotentials up to linear/constant redefinition is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dCigarLiouvilleMirrorDuality,
      "Mirror-duality equivalence constraints between the N=2 cigar and Liouville SCFT descriptions are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryConformalInvariance,
      "Boundary conformal invariance constraints (including boundary stress-tensor gluing and central-charge matching) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryCorrelatorKinematics,
      "Kinematic constraints on boundary two-/three-point correlators from global conformal invariance on the disc/UHP are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryStateIshibashiGluing,
      "Boundary-state gluing/Ishibashi decomposition constraints `(L_n - L̃_{-n})|B⟩ = 0` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryBulkBoundaryOnePoint,
      "The bulk-boundary one-point coefficient relation `R_{i0} = D_{ij} U_B^j` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryCylinderModularDuality,
      "Closed/open channel modular duality for the cylinder partition function with boundary conditions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryChanPatonFactorization,
      "Chan-Paton factorization and matrix-unit multiplication structure for boundary-condition sums are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryFreeBosonNdConditions,
      "Free-boson Neumann/Dirichlet conformal boundary-condition relations are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryFreeBosonNormalization,
      "Free-boson Neumann/Dirichlet boundary-state normalization relations from cylinder modular consistency are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryFreeFermionNdConditions,
      "Free-fermion Neumann/Dirichlet boundary-condition equations with boundary spin-structure choice are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryFreeFermionCoefficients,
      "Free-fermion Ising boundary-state coefficient relations (including `N_1`, `N_2`, `N_3`) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.cft2dBoundaryFreeFermionSectorIdentification,
      "Identification of `NN`/`DD` boundary operator sectors with projected/unprojected NS-sector content in Ising BCFT is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.grSupergravityCurvedSpinorGeometry,
      "Frame-field, curved-gamma, and spinor-covariant-derivative compatibility relations in curved space are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.grSupergravity11dCorePackage,
      "The core 11D supergravity multiplet-content and 4-form field-strength package is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSupergravityTypeIIAFormRelations,
      "Type IIA modified RR/NS form-field relations are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSupergravityTypeIIBPseudoActionConstraints,
      "Type IIB pseudo-action form constraints, including self-duality of the five-form sector, are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSupergravityTypeIGreenSchwarzHatH,
      "Green-Schwarz modified three-form relation in type I supergravity is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.grSupergravityN2SpecialKahlerPotential,
      "The 4D N=2 special-Kahler potential relation from local prepotential data is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.grSupergravityN2QuaternionicRicciRelation,
      "The quaternionic-Kahler Ricci-curvature relation for 4D N=2 hypermultiplet target geometry is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.grSupergravityN2GaugedScalarPotential,
      "The 4D N=2 gauged-supergravity scalar-potential decomposition interface is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.grSupergravityN1GaugeAndPotentialPackage,
      "The 4D N=1 supergravity scalar-potential decomposition and gauge-kinetic shift package is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.lszKleinGordonOperatorExists,
      "A suitable Klein-Gordon operator action is available in the abstract LSZ functional setting."⟩
  , ⟨AssumptionId.lszReductionFormula,
      "The LSZ reduction identity for amplitudes is assumed in the current abstraction layer."⟩
  , ⟨AssumptionId.haagRuelleEqualsLsz,
      "Haag-Ruelle and LSZ constructions give identical scattering amplitudes in the current abstraction layer."⟩
  , ⟨AssumptionId.wightmanPctTheorem,
      "PCT symmetry relation for Wightman functions holds in the current abstraction layer."⟩
  , ⟨AssumptionId.wightmanSpinStatistics,
      "Spin-statistics relation holds in the current abstraction layer."⟩
  , ⟨AssumptionId.wightmanHaagTheorem,
      "Haag's unitary inequivalence conclusion holds in the current abstraction layer."⟩
  , ⟨AssumptionId.wightmanReehSchlieder,
      "Reeh-Schlieder cyclicity/separating conclusion is assumed at this abstraction layer."⟩
  , ⟨AssumptionId.wightmanTemperedness,
      "Temperedness growth bound for Wightman distributions is assumed in the current abstraction layer."⟩
  , ⟨AssumptionId.aqftGnsExistence,
      "GNS representation existence for states on local AQFT algebras is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftReehSchlieder,
      "AQFT Reeh-Schlieder density conclusion is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftHaagTheorem,
      "AQFT Haag-theorem expectation-value equivalence conclusion is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftTomitaTakesaki,
      "Existence of Tomita-Takesaki modular data is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftBisognanoWichmann,
      "Bisognano-Wichmann wedge modular-flow identification is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftBoseFermiAlternative,
      "Bose-Fermi alternative in d >= 4 is assumed for AQFT superselection statistics in this abstraction layer."⟩
  , ⟨AssumptionId.aqftAnyonsIn3d,
      "Existence of anyonic exchange-phase parametrization in d = 3 is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftDoplicherRobertsReconstruction,
      "Existence of Doplicher-Roberts reconstruction data is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.aqftSpinStatistics,
      "Spin-statistics implication statements are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPrologueWeinbergWittenNoLocalStressTensor,
      "The prologue-level Weinberg-Witten incompatibility between local stress tensor and massless spin-2 states is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPrologueLargeNYmWeaklyCoupledFluxStrings,
      "Large-N Yang-Mills flux strings are treated as weakly interacting with splitting/joining amplitudes suppressed in 1/N."⟩
  , ⟨AssumptionId.stringEffectiveNgPolyakovEquivalence,
      "Classical equivalence between Nambu-Goto and Polyakov formulations is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringEffectiveReggeTrajectory,
      "The rotating closed-string Regge relation E^2 = 4 pi T J is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringBosonicCriticalDimension,
      "Weyl-anomaly cancellation selecting the critical bosonic dimension D = 26 is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringBosonicBrstPhysicalStatesCohomology,
      "Physical bosonic-string states are identified with BRST cohomology classes in this abstraction layer."⟩
  , ⟨AssumptionId.stringBosonicSiegelImpliesLevelMatching,
      "Siegel constraints imply level-matching/zero-weight conditions in this abstraction layer."⟩
  , ⟨AssumptionId.stringBosonicMassSpectrumFormula,
      "The bosonic closed-string mass-shell relation m^2 = 4/alpha' * (N - 1) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringPolyakovGaugePackage,
      "The super-Polyakov worldsheet package (local worldsheet supersymmetry, super-Weyl invariance, conformal-gauge free-field reduction, and matter central-charge relation c_m=(3/2)D) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringGhostSystemPackage,
      "The superconformal ghost package (`beta-gamma` OPE sign, `bc`+`beta-gamma` central-charge accounting, and total `c_gh=-15`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringPictureNumberPackage,
      "The picture-number package (`H'[A]` eta_0 condition, genus-dependent ghost-charge anomaly `2g-2`, and canonical NS/R pictures `-1` and `-1/2`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringTypeIIGsoProjection,
      "Type-II chiral GSO projection rules distinguishing IIA (`(-)^F=(-)^F'~=1`) and IIB (`(-)^F=(-)^F~=1`) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringBrstCurrentPackage,
      "The superstring BRST superfield/current and oscillator-relation package (`{Q_B,b_n}=L_n`, `[Q_B,beta_r]=-(1/2)G_r`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringBrstNilpotencyCritical,
      "Critical-dimension superstring BRST nilpotency (`D=10` implies `Q_B^2=0`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringSiegelConstraintPackage,
      "The superstring Siegel-constraint package (`b_0=b~_0=0` and Ramond `beta_0` constraints) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringPhysicalCohomologyPackage,
      "Physical superstring states are identified with BRST cohomology classes subject to Siegel constraints in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringOcqRepresentativePackage,
      "The NS/R OCQ representative package (`c e^{-phi}V` with `h(V)=1/2`, and `c e^{-phi/2}S` with Ramond highest-weight constraints) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringMassSpectrumPackage,
      "The type-II superstring mass-shell package (`L_0=L~_0=0`, level matching, and `m^2=4N/alpha'` with `N` in nonnegative integers after GSO projection) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringMasslessSectorPackage,
      "Massless type-II `(NS,NS)`, `(R,R)`, and mixed fermionic-sector on-shell/transversality/Dirac-condition packages (including gauge redundancies where applicable) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperstringSpacetimeSusyAlgebra,
      "The worldsheet-current realization of spacetime supersymmetry algebra (`{Q,Q}=(sqrt(alpha')/4)Gamma.P`, similarly for right movers, and left-right anticommutator zero up to picture-raising) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringBackgroundWeylBetaVanishing,
      "Vanishing of sigma-model beta functions at a Weyl-invariant string background is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringBackgroundBetaToSpacetimeEom,
      "The link from vanishing worldsheet beta functions to spacetime effective equations is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringBackgroundCOneTachyonMassless,
      "In the c=1 background layer, the asymptotic scalar mode is treated as massless (k0^2 = k1^2)."⟩
  , ⟨AssumptionId.stringSuperBackgroundNsrHilbertGsoDecomposition,
      "The general-background NSR Hilbert-space decomposition with NS/R picture assignments and modular-invariant chiral GSO projection is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundNsnsScftDeformation,
      "The NSNS superconformal deformation package by integrated `(1,1)` superprimary descendants (first-order invariance plus higher-order counterterm requirement) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundNsnsNlsmSuperspaceAction,
      "The supersymmetric NSNS NLSM package with `(G,B,Phi)` backgrounds, `H=dB`, worldsheet `(1,1)` supersymmetry, and classical Weyl invariance is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundNsnsTreeEffectiveAction,
      "The tree-level NSNS spacetime effective-action structure `e^(-2Phi)(R - H^2/12 + 4(dPhi)^2)` with expected low-order `alpha'` correction pattern is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundCalabiYau22Structure,
      "The Calabi-Yau sigma-model package (Kahler target, `(2,2)` superconformal symmetry, and `U(1)xU(1)` R-current structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundCalabiYauRicciFlatTopForm,
      "The Calabi-Yau Ricci-flat package (`R_{I\\bar J}=0`, holomorphic top form, `c1=0`, Yau existence/uniqueness in a Kahler class, and `SU(n)`-holonomy spinor consequences) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundCalabiYauInstantonBFieldPhase,
      "The flat-`B` Calabi-Yau package (`H=0` gives topological worldsheet coupling with non-perturbative instanton-phase shifts and no perturbative `alpha'` dynamics change) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundGreenSchwarzKappaSymmetry,
      "The Green-Schwarz flat-background package (`S=S1+S2`, spacetime supersymmetry, and kappa symmetry projecting out half of worldsheet fermions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundLightConeGaugeSpectrum,
      "The Green-Schwarz light-cone/kappa-gauge package (`Gamma^+ theta=0` with free transverse-field spectrum of 8 bosons and 8+8 fermions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperBackgroundSuperspaceTorsionHConstraints,
      "The Green-Schwarz superspace package (super-vielbein metric relation, torsion and `H` constraint sets, and resulting kappa invariance for on-shell type-II supergravity backgrounds) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAnomalyTypeIibCancellation,
      "Cancellation of type-IIB 10D anomaly-polynomial contributions between dilatino, gravitino, and self-dual four-form sectors is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAnomalyTypeIHeteroticFactorization,
      "The factorized 12-form anomaly-polynomial relation for type-I/heterotic theories at dim(G)=496 is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAnomalyGreenSchwarzCancellation,
      "Green-Schwarz cancellation of quantum anomaly variation by B-field counter-variation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyScalarBoundaryCondition,
      "The standard holographic scalar boundary condition `lim_{z->0} z^(Delta-d) phi = phi_0` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyScalarTwoPointFunction,
      "The holographic scalar two-point coefficient relation proportional to `(2Delta-d) C_Delta` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyGaugeCurrentDictionary,
      "The AdS gauge-field to conserved-current dictionary with `Delta_J = d-1` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyGravityStressTensorDictionary,
      "The AdS graviton to CFT stress-tensor dictionary with `Delta_T = d` and stress-tensor conservation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyRegulatedGravityAction,
      "The regularized AdS gravity action package (bulk Einstein-Hilbert term plus Gibbons-Hawking and local counterterms) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyWittenCubicThreePoint,
      "The cubic scalar Witten-diagram three-point coefficient relation `-g_3 a_Delta` over conformal distance factors is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyMellinConstraints,
      "The Mellin-variable symmetry and linear constraints `sum_{j != i} delta_ij = Delta_i` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyMellinContactAmplitudeUnity,
      "The contact-diagram Mellin amplitude normalization `M = 1` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyMellinExchangePoleSeries,
      "The tree-level scalar-exchange Mellin pole locations at `Delta + 2k` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHolographyMellinFlatSpaceLimit,
      "The large-AdS-radius Mellin to flat-space scattering-amplitude transform relation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftD3DecouplingLimit,
      "The D3-brane low-energy decoupling-limit inequalities on string-scale and coupling-scale energies are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftParameterMap,
      "The AdS5/CFT4 parameter relations `g_B = g_YM^2/(2pi)`, `lambda = 2 g_YM^2 N`, and `R^4/alpha'^2 = lambda` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftN4SymConformalPackage,
      "The `N=4` SYM conformal package with vanishing beta function/stress-tensor trace and superconformal algebra label `psu(2,2|4)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftCoulombBranchVacuumPackage,
      "The Coulomb-branch vacuum moduli-space package `(R^6)^N/S_N` with W-boson mass relation `m_ab = |phi_a - phi_b|` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftProbeD3CoulombMatching,
      "Matching between the probe D3-brane effective action and Coulomb-branch `U(1)` effective action is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftPoincareGlobalCoordinateMap,
      "The Poincare-to-global Euclidean AdS coordinate relations `e^tau = sqrt(|x|^2+z^2)` and `tanh rho = |x|/sqrt(|x|^2+z^2)` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftStateOperatorMap,
      "The global-AdS/CFT state-operator map relation equating global energy with conformal dimension is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftDictionary,
      "The generating-functional AdS/CFT dictionary relation equating bulk partition data with boundary correlator data is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftSupergravitonChiralPrimaries,
      "The supergraviton/chiral-primary package (`[0,n,0]`, `Delta=n`, half-BPS protection) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftMassiveStringScaling,
      "The large-coupling massive-string scaling relation `Delta ~ 2 sqrt(n) lambda^(1/4)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftSpinningStringTwist,
      "The large-spin folded-string twist relation `(Delta-J) ~ (sqrt(lambda)/pi) log(J/sqrt(lambda))` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftGiantGravitonDuality,
      "The giant-graviton BPS relation `Delta=J=N sin^2(theta)` and determinant/sub-determinant operator dual labeling are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftHawkingPageTransition,
      "The AdS5 Hawking-Page transition package relating inverse temperature, horizon radius, and BH/AdS free-energy shift is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdSCftThermalStrongCoupling,
      "The strong-coupling thermal free-energy coefficient relation `f(infinity)=pi^2/8` for `N=4` SYM is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryM2NearHorizonPackage,
      "The M2-brane near-horizon relation `R^6 M11^6 = 32 pi^2 N2` with `R_AdS = R/2` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryM5NearHorizonPackage,
      "The M5-brane near-horizon relation `R^3 M11^3 = pi N5` with `R_AdS = 2R` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryD2GaugeCouplingRelation,
      "The D2/M-theory coupling map `gYM^2 = g_A/ell_A = M11^(3/2) R10` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryN8SymIrFixedPointPackage,
      "The 3D `N=8` SYM IR package with `so(7)->so(8)` enhancement and superconformal algebra `osp(8|4)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryN8SymCoulombBranchSU2,
      "The rank-2 Coulomb-branch package `(S^1 x R^7)/Z_2` with dual-photon periodicity `sigma~sigma+gYM^2` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryN8SymCoulombBranchUN,
      "The general-rank 3D `N=8` SYM Coulomb-branch quotient package `(S^1 x R^7)^N/S_N` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryAbjmLevelQuantization,
      "ABJM Chern-Simons gauge-variation shift `Delta S_CS = 2 pi k n` with integer level quantization is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryAbjmAdS4OrbifoldDuality,
      "The ABJM/M-theory map on `AdS4 x S7/Z_k` with `R^6 M11^6 = 32 pi^2 kN`, `lambda=N/k`, and circle-reduction coupling relations is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryAbjmVacuumModuliSpace,
      "The ABJM vacuum moduli-space relation `M = (C^4/Z_k)^N/S_N` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheoryAbjmKOneTwoEnhancement,
      "For ABJM levels `k=1,2`, enhancement from `osp(6|4)` to `osp(8|4)` with topological `U(1)_T` structure is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheorySixD02SuperconformalMultiplets,
      "The 6D `(0,2)` superconformal package `osp(2,6|4)` with stress-tensor multiplet `D[0,2]` and KK family `D[0,k]` (weight `Delta=2k`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheorySixD02ToFiveDCompactification,
      "The 6D `(0,2)` circle-compactification relation `gYM^2=(2pi)^2 R_M` and instanton mass relation `M_n=4pi^2 n/gYM^2=n/R_M` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMTheorySixD02VacuumModuli,
      "The interacting `A_(N-1)` vacuum-moduli package with center-of-mass quotient and `N-1` tensor multiplets at generic vacua is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5InstantonChargeMap,
      "The D1/D5 instanton-number map (`n=Q1` for `T^4`, `n=Q1+Q5` for K3) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5BranchStructure,
      "The D1-D5 low-energy branch package with ADHM Higgs-branch structure and FI-induced Coulomb-branch lifting is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5InstantonModuliDimension,
      "Dimension formulas for D1-D5 Higgs-branch instanton moduli spaces (`4Q1Q5` on `T^4`, `4(Q1Q5+1)` on K3) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5NearHorizonGeometry,
      "The D1-D5 near-horizon decoupling relations for `R1^2`, `R5^2`, and `AdS_3 x S^3 x M_4` geometry are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5CentralCharge,
      "The D1-D5/Brown-Henneaux central-charge relation `c = 6 Q1 Q5` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5ConformalManifoldUduality,
      "The D1-D5 conformal-manifold/U-duality package with invariant `Q1Q5/(gcd(Q1,Q5))^2`, attractor relation `tau~ = (Q1/Q5) tau`, and coset structure is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3D1D5SymmetricOrbifoldLocus,
      "The symmetric-product-orbifold locus package `Sym^(Q1Q5)(T^4)` and FI-lifted Coulomb-branch behavior is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3BosonicWzwLevelRadius,
      "The bosonic AdS3 WZW level/radius relation `k = R^2/alpha'` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3BosonicSpectralFlow,
      "The bosonic AdS3 `SL(2,R)` spectral-flow automorphism of current and Virasoro modes is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3BosonicPhysicalSpectrum,
      "Allowed bosonic AdS3 string-state representation sectors (discrete/continuous with spectral flow) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3BosonicMassShell,
      "The bosonic AdS3 mass-shell and spacetime-energy relations after spectral flow are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3NsnsSuperstringWorldsheet,
      "The purely `(NS,NS)` AdS3xS3xM4 worldsheet package `hatSL(2)_k x hatSU(2)_k x M_4`, `R^2=k alpha'`, and `c=15` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3NsnsSuperstringMassShell,
      "The `(NS,NS)` AdS3 superstring mass-shell relation and associated BPS lower-bound package are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3MixedFluxParameterization,
      "The mixed `(NS,NS)`/`(R,R)` AdS3 flux parameterization with `R^2 = alpha' sqrt(K5^2 + g_B^2 Q5^2)` and `mu = g_B Q5 / K5` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS3MixedFluxPulsatingShift,
      "The small-`mu` semiclassical correction formula for circular pulsating-string energies in mixed-flux AdS3 backgrounds is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityOneLoopSpinChain,
      "The one-loop `SU(2)` planar `N=4` SYM spin-chain relation `H_1=(1/(8 pi^2)) sum_l (1-P_{l,l+1})` with anomalous-dimension map is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilitySingleMagnonDispersion,
      "The one-loop single-magnon quantization/dispersion relations `p=2 pi n/L` and `epsilon(p)=(1/(2 pi^2)) sin^2(p/2)` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityHeisenbergBetheRoots,
      "The one-loop Heisenberg Bethe-root equations with the cyclicity/product constraint are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityBmnPpWaveMap,
      "The BMN/pp-wave charge map `P_+ = -mu(Delta-J)` and `P_- = -(Delta+J)/(2 mu R^2)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityPpWaveSpectrum,
      "The pp-wave lightcone oscillator spectrum `omega_n = sqrt(mu^2 + n^2/(alpha' p^+)^2)` with `p^-` summation and level-matching constraint is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityMagnonDispersion,
      "The centrally-extended all-order magnon dispersion relation `E = sqrt(1 + 16 h(lambda)^2 sin^2(p/2))` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityWeakCouplingMap,
      "Weak-coupling matching of the magnon interpolating coupling `h(lambda)=sqrt(lambda)/(4 pi)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityZhukovskyVariables,
      "Zhukovsky-variable kinematics (`x^+/x^- = e^{ip}`, `x^+ + 1/x^+ - x^- - 1/x^- = i/h`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilitySMatrixConsistency,
      "Magnon scalar-factor analytic-unitarity and crossing consistency equations are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityCuspBesEquation,
      "The BES/ABA cusp-anomalous-dimension relation `Gamma_cusp = 4 h^2 (1 + 4 h Int_BES)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityCuspStrongCoupling,
      "The strong-coupling cusp asymptotic form `Gamma_cusp = 2h - (3 log 2)/(2 pi) + O(1/h)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityBetheYangSystem,
      "Nested Bethe-Yang factorization for level-I transfer phases and level-II/III scattering contributions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5IntegrabilityBoundStateDispersion,
      "Bound-state magnon (`Q`-particle) dispersion `E = sqrt(Q^2 + 16 h(lambda)^2 sin^2(p/2))` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorDoubleWickMap,
      "The mirror-model double-Wick kinematic map `E=i p_tilde`, `p=i E_tilde` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorMagnonDispersion,
      "The mirror-magnon dispersion relation derived from double-Wick continuation of AdS5xS5 magnon kinematics is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorSingleSpeciesTba,
      "The one-species mirror thermodynamic-Bethe-ansatz pseudo-energy equation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorExcitedStateQuantization,
      "The excited-state mirror-TBA quantization condition at zeros of `1+exp(-zeta)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorBetheYangSystem,
      "Factorized mirror Bethe-Yang equations for finite-volume spectra are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorBetheStrings,
      "The mirror Bethe-string taxonomy (`bullet`, `oplus/ominus`, `n|yw`, `n|w`) and associated Zhukovsky branch structure are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorTbaEquationSystem,
      "The coupled multi-species mirror-TBA equation system for the AdS5xS5 integrable model is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorYSystemHirota,
      "The finite-volume mirror Y-system and equivalent Hirota bilinear system on the T-hook domain are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorFiniteVolumeEnergy,
      "The finite-volume excited-state energy formula combining physical magnons and mirror thermal-bath contributions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorKonishiWrapping,
      "The mirror-TBA wrapping-correction package for the Konishi multiplet is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorQuantumSpectralCurvePMu,
      "The AdS5xS5 quantum-spectral-curve (`Pmu`) equations, including monodromy and quadratic constraints, are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorPMuAsymptotics,
      "Large-`u` asymptotic conditions for `P_a`, `mu_ab`, and coefficient products in the `Pmu` system are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorWeakCouplingBaxter,
      "Weak-coupling reduction of the `Pmu` system to the one-loop `SL(2)` Baxter equation and anomalous-dimension sum rule is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringAdS5MirrorSmallSpinExpansion,
      "Analytic small-spin continuation around the BPS point in the `Pmu` system is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringWilsonMaldacenaLoopSaddle,
      "The strong-coupling holographic saddle formula for Maldacena-Wilson loop expectation values with the standard perimeter subtraction is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringWilsonQuarkAntiquarkPotentialStrongCoupling,
      "The rectangular-loop strong-coupling potential relation `V(L) = -4 pi sqrt(lambda)/((Gamma(1/4))^4 L)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringWilsonCuspLargeAngleRelation,
      "The large-Lorentzian-angle cuspy Wilson-line relation `Delta_cusp(pi-iC) = (1/2) Gamma_cusp C` together with the strong-coupling `Gamma_cusp` scaling is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringWilsonBremsstrahlungFunction,
      "The small-angle cusp/bremsstrahlung package `Delta_cusp = -B angle^2`, `A = 2 pi B`, and planar localization expression for `B(lambda,N)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringWittenConfinementCircleData,
      "Witten-model circle compactification relations for `L`, `g_4`, `M_KK` and anti-periodic fermion boundary conditions are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringWittenConfiningStringTension,
      "Witten-model linear quark-antiquark potential and equivalent confining-string tension formulas in terms of geometric and 4D gauge-theory parameters are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSakaiSugimotoChiralSymmetryBreaking,
      "Sakai-Sugimoto chiral-holonomy transformation law `U -> g_+ U g_-^{-1}` and diagonal unbroken flavor subgroup identification are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSakaiSugimotoPionSkyrmeAction,
      "Sakai-Sugimoto pion effective-action coefficient package (including Skyrme-term coefficients and `f_pi` kinetic normalization relation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSakaiSugimotoEtaPrimeMass,
      "The Sakai-Sugimoto eta-prime mass formula from RR two-form dynamics and anomalous `U(1)_A` coupling is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSakaiSugimotoMesonSpectrum,
      "The leading scalar/vector meson mass-ratio package from D8 fluctuation eigenmodes in Sakai-Sugimoto holographic QCD is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringKlebanovWittenMarginalConifoldData,
      "Klebanov-Witten conifold fixed-point data (`gamma_AB = -1/2`, quartic chiral operator dimension, and exactly marginal family structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringKlebanovWittenAdS5T11Duality,
      "The AdS5 x T^{1,1} geometric parameter map (including `vol(T^{1,1})` and `R^4` relation) for Klebanov-Witten duality is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringKlebanovTseytlinFluxRunning,
      "The Klebanov-Tseytlin effective-rank running relation `N_eff = N + (3/(2 pi)) g_s M^2 log(r/r0)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringKlebanovCascadeSeibergDualStep,
      "The cascade rank-step map `(N+M,N) -> (N,N-M)` of Seiberg-dual flow is assumed at the interface level in this abstraction layer."⟩
  , ⟨AssumptionId.stringKlebanovStrasslerConfinement,
      "Klebanov-Strassler confining-string tension and glueball-scale relations at the warped-conifold tip are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixBfssUpliftParameters,
      "The BFSS uplift parameter relations linking D0-brane harmonic coefficient `c0` to type-IIA and M-theory scales are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixBfssNearHorizonDuality,
      "The BFSS near-horizon harmonic profile/source package (`f0(r) ~ c0 N/r^7`, with `T_yy` scaling) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixBfssBlackHoleThermodynamics,
      "The near-extremal D0 black-hole thermodynamic relation for inverse temperature and Hawking temperature in the BFSS regime is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixBfssMicrocanonicalEntropyScaling,
      "Canonical and microcanonical BFSS entropy scaling relations (`S ~ N^(7/5) betaBar^(-9/5)` and `S ~ N^(1/2) (E/M)^(9/14)`) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixBfssMomentumMap,
      "The D0-charge to asymptotic supergraviton momentum/energy map (`E`, `P_y`, `P_i`) in BFSS kinematics is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixBfssSmatrixConjecture,
      "The BFSS conjecture that reduced MQM amplitudes converge to reduced M-theory supergraviton amplitudes in the large-`N` limit is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixGaugeCouplingDuality,
      "The matrix-string coupling relation `g_A = 1/(sqrt(2 pi) g_YM R)` from the duality chain is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixSymmetricOrbifoldIrLimit,
      "The matrix-string infrared symmetric-product-orbifold package (`Sym^N(R^8)` with cycle decomposition sectors) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixDvvTwistDeformation,
      "The DVV twist-field deformation package with weight `(3/2,3/2)` and coupling proportional to `a0/g_YM` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixDvvCoefficientNormalization,
      "The DVV-coupling normalization value `a0 = -2^(5/2) pi^(3/2)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixTreeAmplitudeMatching,
      "The leading matrix-string to covariant-string tree-level amplitude matching relation with lightcone assignment `k_i^+ = N_i` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringMatrixStringConjectureLargeN,
      "The matrix-string conjecture that normalized connected amplitudes converge to covariant string connected amplitudes in the large-`N` limit is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringConventionsBosonicNormalizationPackage,
      "Appendix-A bosonic normalization conventions (`N_{h,n}=g_s^(n+2h-2)` and `K_{S^2}=8 pi/kappa^2`) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringConventionsGravitationalCouplingRelations,
      "Cross-theory coupling conventions `kappa=2 pi g_s` (bosonic), `kappa=(pi/2) g_s` (type II), `kappa=pi g_s` (heterotic), and heterotic `g_YM` relations are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringConventionsBosonicDpTensionRelations,
      "Appendix-A bosonic open/closed coupling and Dp-brane tension relations (`g_s=g_o^2`, `T_p=1/(2 pi^2 alpha' g_o^2)`, and `T_p` in terms of `kappa`) are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringConventionsTypeIIDpTensionRelation,
      "Appendix-A type-II Dp-brane tension relation `T_p=(sqrt(pi)/kappa)(4 pi^2 alpha')^((3-p)/2)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringConventionsTypeIIDimensionlessCouplings,
      "Appendix-A type-II dimensionless-coupling relations among `g_A`, `g_B`, D-brane tensions, `kappa`, and `g_s` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringConventionsMTheoryScaleTensionRelations,
      "Appendix-A M-theory scale/tension relations linking `kappa_11`, `alpha'`, `g_A`, `M_11`, `T_M2`, and `T_M5` are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeGaugeFixedModuliAmplitude,
      "The gauge-fixed moduli-space formula for genus-`h` closed-string amplitudes (`A_h = N_{h,n} ∫_{M_{h,n}} Ω`) with `dim_R(M_{h,n}) = 6h-6+2n` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeBeltramiBInsertion,
      "Equivalence between Beltrami-differential and contour representations of `b`-ghost insertions in perturbative string amplitudes is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeGhostNumberAnomaly,
      "The worldsheet ghost-number anomaly package (`∇·j_gh = -(3/4)R` and genus-dependent ghost-number selection rule) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeBrstBoundaryVariation,
      "BRST variation of moduli-space integrands being exact up to boundary contributions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativePlumbingFixtureDegeneration,
      "The plumbing-fixture degeneration map `z' = q/z` with `|q|<1` and cylinder-length relation `-log|q|` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeTreeUnitarityFactorization,
      "Tree-level one-particle channel factorization of reduced amplitudes with denominator `(P^2+M^2-iε)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeNormalizationRecursion,
      "Perturbative normalization recursion from factorization, including the sphere normalization `K_{S^2}=8 pi/alpha'`, is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeVirasoroShapiroKernel,
      "The four-tachyon Virasoro-Shapiro reduced-amplitude package (`s+t+u=16/alpha'`, `A_0=(8 pi/alpha') g_s^2 F`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeOneLoopTorusMeasure,
      "The one-loop torus fundamental-domain/measure package with ghost factor `|eta(τ)|^4/(2 τ_2)` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringPerturbativeCOneThermalDuality,
      "The `c=1` one-loop thermal-circle duality package (`R_dual=alpha'/R` and duality-invariant vacuum-density expression) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativeGaugeFixingSupermoduli,
      "The supermoduli gauge-fixing package for perturbative superstrings (`exp(iS)` weight with complex action functional, dimension bookkeeping, and FP-reduced amplitude map) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativeSrsReparameterization,
      "The super-Riemann-surface transition package preserving the superconformal distribution and worldsheet diffeomorphism/reparameterization invariance is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativeOddModuliCounting,
      "The odd-supermoduli counting package (`dim_odd = 2g-2+n_NS`) with matching odd-Beltrami and PCO insertion counts is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativeBerezinianIntegration,
      "The supermoduli Berezinian integration package (degree bookkeeping and codimension-one corrected global integral) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativePlumbingFactorization,
      "The superstring plumbing-fixture and one-particle-channel factorization package (`w' = q/w`, `|q|<1`, propagator pole structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativePcoFormalism,
      "The picture-changing formalism package (PCO count equals odd-moduli dimension, BRST-closed integrand, BRST-exact position shifts) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativeSpuriousSingularityControl,
      "The spurious-singularity control package from beta-gamma/theta-section determinant structure with cancellation of unphysical poles is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperPerturbativeVerticalIntegration,
      "The full PCO-contour vertical-integration package (horizontal plus vertical contour contributions with BRST-exact patch jumps) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitTreeLevelPcoAmplitude,
      "The tree-level superstring explicit-computation package for PCO counting (`d_o = n_NS + n_R/2 - 2` by chirality) and normalization `A_0 = i^(n-3) ∫_{S_{0,n}} Ω~` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitNsnsPictureRaising,
      "The NSNS picture-raising package for PCO-collision limits and integrated-vertex conversion (`b_{-1}\\tilde b_{-1} V^(0,0) = (1/4) G_{-1/2}\\tilde G_{-1/2} V^m`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitNsnsThreePointSupergravity,
      "The tree-level three-point NSNS match to Einstein-Hilbert kinematics with `kappa=(pi/2) g_s` and absence of independent on-shell `R^2`/`R^3` terms is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitNsnsFourPointTreeKernel,
      "The tree-level four-point NSNS Virasoro-Shapiro kernel package (`s+t+u=0` with `K_NS` tensor factor and gamma-ratio structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitFourPointLowEnergyExpansion,
      "The low-energy expansion package of the four-point gamma kernel (supergravity pole plus `zeta(3)`-controlled `alpha'^3 R^4` term and threshold nonanalyticity) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitRrFourPointTreeKernel,
      "The tree-level four-point RR kernel package (no PCO required for four Ramond punctures on the sphere, with RR tensor factor and common gamma-ratio structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitOneLoopNsnsSpinStructure,
      "The genus-one NSNS spin-structure contour package (`dim S_{1,n,epsilon}=2n`, `(i^n)/4` prefactor, torus `Z_2` puncture redundancy, and odd-spin PCO-separation prescription) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitOneLoopNsnsVanishingLowMultiplicity,
      "The one-loop NSNS low-multiplicity vanishing package (`n<=3`) from Jacobi-theta identities and transversality constraints is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitOneLoopNsnsFourPointLeading,
      "The one-loop four-point NSNS leading low-energy package with modular integral value `pi/6` and prefactor scaling `g_s^4 /(2^10 pi^2 alpha')` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitOneLoopRrFourPoint,
      "The one-loop four-point RR package using Ramond theta identities and the expected RR tensor contraction times the bosonic torus integral is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitHigherGenusGhostCorrelators,
      "The higher-genus ghost-correlator package for `(b_lambda,c_{1-lambda})` and `beta-gamma` systems, including anomaly counting and theta/prime-form/inverse-theta structures, is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitHigherLoopVacuumVanishing,
      "The higher-loop vacuum-amplitude vanishing package (`h>=2`) from supersymmetry/BRST contour reduction with vertical slits and `oint dxi = 0` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperExplicitFourGravitonCouplingFunction,
      "The full four-supergraviton coupling-function package `A_4 ~ K_NS f(s,t;g_s)`, including the perturbative `alpha'^0` one-loop shift and absence of further perturbative `alpha'^0` corrections, is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftClosedFieldSpaceHZero,
      "The closed-string-field kinematic space constraint package (`b_0^- Psi = 0`, `L_0^- Psi = 0`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftOffShellAmplitudeCycle,
      "The off-shell SFT amplitude construction by integration over a `(6h-6+2n)`-cycle in `P-hat_{h,n}` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftBrstExteriorDerivativeIdentity,
      "The off-shell BRST identity `Omega[Q_B Psi] = - d Omega[Psi]` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftPlumbingCycleCompatibility,
      "Compatibility of off-shell integration cycles with plumbing-fixture sewing limits near degeneration boundaries is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftSiegelGaugePropagator,
      "The Siegel-gauge internal-line propagator kernel `b_0^+ b_0^- / L_0^+` in off-shell SFT factorization is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftOnePiEffectiveActionSiegel,
      "The Siegel-gauge 1PI effective-action decomposition into kinetic minus interaction contributions is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftClassicalEquationWithBrackets,
      "The classical closed-SFT equation package `E[Psi] = Q_B Psi + sum (1/n!)[Psi^n] = 0` is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftStringBracketDuality,
      "Duality between the string bracket and `(n+1)`-string vertex pairing (`<Phi|c_0^-|[Psi^n]> = {Phi,Psi^n}`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftLInfinityHomotopyIdentity,
      "The homotopy-Lie (L-infinity) identity balance implied by the geometric master equation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftMasslessFieldDictionary,
      "The low-derivative massless-field dictionary between flat-bracket SFT variables and covariant spacetime fields (`G`, `B`, `Phi`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSftBackgroundIndependenceMap,
      "Background-independence maps between nearby CFT-defined SFTs preserving symplectic data and measure-weighted action are assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftFieldSpaceNsrAuxiliary,
      "The closed super-SFT NS/R field-space package (`Q_B` nilpotency, `b_0^-`/`L_0^-` constraints, GSO projection, auxiliary Ramond `-3/2` picture sector) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftOffShellAmplitudeChain,
      "The off-shell closed super-SFT amplitude-chain package (`dim S = 6h-6+2n`, NS/R-dependent PCO counts, vertical-boundary chain data over spin structures) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftRamondPlumbingPcoCompatibility,
      "The Ramond plumbing compatibility package (averaged PCO insertions, degeneration compatibility, and spurious-singularity control) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftOnePiPictureAdjustedPropagator,
      "The super-SFT 1PI package with picture-adjusted Siegel propagator (`(b_0^+ b_0^- / L_0^+) G`) and Legendre-equivalent effective action is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftRamondTowerRegularization,
      "The Ramond-tower regularization package (infinite `B_0^n` degeneracy controlled by picture-raising so only finitely many nonzero propagator contributions survive) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftBvQuantumMasterEquation,
      "The BV quantum closed super-SFT package (canonical BV pairing, geometric master equation, and quantum master equation with Ramond picture adjustment) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftRrKineticTermMatching,
      "The RR kinetic-term matching package (auxiliary-field super-SFT kinetic structure reproducing supergravity RR two-point data, including type-IIB self-duality handling) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftFieldEquationBracketPackage,
      "The super-SFT field-equation package (`Q_B Psi + sum (1/n!)[Psi^n] = 0`) with bracket data induced by 1PI auxiliary pairing is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftFlatBracketVerticalCorrection,
      "The flat-frame super-SFT bracket package (`G`-adjusted two-string bracket and vertical-correction three-string bracket with homotopy compatibility) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringSuperSftPpWaveSolutionPackage,
      "The pp-wave massless-solution package (RR five-form plus NSNS metric deformation solving the massless super-SFT equation to all orders via boost-charge selection) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticWorldsheetChiralSupersymmetry,
      "The heterotic worldsheet package (chiral local supersymmetry, `(0,1)` gauge-fixed SCFT, central-charge/anomaly cancellation with 32 left-moving fermions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticLambdaGsoCurrentAlgebras,
      "The heterotic `lambda`-sector GSO package (modular-invariant chiral projections realizing either `Spin(32)/Z_2` or `E8 x E8` current algebras with Narain-lattice descriptions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticPhysicalSpectrumCohomology,
      "The heterotic BRST/Siegel physical-spectrum package (level matching with right-moving GSO, tachyon-free spectrum, and massless `N=1` supergravity/gauge multiplets) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticPerturbativeAmplitudePrescription,
      "The heterotic perturbative amplitude package (anti-holomorphic supermoduli integration with PCO-equivalent contour prescription and spurious-singularity control) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticTreeLevelEffectiveCouplings,
      "The heterotic tree-level effective-coupling package (`kappa = pi g_s`, `g_YM = 2 pi g_s / sqrt(alpha')`, `R^2` correction and no independent tree-level `R^3`) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticGreenSchwarzAnomalyCoupling,
      "The heterotic Green-Schwarz anomaly-cancellation package (`B_2 wedge X_8` with odd-spin one-loop origin and anomaly-canceling `B` variation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticNonBpsSpinorMassRenormalization,
      "The heterotic non-BPS `SO(32)` spinor mass-renormalization package (classical `m^2=4/alpha'`, positive one-loop shift, and off-shell 1PI pole control) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticBackgroundNlsmGaugeLorentzAnomaly,
      "The heterotic background `(0,1)` NLSM package (gauge/lorentz anomaly compensation via `B` transformation, gauge-invariant `H-hat`, modified Bianchi identity, and beta-function structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticCalabiYauStandardEmbedding,
      "The heterotic Calabi-Yau standard-embedding package (Hermitian gauge bundle, `(0,2)` enhancement, `H-hat` simplification, and expected 4D `N=1` unbroken gauge algebra) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticStromingerSystem,
      "The heterotic Strominger-system package (integrable complex/Hermitian geometry with torsion, corrected `H-hat` equation, Hermitian Yang-Mills constraints, and supersymmetry conditions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticFourDEffectiveFiPotential,
      "The heterotic 4D effective/FI package (anomalous `U(1)` axion shift, dilaton-dependent moment-map term, and induced `D`-term scalar potential) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticOneLoopFiMassTerm,
      "The heterotic one-loop Fayet-Iliopoulos mass package (`delta m^2 = q kappa^2 (h^{2,1}-h^{1,1}) /(3 pi^2 alpha'^2)` from torus two-point/index analysis) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticTwoLoopVacuumEnergyFromBoundary,
      "The heterotic two-loop vacuum-energy package (genus-two boundary/degeneration reduction with spurious-residue control and torus-current factorization) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringHeteroticShiftedVacuumSupersymmetryRestoration,
      "The shifted heterotic vacuum package (charged-scalar VEV cancels FI `D`-term and restores spacetime supersymmetry when both charge signs are present) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneBosonicBoundaryConditions,
      "The bosonic D-brane boundary-condition package (conformal/BRST-preserving boundary constraints with Neumann-Dirichlet split and doubling-trick realization in 26D) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneBosonicBoundaryStateNormalization,
      "The bosonic D-brane boundary-state package (oscillator/ghost gluing plus boundary-state normalization fixed by cylinder open/closed duality) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneOpenBosonicSpectrum,
      "The open bosonic D-brane spectrum package (`alpha' k_parallel^2 + N - 1 = 0`, level-0 tachyon, and level-1 vector/scalar states with gauge redundancy) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneBoundaryMarginalDeformations,
      "The D-brane boundary marginal-deformation package (worldvolume gauge/scalar couplings, linearized marginality equations, and transverse position shifts) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneChanPatonGaugeEnhancement,
      "The Chan-Paton gauge-enhancement package (`H_(B^n,B^n) ~ H_(B,B) tensor Mat(n)`, stretched-string `W` mass, and `U(n)` enhancement at coincidence) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneTypeIIBpsBoundarySupersymmetry,
      "The type-II BPS D-brane boundary package (superconformal/fermion gluing, parity constraints, and half-supersymmetry preservation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneOpenSuperstringSpectrum,
      "The open superstring D-brane spectrum package (`alpha' k^2 + N = 0` with GSO removal of NS tachyon and massless NS/R worldvolume multiplets) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneBpsBoundaryStateRrCharge,
      "The BPS D-brane boundary-state package (NSNS+RR components, modular-crossing consistency, RR charge, and anti-brane sign flip) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneNonBpsConstruction,
      "The non-BPS D-brane construction package (brane-antibrane projection, pure-NSNS boundary state, vanishing RR charge, full SUSY breaking, and tachyon instability) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneIntersectingNdSpectrum,
      "The intersecting D-brane ND-spectrum package (`m_NS^2 = ((d_ND/8)-1/2)/alpha'`, massless R intersection fermions, and `d_ND mod 4` supersymmetry pattern) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneAtAnglesStabilityBpsCondition,
      "The D-branes-at-angles package (angle-dependent lowest NS masses, tachyon criterion, and equal-angle quarter-BPS condition) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicOpenClosedPerturbation,
      "The bosonic D-brane-dynamics open+closed perturbation package (moduli-space amplitude sum, boundary orientation/sign conventions, open-channel plumbing-factorization, and unitarity normalization recursion) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicDiscTachyonAmplitudes,
      "The bosonic D-brane-dynamics disc tachyon-amplitude package (disc normalization, three-tachyon coupling, and four-point Veneziano channel structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicDiscChanPatonGaugeStructure,
      "The bosonic D-brane-dynamics disc Chan-Paton/gauge package (trace ordering, nonabelian commutator structures, and adjoint tachyon couplings on coincident branes) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicCylinderOpenClosedDuality,
      "The bosonic D-brane-dynamics cylinder package (open-trace/closed-boundary-state dual representations, modular crossing, and massless closed-exchange extraction) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicNambuGotoTensionMatching,
      "The bosonic D-brane-dynamics Nambu-Goto package (worldvolume reparameterization invariance, induced-metric expansion, and low-energy tension matching to open-string amplitudes) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicDilatonTDualityRelations,
      "The bosonic D-brane-dynamics dilaton/T-duality package (dilaton prefactor, radius/coupling duality map, and Dp-to-D(p-1) energy-density consistency) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicBornInfeldGaugeInvariance,
      "The bosonic D-brane-dynamics Born-Infeld gauge package (B-field/worldvolume gauge invariance and `G+B+2 pi alpha'F` DBI dependence for slowly varying fields) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicGravitonDilatonExchange,
      "The bosonic D-brane-dynamics graviton/dilaton exchange package (Einstein-frame linearization, gauge-fixed propagators, and matching to cylinder massless exchange) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicCOneZzRollingTachyon,
      "The `c=1` bosonic D-brane-dynamics ZZ/rolling-tachyon package (cylinder-crossing boundary state, open tachyon instability, and rolling-tachyon marginal deformation with MQM interpretation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsBosonicCOneFzztLongStrings,
      "The `c=1` bosonic D-brane-dynamics FZZT/long-string package (boundary-wavefunction crossing relations, stability range, ZZ-FZZT stretched-string energy relation, and long-string MQM duality) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIOpenClosedPerturbation,
      "The type-II D-brane-dynamics open+closed perturbation package (BSRS transition/boundary-spin data, supermoduli/PCO prescriptions with vertical integration, and normalization conventions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIDiscOpenGaugeAmplitudes,
      "The type-II D-brane-dynamics disc open-gauge package (Chan-Paton ordered 3/4-point amplitudes, Yang-Mills matching, and leading `alpha'^2 t8 F^4` correction) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIDiscOpenClosedRrCouplings,
      "The type-II D-brane-dynamics disc open+closed RR package (RR/NS disc amplitude, `A wedge F_p` and transverse-displacement couplings, and Dp RR charge identification) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIICylinderNsnsRrCancellation,
      "The type-II D-brane-dynamics cylinder package (NSNS/RR channel decomposition, Jacobi-theta cancellation for parallel BPS branes, and anti-brane RR-sign reversal) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIBpsKappaSymmetricAction,
      "The type-II BPS D-brane kappa-symmetric action package (supersymmetric DBI+WZ structure, projector constraints, static-gauge reduction, and tension matching) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIBpsBackgroundCouplings,
      "The type-II BPS D-brane background-coupling package (DBI dependence on `G,B,Phi,F`, RR Wess-Zumino sum, and force-cancellation consistency) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIRrChargeDiracQuantization,
      "The type-II D-brane RR-charge quantization package (electric/magnetic dual sourcing, Dirac quantization, and physical coupling dictionaries) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIWrappedBraneSupersymmetry,
      "The type-II wrapped-D-brane supersymmetry package (kappa-projector criterion and preserved-supercharge condition for classical embeddings) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIID2HolomorphicCurveBps,
      "The type-II D2 holomorphic-curve BPS package (complex-holomorphic embedding projectors with flat/compactified preserved-supersymmetry fractions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIID3SpecialLagrangianBps,
      "The type-II D3 special-Lagrangian BPS package (phase-aligned SLag condition and corresponding supersymmetry projectors) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIIWorldvolumeFluxBion,
      "The type-II worldvolume-flux BPS package (BIon condition, quarter-BPS projector, and F1-charge/tension interpretation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIINonAbelianStackedEffectiveTheory,
      "The type-II stacked-D-brane non-Abelian effective-theory package (maximally supersymmetric Yang-Mills content, commutator potential, and brane-separation vacuum interpretation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDbraneDynamicsTypeIID0ScatteringBfssMatrixQM,
      "The type-II D0 scattering/BFSS package (moving-brane cylinder amplitude, `v^4/r^7` long-distance behavior, matrix-QM supercharge algebra, and threshold-bound-state statement) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftClassicalBvAInfinityStructure,
      "The classical bosonic OSFT BV package (field/antifield split, cyclic vertices from boundary moduli, and geometric master-equation consistency) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftEquationGaugeAInfinityRelations,
      "The bosonic OSFT equation/gauge package (`Q_B` plus open-string brackets forming `A_infinity`, with `Q_Psi` gauge generator and nilpotency/equation equivalence) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftWittenCubicStarAlgebra,
      "Witten's cubic OSFT package (quadratic-differential strip decomposition, associative star product, cubic action, and corresponding gauge transformations) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftTachyonCondensationLevelTruncation,
      "The OSFT level-truncation tachyon-condensation package (nontrivial tachyon potential extrema with improved higher-level tension cancellation approaching full brane-tension removal) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftKbcAlgebraWedgeStates,
      "The wedge-state/`KBc` algebra package (wedge semigroup, sliver-frame representation, and `K,B,c` BRST/anticommutation relations) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftTachyonVacuumExactSolution,
      "The analytic `KBc` tachyon-vacuum package (exact OSFT solution, trivial `Q_Psi` cohomology, and exact D-brane tension cancellation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftMarginalDeformationKiermaierOkawa,
      "The Kiermaier-Okawa marginal-deformation OSFT package (left/right complex solutions, regularized OPE prescription, and real-solution reconstruction by gauge dressing) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftRollingTachyonCovariantPhaseSpace,
      "The rolling-tachyon OSFT package (covariant phase-space symplectic form with midpoint projection regularization and energy extraction consistent with Ellwood/worldsheet data) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftErlerMaccaferriIntertwiningSolution,
      "The Erler-Maccaferri OSFT package (intertwining fields, homotopy/flag-state construction, and background-independent multi-brane solutions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftQuantumOpenClosedBvVertices,
      "The quantum open+closed bosonic SFT BV package (genus/boundary vertices, exceptional disc one-point treatment, and hyperbolic/geometric vertex consistency including Witten-cubic limit) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOsftOpenClosedSuperBvActionAndTadpoles,
      "The open+closed super-SFT BV package (NS/R plus auxiliary picture field spaces, PCO-chain vertices, and linearized closed-string source/tadpole structure around D-branes) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDinstantonTransseriesAndModuliIntegral,
      "The D-instanton transseries/moduli package (perturbative plus D-instanton sectors, disconnected-worldsheet exponentiation, and non-perturbative treatment of boundary divergences) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDinstantonCOneZzContributionAndNormalization,
      "The `c=1` ZZ-instanton package (instanton action dictionary, dual matrix-model bounce interpretation, and normalized leading `1 -> n` non-perturbative amplitude) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDinstantonTypeIIBAxioDilatonExpansion,
      "The type-IIB D(-1)-instanton package (axio-dilaton action map, discrete axion-shift remnant, and instanton-corrected four-supergraviton coupling structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDinstantonOpenClosedSftZeroModeGaugeFixing,
      "The D-instanton open+closed-SFT zero-mode package (collective-mode/moduli reparameterization, relaxed Siegel gauge, FP replacement by gauge-volume factor, and contour/Wick-rotation prescriptions) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDinstantonNormalizationFromZeroModeMeasure,
      "The D-instanton normalization package (open-string zero-mode measure extraction with gauge-angle fixing and leading `R^4`-sector coefficient matching) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDinstantonMultipleIkktIntegralScaling,
      "The multiple D-instanton IKKT package (`U(k)` Chan-Paton/zero-mode promotion, matrix-integral normalization, and `sqrt(k) Z(k)` scaling of leading `R^4` corrections) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeIUnorientedWorldsheetParityProjection,
      "The type-I unoriented-worldsheet parity package (gauged orientation reversal, `Omega`-invariant state projection, crosscap Euler-characteristic bookkeeping, and NSNS `B`-field projection) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeICrosscapStateAndKleinBottleDuality,
      "The type-I crosscap package (crosscap gluing conditions, explicit crosscap state, Klein-bottle modular crossing, and Mobius-fixable normalization sign) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeIClosedOpenOmegaProjectionSpectrum,
      "The type-I closed/open projection package (type-IIB parent with `Omega` action on matter/ghost/superghost sectors, RR-spectrum reduction, and `SO/Sp` Chan-Paton algebra outcomes) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeITadpoleCancellationSO32,
      "The type-I tadpole-cancellation package (NSNS/RR crosscap and D9 boundary-state matching with unique `SO(32)` cancellation condition) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeIAmplitudeNormalizationUnorientedOpenClosed,
      "The type-I unoriented open+closed amplitude-normalization package (PCO/spin-structure fiber integration, unitarity normalization, and `Omega`-invariant factorization) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeIVacuumAmplitudeTopologyAndCancellation,
      "The type-I vacuum-amplitude package (torus/Klein/cylinder/Mobius one-loop sectors, tadpole-controlled divergence cancellation, and supersymmetric vacuum-energy vanishing) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeIEffectiveActionGaugeGravityCouplings,
      "The type-I effective-action package (functional gauge/gravity coupling dictionary with RR Chern-Simons and Green-Schwarz anomaly-cancellation couplings) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeIBpsD1D5BraneSpectrum,
      "The type-I BPS D1/D5 package (`Omega`-compatible brane sectors, Chan-Paton symmetry constraints, and D1/D5 with D9-induced massless spectra) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringTypeINonBpsD0StabilityAndFermions,
      "The type-I non-BPS D0 package (`Omega` tachyon projection, residual `Z_2` gauge structure, and D0-D9 fermionic zero-mode spectrum/stability data) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringOrientifoldPlaneCrosscapChargeDictionary,
      "The orientifold-plane package (`Omega * I` quotient construction, crosscap normalization, `O p^+ / O p^-` classification, and charge/tension relations via duality checks) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityHeteroticTypeIStrongWeak,
      "The heterotic/type-I duality package (Einstein-frame dictionary, opposite-dilaton map, D1/fundamental-string and NS5/D5 matching, and non-BPS state correspondence) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityTypeIINS5BpsSoliton,
      "The type-II NS5 BPS package (quantized H-flux, supersymmetric harmonic-profile solution, and NS5 tension scaling) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityNS5ThroatLittleStringScft,
      "The NS5-throat package (linear-dilaton plus `SU(2)_k` worldsheet factorization and little-string-theory interpretation) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityHeteroticNS5GaugeInstantonSmallInstanton,
      "The heterotic NS5/small-instanton package (self-dual instanton equations, modified-Bianchi dilaton profile, and instanton-to-NS5 limit) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityTypeIIBSdualityModularInvariantCouplings,
      "The type-IIB S-duality package (`SL(2,Z)` action and modularly completed protected couplings, including `R^4` Eisenstein-structure checks) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityPQStringsAndFiveBranes,
      "The `(p,q)`-state package (worldvolume electric-flux quantization, `SL(2,Z)` orbits, and `(p,q)` string/five-brane BPS tension structure) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityBlackPBraneSupergravityDictionary,
      "The black p-brane package (RR flux quantization, warped supergravity solutions, and charge/radius parameter dictionaries) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityD7BraneFTheoryEllipticMonodromy,
      "The D7/F-theory package (axio-dilaton monodromies, elliptic-fibration/j-invariant construction, and Sen-limit orientifold identification) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityMTheoryTypeIIACircleRelation,
      "The M-theory/type-IIA circle package (11D reduction, D0/Kaluza-Klein map, and Planck-scale/radius dictionaries) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityM2M5BraneTensionDictionary,
      "The M2/M5 package (electric/magnetic C3-charge sectors with wrapped-brane maps to F1/D4 and tension dictionaries) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityD6KaluzaKleinMonopoleUplift,
      "The D6/KK-monopole package (Taub-NUT uplift, smooth-core/orbifold structure, and half-BPS compatibility) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityMTheoryHigherDerivativeProtectedTerms,
      "The M-theory higher-derivative package (protected `R^4`/related terms from type-IIA decompactification and strong-coupling limits) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityHeteroticE8SO32CircleTduality,
      "The heterotic circle T-duality package (Narain-lattice isomorphism with Wilson lines and hetE/hetO radius/momentum map) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityHeteroticStrongCouplingMTheoryInterval,
      "The strong-coupling hetE package (duality chain to M-theory on interval, boundary `E8 x E8`, and stretched-M2 heterotic-string realization) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityHoravaWittenBoundaryAnomalyInflow,
      "The Horava-Witten package (boundary conditions for `G_4`, anomaly inflow from bulk Chern-Simons terms, and boundary-coupling matching) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.stringDualityMassiveIIARomansD8System,
      "The massive-IIA Romans package (`F_0` quantization, T-dual axion monodromy interpretation, and D8/O8 consistency structure) is assumed in this abstraction layer."⟩
  ]

end PhysicsLogic
