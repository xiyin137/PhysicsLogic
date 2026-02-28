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
def bvDifferentialNilpotent : String := "qft.bv.differential_nilpotent"
def bvDifferentialNZero : String := "qft.bv.differential_n_zero"
def bvGaugeIndependence : String := "qft.bv.gauge_independence"
def tqftModularRelation : String := "qft.tqft.modular_relation"
def tqftZ3ModularAxioms : String := "qft.tqft.z3_modular_axioms"
def tqftSu24FusionAxioms : String := "qft.tqft.su24_fusion_axioms"
def tqftSu24RibbonAxioms : String := "qft.tqft.su24_ribbon_axioms"
def tqftIsingModularAxioms : String := "qft.tqft.ising_modular_axioms"
def osReconstruction : String := "euclidean.os_reconstruction"
def ghsInequality : String := "euclidean.ghs_inequality"
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
def schwarzschildMetricWellFormed : String := "gr.schwarzschild_metric_well_formed"
def conformalPreservesNull : String := "spacetime.conformal_preserves_null"
def conformalPreservesCausalStructure : String := "spacetime.conformal_preserves_causal_structure"
def cftCrossRatiosPositiveFromPoints : String := "qft.cft.cross_ratios_positive_from_points"
def cftTDualWeightSymmetry : String := "qft.cft.2d.t_dual_weight_symmetry"
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
  , ⟨AssumptionId.bvDifferentialNilpotent,
      "Nilpotency of the BV differential under the classical master equation is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvDifferentialNZero,
      "Vanishing of higher BV differential iterates (n >= 2) is assumed in this abstraction layer."⟩
  , ⟨AssumptionId.bvGaugeIndependence,
      "Gauge-fixing independence in BV via BV-exact variation is assumed in this abstraction layer."⟩
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
  ]

end PhysicsLogic
