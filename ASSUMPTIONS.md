# Physics Assumptions Report

- Registered assumptions: `73`
- Assumptions referenced in non-Papers modules: `73`
- Assumptions with zero references outside registry: `0`

| AssumptionId | Payload | Core refs | Papers refs | Total refs | Description |
| --- | --- | ---: | ---: | ---: | --- |
| `aqftAnyonsIn3d` | `qft.aqft.anyons_in_3d` | 1 | 0 | 1 | Existence of anyonic exchange-phase parametrization in d = 3 is assumed in this abstraction layer. |
| `aqftBisognanoWichmann` | `qft.aqft.bisognano_wichmann` | 1 | 0 | 1 | Bisognano-Wichmann wedge modular-flow identification is assumed in this abstraction layer. |
| `aqftBoseFermiAlternative` | `qft.aqft.bose_fermi_alternative` | 1 | 0 | 1 | Bose-Fermi alternative in d >= 4 is assumed for AQFT superselection statistics in this abstraction layer. |
| `aqftDoplicherRobertsReconstruction` | `qft.aqft.doplicher_roberts_reconstruction` | 1 | 0 | 1 | Existence of Doplicher-Roberts reconstruction data is assumed in this abstraction layer. |
| `aqftGnsExistence` | `qft.aqft.gns_existence` | 1 | 0 | 1 | GNS representation existence for states on local AQFT algebras is assumed in this abstraction layer. |
| `aqftHaagTheorem` | `qft.aqft.haag_theorem` | 1 | 0 | 1 | AQFT Haag-theorem expectation-value equivalence conclusion is assumed in this abstraction layer. |
| `aqftReehSchlieder` | `qft.aqft.reeh_schlieder` | 1 | 0 | 1 | AQFT Reeh-Schlieder density conclusion is assumed in this abstraction layer. |
| `aqftSpinStatistics` | `qft.aqft.spin_statistics` | 1 | 0 | 1 | Spin-statistics implication statements are assumed in this abstraction layer. |
| `aqftTomitaTakesaki` | `qft.aqft.tomita_takesaki` | 1 | 0 | 1 | Existence of Tomita-Takesaki modular data is assumed in this abstraction layer. |
| `bianchiImpliesConservation` | `gr.bianchi_implies_conservation` | 1 | 0 | 1 | Contracted Bianchi identity implies covariant stress-energy conservation in this abstraction layer. |
| `brstExactImpliesClosed` | `qft.bv.brst.exact_implies_closed` | 1 | 0 | 1 | BRST exact implies BRST closed is assumed in this abstraction layer. |
| `brstGaugeFixedInvariant` | `qft.bv.brst.gauge_fixed_invariant` | 1 | 0 | 1 | BRST invariance of the gauge-fixed action is assumed in this abstraction layer. |
| `brstGaugeFixingDifferenceExact` | `qft.bv.brst.gauge_fixing_difference_exact` | 1 | 0 | 1 | BRST exactness of differences between gauge-fixed actions is assumed in this abstraction layer. |
| `bvDifferentialNZero` | `qft.bv.differential_n_zero` | 1 | 0 | 1 | Vanishing of higher BV differential iterates (n >= 2) is assumed in this abstraction layer. |
| `bvDifferentialNilpotent` | `qft.bv.differential_nilpotent` | 2 | 0 | 2 | Nilpotency of the BV differential under the classical master equation is assumed in this abstraction layer. |
| `bvGaugeIndependence` | `qft.bv.gauge_independence` | 1 | 0 | 1 | Gauge-fixing independence in BV via BV-exact variation is assumed in this abstraction layer. |
| `cftCrossRatiosPositiveFromPoints` | `qft.cft.cross_ratios_positive_from_points` | 1 | 0 | 1 | Computed CFT cross-ratios from the selected point configuration are in the positive region used by the bootstrap layer. |
| `cftTDualWeightSymmetry` | `qft.cft.2d.t_dual_weight_symmetry` | 1 | 0 | 1 | Free-boson momentum/winding conformal weights obey the T-duality swap symmetry used in this abstraction layer. |
| `conformalPreservesCausalStructure` | `spacetime.conformal_preserves_causal_structure` | 1 | 0 | 1 | Conformal rescaling preserves causal classification (timelike/spacelike/lightlike) in the current abstraction layer. |
| `conformalPreservesNull` | `spacetime.conformal_preserves_null` | 1 | 0 | 1 | Conformal rescaling preserves null separation in the current abstraction layer. |
| `flrwMetricWellFormed` | `gr.flrw_metric_well_formed` | 3 | 0 | 3 | FLRW metric data is treated as a valid Lorentzian metric package in this abstraction layer. |
| `ghsInequality` | `euclidean.ghs_inequality` | 1 | 0 | 1 | Ferromagnetic Euclidean theories satisfy the stated GHS-type correlation inequality. |
| `haagRuelleEqualsLsz` | `qft.smatrix.haag_ruelle_equals_lsz` | 1 | 0 | 1 | Haag-Ruelle and LSZ constructions give identical scattering amplitudes in the current abstraction layer. |
| `holevoBound` | `qi.holevo_bound` | 1 | 0 | 1 | Classical capacity of the identity channel is bounded by log(dim) in this abstract channel model. |
| `lorentzBoostPreservesMetric` | `spacetime.lorentz_boost_preserves_metric` | 1 | 0 | 1 | The explicit x-direction boost matrix preserves the Minkowski inner product. |
| `lorentzComposePreservesMetric` | `sym.lorentz.compose_preserves_metric` | 6 | 0 | 6 | Composition of Lorentz transformations preserves the Minkowski inner product. |
| `lorentzGroupInvMulCancel` | `sym.lorentz.group.inv_mul_cancel` | 1 | 0 | 1 | Lorentz inverse is a left inverse in the chosen abstraction. |
| `lorentzGroupMulAssoc` | `sym.lorentz.group.mul_assoc` | 1 | 0 | 1 | Lorentz multiplication is associative in the chosen abstraction. |
| `lorentzGroupMulOne` | `sym.lorentz.group.mul_one` | 1 | 0 | 1 | Lorentz identity is a right unit in the chosen abstraction. |
| `lorentzGroupOneMul` | `sym.lorentz.group.one_mul` | 1 | 0 | 1 | Lorentz identity is a left unit in the chosen abstraction. |
| `lorentzInversePreservesMetric` | `sym.lorentz.inverse_preserves_metric` | 6 | 0 | 6 | The explicit Lorentz inverse construction preserves the Minkowski inner product. |
| `lorentzPreservesLightlike` | `spacetime.lorentz_preserves_lightlike` | 2 | 0 | 2 | Lorentz transformations preserve lightlike separation in the Minkowski model. |
| `lorentzPreservesSpacelike` | `spacetime.lorentz_preserves_spacelike` | 2 | 0 | 2 | Lorentz transformations preserve spacelike separation in the Minkowski model. |
| `lorentzPreservesTimelike` | `spacetime.lorentz_preserves_timelike` | 2 | 0 | 2 | Lorentz transformations preserve timelike separation in the Minkowski model. |
| `lszKleinGordonOperatorExists` | `qft.smatrix.lsz.klein_gordon_operator_exists` | 1 | 0 | 1 | A suitable Klein-Gordon operator action is available in the abstract LSZ functional setting. |
| `lszReductionFormula` | `qft.smatrix.lsz.reduction_formula` | 1 | 0 | 1 | The LSZ reduction identity for amplitudes is assumed in the current abstraction layer. |
| `metricPerturbationWellFormed` | `gr.metric_perturbation_well_formed` | 1 | 0 | 1 | First-order perturbed metric data is treated as a valid Lorentzian metric package in this linearized model. |
| `osReconstruction` | `euclidean.os_reconstruction` | 1 | 0 | 1 | OS axioms provide analytic continuation to Wightman data in this abstract reconstruction interface. |
| `perfectFluidEnergyConditions` | `gr.perfect_fluid_energy_conditions` | 1 | 0 | 1 | Perfect-fluid stress tensor satisfies WEC and NEC under the declared equation-of-state bounds. |
| `poincareGroupInvMulCancel` | `sym.poincare.group.inv_mul_cancel` | 1 | 0 | 1 | Poincare inverse is a left inverse in the chosen abstraction. |
| `poincareGroupMulAssoc` | `sym.poincare.group.mul_assoc` | 1 | 0 | 1 | Poincare multiplication is associative in the chosen abstraction. |
| `poincareGroupMulOne` | `sym.poincare.group.mul_one` | 1 | 0 | 1 | Poincare identity is a right unit in the chosen abstraction. |
| `poincareGroupOneMul` | `sym.poincare.group.one_mul` | 1 | 0 | 1 | Poincare identity is a left unit in the chosen abstraction. |
| `qcdAsymptoticFreedom` | `rg.gellmannlow.qcd_asymptotic_freedom` | 1 | 0 | 1 | One-loop QCD coefficient has the asymptotic-freedom sign in the Nf < 17 regime under the chosen convention. |
| `qiArakiLieb` | `qi.araki_lieb` | 1 | 0 | 1 | Araki-Lieb entropy triangle inequality is assumed in this abstraction layer. |
| `qiDistillationLessThanFormation` | `qi.distillation_le_formation` | 1 | 0 | 1 | Distillable entanglement is bounded above by entanglement of formation in this abstraction layer. |
| `qiKleinInequality` | `qi.klein_inequality` | 1 | 0 | 1 | Klein inequality equality condition for relative entropy is assumed in this abstraction layer. |
| `qiLoccMonotone` | `qi.locc_monotone` | 1 | 0 | 1 | LOCC monotonicity of entanglement of formation is assumed in this abstraction layer. |
| `qiLoccPreservesSeparability` | `qi.locc_preserves_separability` | 1 | 0 | 1 | LOCC operations preserve separability in this abstraction layer. |
| `qiNoBroadcasting` | `qi.no_broadcasting` | 1 | 0 | 1 | No-broadcasting impossibility statement is assumed in this abstraction layer. |
| `qiNoCloning` | `qi.no_cloning` | 1 | 0 | 1 | No-cloning impossibility statement is assumed in this abstraction layer. |
| `qiNoDeleting` | `qi.no_deleting` | 1 | 0 | 1 | No-deleting impossibility statement is assumed in this abstraction layer. |
| `qiSeparableDiscordNonzero` | `qi.separable_discord_nonzero` | 1 | 0 | 1 | Existence of separable states with nonzero quantum discord is assumed in this abstraction layer. |
| `qiStrongSubadditivity` | `qi.strong_subadditivity` | 1 | 0 | 1 | Strong subadditivity inequality is assumed in this abstraction layer. |
| `quantumExpectationReal` | `quantum.expectation_real` | 1 | 0 | 1 | Reality of expectation values for Hermitian observables is assumed in this abstraction layer. |
| `quantumPauliDirectionObservable` | `quantum.pauli_direction_observable` | 3 | 3 | 6 | Linearity and Hermiticity proof obligations for Bloch-sphere directional Pauli observables are assumed in this abstraction layer. |
| `quantumPureToDensityAxioms` | `quantum.pure_to_density_axioms` | 5 | 1 | 6 | Self-adjointness/positivity/trace-one proof obligations for the pure-state density operator construction are assumed in this abstraction layer. |
| `quantumSingletPauliCorrelation` | `quantum.singlet_pauli_correlation` | 1 | 2 | 3 | Singlet-state Pauli correlation formula is assumed in this abstraction layer. |
| `quantumUnitaryPreservesNorm` | `quantum.unitary_preserves_norm` | 2 | 0 | 2 | Unitary norm preservation is assumed in this abstraction layer's quantum operator model. |
| `reissnerNordstromMetricWellFormed` | `gr.reissner_nordstrom_metric_well_formed` | 2 | 0 | 2 | Reissner-Nordstrom metric data is treated as a valid Lorentzian metric package in this abstraction layer. |
| `schwarzschildMetricWellFormed` | `gr.schwarzschild_metric_well_formed` | 5 | 0 | 5 | Schwarzschild metric data is treated as a valid Lorentzian metric package in this abstraction layer. |
| `spatialRotationPreservesMetric` | `spacetime.spatial_rotation_preserves_metric` | 1 | 0 | 1 | The explicit spatial z-rotation matrix preserves the Minkowski inner product. |
| `tqftIsingModularAxioms` | `qft.tqft.ising_modular_axioms` | 1 | 0 | 1 | Coherence and modularity proof obligations for the explicit Ising modular-category instance are assumed in this abstraction layer. |
| `tqftModularRelation` | `qft.tqft.modular_relation` | 1 | 0 | 1 | The modular relation connecting S and T matrices is assumed in this abstraction layer. |
| `tqftSu24FusionAxioms` | `qft.tqft.su24_fusion_axioms` | 3 | 0 | 3 | Coherence proof obligations for the explicit SU(2)_4 fusion-category instance are assumed in this abstraction layer. |
| `tqftSu24RibbonAxioms` | `qft.tqft.su24_ribbon_axioms` | 2 | 0 | 2 | Braiding/twist coherence proof obligations for the explicit SU(2)_4 ribbon-category instance are assumed in this abstraction layer. |
| `tqftZ3ModularAxioms` | `qft.tqft.z3_modular_axioms` | 6 | 2 | 8 | Coherence and modularity proof obligations for the explicit Z3 modular-category instance are assumed in this abstraction layer. |
| `wightmanHaagTheorem` | `qft.wightman.haag_theorem` | 1 | 0 | 1 | Haag's unitary inequivalence conclusion holds in the current abstraction layer. |
| `wightmanPctTheorem` | `qft.wightman.pct_theorem` | 1 | 0 | 1 | PCT symmetry relation for Wightman functions holds in the current abstraction layer. |
| `wightmanReehSchlieder` | `qft.wightman.reeh_schlieder` | 1 | 0 | 1 | Reeh-Schlieder cyclicity/separating conclusion is assumed at this abstraction layer. |
| `wightmanSpinStatistics` | `qft.wightman.spin_statistics` | 1 | 0 | 1 | Spin-statistics relation holds in the current abstraction layer. |
| `wightmanTemperedness` | `qft.wightman.temperedness` | 1 | 0 | 1 | Temperedness growth bound for Wightman distributions is assumed in the current abstraction layer. |
| `wilsonianIrrelevantSuppression` | `rg.wilsonian.irrelevant_suppression` | 1 | 0 | 1 | Irrelevant operators are power-law suppressed along Wilsonian RG flow in this abstraction layer. |
