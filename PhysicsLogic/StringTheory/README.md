# StringTheory Module

This folder contains non-Papers core interfaces extracted from the string-book
program, organized by physics lanes rather than chapter order. The intent is
architectural clarity, not full mathematical rigor.

## Files
- `QuantumGravityInterface.lean`: quantum-gravity motivation layer and large-N string viewpoint.
- `Worldsheet.lean`: worldsheet and effective-string interfaces.
- `Quantization.lean`: BRST/Siegel/cohomology and mass-spectrum interfaces for bosonic and type-II superstrings.
- `SuperstringQuantization.lean`: Section-06 superstring quantization interfaces for super-Polyakov gauge symmetry, superconformal ghosts/picture number, type-II GSO projection, BRST structure, physical-state cohomology, massless spectrum, and spacetime supersymmetry algebra.
- `Backgrounds.lean`: sigma-model background fields, Weyl-beta constraints, and spacetime-EOM interface.
- `SuperstringGeneralBackgrounds.lean`: Section-09 interfaces for general NSNS backgrounds, Calabi-Yau `(2,2)` sigma-model structure, Green-Schwarz `kappa`-symmetric formulations, and type-II superspace torsion/`H` constraints.
- `PerturbativeScattering.lean`: perturbative worldsheet/moduli, ghost anomaly, plumbing-fixture factorization, and tree/loop scattering interface packages.
- `SuperstringPerturbation.lean`: Section-07 interfaces for supermoduli gauge-fixing, SRS reparameterization invariance, odd-moduli/Berezinian integration, superstring plumbing-unitarity, and PCO/spurious-singularity/vertical-integration packages.
- `SuperstringExplicitComputations.lean`: Section-08 interfaces for explicit tree/loop superstring amplitudes (NSNS and RR), spin-structure/PCO prescriptions, higher-genus ghost correlator formulas, and higher-loop vacuum/coupling-function constraints.
- `ClosedStringFieldTheory.lean`: off-shell closed-string field space, Siegel-gauge 1PI structure, classical bracket EOM, and background-independence interfaces.
- `SuperstringFieldTheory.lean`: Section-10 interfaces for closed super-SFT NS/R field space, off-shell/1PI/BV structures, Ramond-picture control, RR kinetic matching, and super-SFT field-equation/pp-wave solution packages.
- `HeteroticStringTheory.lean`: Section-11 interfaces for heterotic worldsheet/GSO/spectrum structure, perturbative/effective couplings, non-BPS mass renormalization, background `(0,1)` sigma-model anomalies, Calabi-Yau gauge-bundle/Strominger conditions, and quantum-corrected FI/vacuum packages.
- `DBranes.lean`: Section-12 interfaces for bosonic/type-II/non-BPS D-brane boundary conditions and boundary states, open-string spectra, Chan-Paton gauge enhancement, intersecting ND sectors, and D-branes-at-angles stability/BPS conditions.
- `DBraneDynamicsBosonic.lean`: Section-13 interfaces for open+closed perturbation with boundaries, disc and cylinder amplitude structure, D-brane DBI effective dynamics, graviton/dilaton exchange matching, and `c=1` ZZ/FZZT long-string sectors.
- `DBraneDynamicsTypeII.lean`: Section-14 interfaces for open+closed type-II perturbation, disc/cylinder D-brane amplitudes, kappa-symmetric BPS effective actions, RR charge quantization, wrapped-brane supersymmetry, non-Abelian stacked-brane theory, and D0/BFSS dynamics.
- `OpenStringFieldTheory.lean`: Section-15 interfaces for classical/quantum open string field theory, cubic star-algebra dynamics, tachyon condensation and `KBc`/analytic solutions, marginal and rolling-tachyon deformations, Erler-Maccaferri background-independence constructions, and open+closed (super)SFT BV packages.
- `DInstantons.lean`: Section-16 interfaces for D-instanton transseries/moduli integration, `c=1` ZZ and type-IIB D(-1) sectors, open+closed-SFT zero-mode gauge treatment, normalization extraction, and multiple-instanton IKKT scaling packages.
- `Conventions.lean`: Appendix-A convention interfaces for string/gravity couplings, D-brane tensions, and M-theory scale dictionaries.
- `Anomalies.lean`: type-IIB and type-I/heterotic anomaly-polynomial and Green-Schwarz-cancellation interfaces.
- `Holography.lean`: AdS/CFT scalar, current, stress-tensor, Witten-diagram, and Mellin-amplitude interfaces.
- `AdSCFT.lean`: Section-20 AdS/CFT interfaces for decoupling limits, parameter map, Coulomb branch, operator/state map, spectra, giant gravitons, and thermodynamics.
- `MTheoryHolography.lean`: Section-21 interfaces for M2/M5 near-horizon duals, 3D `N=8` SYM/ABJM structure, and 6D `(0,2)` SCFT compactification packages.
- `AdS3CFT2.lean`: Section-22 interfaces for D1-D5/AdS3-CFT2 moduli and decoupling, AdS3 WZW/spectral-flow spectra, and mixed `(NS,NS)`/`(R,R)` flux deformation packages.
- `AdS5Integrability.lean`: Section-23 interfaces for planar `N=4` spin-chain integrability, BMN/pp-wave mapping, centrally extended magnon kinematics, S-matrix crossing/dressing constraints, BES cusp relations, and Bethe-Yang/bound-state packages.
- `AdS5MirrorTBAQSC.lean`: Section-24 interfaces for mirror double-Wick kinematics, finite-volume mirror TBA/Y-system, wrapping corrections (including Konishi), and the `Pmu` quantum spectral curve with weak-coupling and small-spin limits.
- `WilsonLinesConfinement.lean`: Section-25 interfaces for Maldacena-Wilson lines, cusp/bremsstrahlung observables, Witten and Sakai-Sugimoto holographic QCD packages, and Klebanov-Witten/Tseytlin/Strassler conifold-cascade confinement data.
- `MatrixTheory.lean`: Section-26 interfaces for BFSS D0/M-wave uplift and thermodynamics, BFSS large-`N` S-matrix convergence package, matrix-string symmetric-orbifold and DVV deformation data, and large-`N` matrix-string amplitude matching.
- `Core.lean`: lane-level aggregator.

Source modules currently backing those lanes:
- `Prologue.lean`
- `EffectiveString.lean`
- `BosonicQuantization.lean`
- `SuperstringQuantization.lean`
- `Backgrounds.lean`
- `SuperstringGeneralBackgrounds.lean`
- `PerturbativeScattering.lean`
- `SuperstringPerturbation.lean`
- `SuperstringExplicitComputations.lean`
- `ClosedStringFieldTheory.lean`
- `SuperstringFieldTheory.lean`
- `HeteroticStringTheory.lean`
- `DBranes.lean`
- `DBraneDynamicsBosonic.lean`
- `DBraneDynamicsTypeII.lean`
- `OpenStringFieldTheory.lean`
- `DInstantons.lean`
- `Conventions.lean`
- `Anomalies.lean`
- `Holography.lean`
- `AdSCFT.lean`
- `MTheoryHolography.lean`
- `AdS3CFT2.lean`
- `AdS5Integrability.lean`
- `AdS5MirrorTBAQSC.lean`
- `WilsonLinesConfinement.lean`
- `MatrixTheory.lean`

## Conventions
- Physical claims are carried via `PhysicsAssumption AssumptionId.*` wrappers.
- Avoid hidden assumptions and raw-string assumption labels.
- Keep declarations composable so they can later be linked to deeper QFT/GR/CFT modules.
- Encode worldsheet diffeomorphism/reparameterization invariance explicitly in
  data structures rather than treating worldsheet points as fixed coordinates.
- Treat string/QFT actions as configuration-space functionals; use complex-valued
  codomains for general quantum/path-integral interfaces.
