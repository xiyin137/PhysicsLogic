# Section 13: D-brane dynamics in bosonic string theory

- Status: initial extraction complete
- Source page start: 261
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/DBraneDynamicsBosonic.lean`

## Reading Summary
- Extracted open+closed bosonic perturbation with boundaries: genus/boundary
  expansion over `M_{h,n;b,m}`, boundary-orientation sign conventions,
  strip-BPZ conjugation, open plumbing fixture degeneration, open-channel
  factorization poles, and unitarity normalization recursion (`openampbos`,
  `omegaopencl`, `bpzconjdefbdr`, `openplumbing`, `nnopenaf`, `nnopenafb`,
  `nnopenafbc`, `nhbnmbos`).
- Extracted disc normalization and open-string coupling dictionary from
  boundary matter+ghost correlators and boundary-state crossing:
  `K_{D^2}` normalization, open tachyon vertex normalization, and `g_s`-`g_o`
  relation (`discnorm`, `ndtwon`, `vtopens`, `gsgorel`).
- Extracted disc amplitudes: 3-tachyon reduced amplitude and cubic tachyon
  effective interaction, 4-tachyon Veneziano decomposition, Chan-Paton
  multi-brane amplitudes, and gauge-boson/tachyon 3-point commutator structure
  supporting nonabelian worldvolume couplings (`discbosg`, `opentchthr`,
  `tachyoncubicop`, `atttto`, `tachthrcp`, `attamp`).
- Extracted cylinder amplitude formalism: open/closed-channel expressions,
  vacuum amplitude extension, modular crossing with boundary states, two-brane
  interaction interpretation, and parallel D$p$-brane expansion with tachyon IR
  divergence and finite massless exchange term (`acylam`, `omecylfi`,
  `azetwegenn`, `cylvacboss`, `cylindbb`, `aonetwdd`, `cylampexp`).
- Extracted D$p$-brane effective action physics: worldvolume
  reparameterization invariance, embedding-field induced metric, Nambu-Goto
  static-gauge expansion, and tension matching with low-energy open-string
  amplitudes (`stpmink`, `inducedmetricbos`, `dpnmgoex`, `gotprels`).
- Extracted dilaton and T-duality dependence of the effective action:
  `e^{-Phi}` prefactor, dual-radius and dual-coupling map, and tension/energy
  consistency across D$p$ <-> D$(p-1)$ descriptions (`xptdual`, `gspgs`,
  `tpponeden`).
- Extracted gauge-field dependence and Born-Infeld structure: worldsheet
  `B`/boundary-`A` couplings, compensating gauge transformations,
  gauge-invariant `B+2 pi alpha' F`, T-duality derivation from D2->D1 setup,
  and DBI action form (`wsbdryact`, `bplusf`, `deltasax`, `sactdo`, `sactdt`,
  `dpdbibos`).
- Extracted graviton/dilaton exchange between parallel D$p$-branes from
  Einstein-frame linearized bulk+brane action, gauge fixing and propagators,
  and matching to the cylinder massless term to recover tension-coupling
  consistency (`branactlin`, `gfexgrdi`, `gravipropb`, `dilatpropb`,
  `tpkapbos`).
- Extracted `c=1` D-brane dynamics: ZZ boundary state from modular crossing,
  open tachyon mode and rolling-tachyon marginal deformation, ZZ mass and MQM
  fermion interpretation, FZZT boundary wavefunction/cylinder identities,
  stability range without relevant deformations, ZZ-FZZT stretched-string
  energy relation, and long-string double-scaling/MQM adjoint-sector duality
  (`zzcrosscyl`, `psizz`, `zzopentacver`, `szzactmas`, `deformarolltac`,
  `elamrolttare`, `fzztbdrydt`, `cylidzzfzrt`, `sctablerfz`).

## Candidate Formalization Units
- `OpenClosedBosonicPerturbationPackage`
- `DiscOpenTachyonAmplitudePackage`
- `DiscChanPatonGaugePackage`
- `CylinderBosonicDbraneAmplitudePackage`
- `DbraneNambuGotoTensionPackage`
- `DbraneDilatonTDualityPackage`
- `DbraneBornInfeldGaugePackage`
- `DbraneGravitonDilatonExchangePackage`
- `COneZzRollingTachyonPackage`
- `COneFzztLongStringPackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicOpenClosedPerturbation`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicDiscTachyonAmplitudes`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicDiscChanPatonGaugeStructure`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicCylinderOpenClosedDuality`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicNambuGotoTensionMatching`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicDilatonTDualityRelations`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicBornInfeldGaugeInvariance`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicGravitonDilatonExchange`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicCOneZzRollingTachyon`.
- Mapped `AssumptionId`: `stringDbraneDynamicsBosonicCOneFzztLongStrings`.

## Subsections
- [x] 13.1 Open+closed bosonic string perturbation theory (p.261)
- [x] 13.2 Disc amplitudes (p.264)
- [x] 13.3 Cylinder amplitudes (p.266)
- [x] 13.4 D-brane effective action (p.269)
- [x] 13.5 Graviton-dilaton exchange amplitude between D$p$-branes (p.273)
- [x] 13.6 D-branes in $c=1$ string theory (p.274)

## Subsubsections
- [x] 13.4.1 Dilaton dependence (p.270)
- [x] 13.4.2 Gauge field dependence (p.271)
- [x] 13.6.1 The ZZ-brane and rolling tachyon (p.275)
- [x] 13.6.2 The FZZT-brane and long strings (p.277)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
