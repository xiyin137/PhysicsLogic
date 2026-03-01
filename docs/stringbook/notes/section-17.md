# Section 17: Type I string theory and orientifolds

- Status: initial extraction complete
- Source page start: 352
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/TypeIOrientifolds.lean`

## Reading Summary
- Extracted unoriented-string setup: gauging orientation-reversing
  diffeomorphisms, worldsheet parity `Omega` action on matter/ghost fields,
  parity projection of the closed-string spectrum, `B`-field removal, and
  crosscap counting via `chi = 2-2h-b-c` with oriented-double-cover viewpoint
  (`omegacyl`, `omegacylplane`, `omegakkdd`, `chihbc`).
- Extracted bosonic crosscap-state construction from cylinder identification:
  crosscap gluing conditions, explicit oscillator-state solution, Klein-bottle
  modular crossing relation, normalization determination up to sign, and
  tadpole interpretation (`crosscapbdry`, `crosscapcond`, `crosscapexp`,
  `bccylcrosscap`, `notimes`).
- Extracted type-I projection from type-IIB: `Omega` action in NS/R and ghost
  sectors, `Omega^2` structure, (R,R) projection retaining `C_2`, open-string
  strip/UHP parity action, Chan-Paton matrix constraint, and `SO(n)`/`Sp(n)`
  gauge-algebra outcomes with type-I `SO(32)` selection target (`omegapsibc`,
  `omegaffp`, `omegapsibcz`, `rrgrdom`, `stripomegas`, `omenft`,
  `omegauhp`, `omegacpfac`, `socp`, `spcp`, `masslessomega`, `llttrans`).
- Extracted tadpole cancellation mechanism: super crosscap states in NSNS/RR,
  Klein-bottle and Mobius modular-crossing normalizations, and the unique
  cancellation of both NSNS and RR massless tadpoles for `SO(32)` D9-branes
  (`crosscapcondsup`, `nscrosscap`, `rrcrosscap`, `kleincrosssup`,
  `ccparsm`, `ncrosscapns`, `mobiuscross`, `hatrhopsi`, `intcpnvx`).
- Extracted perturbative type-I amplitudes: oriented+unoriented open+closed
  superstring amplitude prescription with spin-structure/PCO fibers and
  unitarity normalization, plus vacuum-topology decomposition
  (torus/Klein/cylinder/Mobius) and tadpole-controlled UV consistency
  (`openclosedtypeiamppco`, `normunoriented`, `torustypei`, `kleintypei`,
  `cylmobtypei`).
- Extracted type-I spacetime effective theory: gauge/gravity coupling
  dictionary, dilaton-weight structure by worldsheet topology, and RR
  Chern-Simons terms tied to Green-Schwarz anomaly cancellation (`typeiseff`,
  `kappagymtypei`, `csstypei`).
- Extracted type-I D-brane sectors: BPS D1/D5 consistency under `Omega`,
  Chan-Paton symmetry constraints, D1-D9 chiral fermion sector, D5-D9
  hypermultiplet content, plus non-BPS D0 construction where `Omega` projects
  out tachyon and leaves stable states with D0-D9 fermionic zero modes
  (`omegauhpacss`, `omegajj`, `omegadone`, `donetypeiramond`, `uuconda`,
  `sigmathetdnin`, `omegadfive`, `omegafivenine`, `sigmalama`, `sigmalamb`,
  `jalbdryconddpbartypei`, `tachhhdzz`, `masslessdzernsrr`,
  `csigmmatvert`).
- Extracted general orientifold-plane construction from `Omega * I` quotient
  in type II, including crosscap states for `O p` planes, normalization/sign
  options tied to `SO/Sp`, `O p^+ / O p^-` classification, and charge/tension
  dictionary with T-duality checks (`wtomom`, `califl`, `califliia`,
  `crosscapp`, `crosscapprr`, `orientcc`).

## Candidate Formalization Units
- `UnorientedWorldsheetParityPackage`
- `CrosscapStateBosonicPackage`
- `TypeIClosedOpenProjectionPackage`
- `TypeITadpoleCancellationPackage`
- `TypeIAmplitudeNormalizationPackage`
- `TypeIVacuumAmplitudePackage`
- `TypeIEffectiveActionPackage`
- `TypeIBpsD1D5Package`
- `TypeINonBpsD0Package`
- `OrientifoldPlanePackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringTypeIUnorientedWorldsheetParityProjection`.
- Mapped `AssumptionId`: `stringTypeICrosscapStateAndKleinBottleDuality`.
- Mapped `AssumptionId`: `stringTypeIClosedOpenOmegaProjectionSpectrum`.
- Mapped `AssumptionId`: `stringTypeITadpoleCancellationSO32`.
- Mapped `AssumptionId`: `stringTypeIAmplitudeNormalizationUnorientedOpenClosed`.
- Mapped `AssumptionId`: `stringTypeIVacuumAmplitudeTopologyAndCancellation`.
- Mapped `AssumptionId`: `stringTypeIEffectiveActionGaugeGravityCouplings`.
- Mapped `AssumptionId`: `stringTypeIBpsD1D5BraneSpectrum`.
- Mapped `AssumptionId`: `stringTypeINonBpsD0StabilityAndFermions`.
- Mapped `AssumptionId`: `stringOrientifoldPlaneCrosscapChargeDictionary`.

## Subsections
- [x] 17.1 Unoriented strings (p.352)
- [x] 17.2 The cross cap state (p.353)
- [x] 17.3 Type I string theory (p.354)
- [x] 17.4 Tadpole cancellation (p.358)
- [x] 17.5 Type I string amplitudes (p.361)
- [x] 17.6 D-branes in type I string theory (p.365)
- [x] 17.7 Orientifold planes (p.369)

## Subsubsections
- [x] 17.5.1 Vacuum amplitude (p.362)
- [x] 17.5.2 Spacetime effective theory (p.363)
- [x] 17.6.1 BPS D1 and D5-branes (p.365)
- [x] 17.6.2 The non-BPS D0-brane (p.367)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
