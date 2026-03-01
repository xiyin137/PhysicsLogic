# Section 12: D-branes

- Status: initial extraction complete
- Source page start: 241
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/DBranes.lean`

## Reading Summary
- Extracted bosonic D-brane boundary-condition setup from open-string endpoint
  constraints, including Neumann/Dirichlet splitting, stress-tensor/ghost
  boundary consistency, boundary BRST structure, and doubling-trick treatment
  of upper-half-plane correlators (`bcjcont`, `bcjcond`, `ttboundary`,
  `bcbdryc`, `imzxxdp`, `doublingtrick`, `bcbdrytst`, `dpbosbdrystcond`).
- Extracted bosonic boundary-state construction and normalization via
  oscillator/ghost gluing and cylinder open/closed-channel modular crossing
  (`dpbdryst`, `bccylcross`, `ndpbosc`).
- Extracted open bosonic-string spectrum on D-branes (Siegel/BRST constraints,
  mass-shell relation, level-0 tachyon, level-1 gauge/scalar multiplet), plus
  worldvolume marginal boundary deformations and D-brane translation by
  transverse scalar zero mode (`qbodef`, `opensiegel`, `openmasshell`,
  `opengaugcoll`, `delsbdry`, `delsbdryz`, `amuxcoup`, `exppsigdxx`).
- Extracted multiple-D-brane Chan-Paton structure and gauge enhancement:
  matrix-factorized open-string Hilbert space, stretched-string masses, and
  coincidence limit with nonabelian enhancement (`chanpatondefoneop`).
- Extracted type-II BPS D-brane sector: superconformal boundary conditions,
  fermion/spin-field gluing, preserved half-supersymmetry, open superstring NS/R
  spectra with GSO projection, and BPS boundary states with RR charge and
  anti-brane sign flip (`gbetagambdry`, `imzpsidp`, `jalbdrycond`, `susydbrane`,
  `doublingtrickii`, `dsugauge`, `dsucoll`, `dsugoldst`, `dpbryst`,
  `psibdrystcond`, `nsdryst`, `rrdryst`, `psibccond`, `dpavg`, `dpabr`,
  `ndnsnsrrres`, `jalbdryconddpbar`, `dsugoldstbar`).
- Extracted non-BPS constructions from brane-antibrane sectors with opposite
  GSO projection, pure-NSNS boundary states, vanishing RR charge, complete
  supersymmetry breaking, and open-string tachyon instability (`hbbproj`,
  `dsugaugenonbps`, `ddbartach`, `nonbpsbdryst`, `dpabrnonbps`).
- Extracted more general configurations: intersecting D-branes classified by
  ND direction count and mod-4 supersymmetry pattern, and D-branes-at-angles
  with explicit low-lying NS masses and equal-angle quarter-BPS/tachyon-free
  condition (`xlldoulbndmix`, `nsndbdry`, `mkdnd`, `rndbdry`, `epssuperq`,
  `zlldoulbndmix`, `zlmodexp`, `psizmodexp`, `twolowns`, `dangltach`,
  `openddtwos`, `epsdtdt`, `uvgeomsimp`, `deformttuv`).

## Candidate Formalization Units
- `BosonicDbraneBoundaryPackage`
- `BosonicDbraneBoundaryStatePackage`
- `OpenBosonicDbraneSpectrumPackage`
- `DbraneWorldvolumeDeformationPackage`
- `DbraneChanPatonPackage`
- `TypeIIBpsDbraneBoundaryPackage`
- `OpenSuperstringDbraneSpectrumPackage`
- `BpsDbraneBoundaryStateRrPackage`
- `NonBpsDbraneConstructionPackage`
- `IntersectingDbraneNdPackage`
- `DbranesAtAnglesPackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringDbraneBosonicBoundaryConditions`.
- Mapped `AssumptionId`: `stringDbraneBosonicBoundaryStateNormalization`.
- Mapped `AssumptionId`: `stringDbraneOpenBosonicSpectrum`.
- Mapped `AssumptionId`: `stringDbraneBoundaryMarginalDeformations`.
- Mapped `AssumptionId`: `stringDbraneChanPatonGaugeEnhancement`.
- Mapped `AssumptionId`: `stringDbraneTypeIIBpsBoundarySupersymmetry`.
- Mapped `AssumptionId`: `stringDbraneOpenSuperstringSpectrum`.
- Mapped `AssumptionId`: `stringDbraneBpsBoundaryStateRrCharge`.
- Mapped `AssumptionId`: `stringDbraneNonBpsConstruction`.
- Mapped `AssumptionId`: `stringDbraneIntersectingNdSpectrum`.
- Mapped `AssumptionId`: `stringDbraneAtAnglesStabilityBpsCondition`.

## Subsections
- [x] 12.1 D-branes in critical bosonic string theory (p.241)
- [x] 12.2 BPS D-branes in type II superstring theory (p.248)
- [x] 12.3 Non-BPS D-branes (p.253)
- [x] 12.4 More general configurations of D-branes (p.255)

## Subsubsections
- [x] 12.1.1 Open string states (p.244)
- [x] 12.1.2 Deformations of a D$p$-brane (p.245)
- [x] 12.1.3 Multiple D$p$-branes (p.247)
- [x] 12.2.1 Open superstring states (p.249)
- [x] 12.2.2 The boundary state (p.250)
- [x] 12.4.1 Intersecting D-branes (p.255)
- [x] 12.4.2 D-branes at angles (p.257)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
