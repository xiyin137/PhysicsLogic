# Section 09: Superstrings in general backgrounds

- Status: initial extraction complete
- Source page start: 184
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/SuperstringGeneralBackgrounds.lean`

## Reading Summary
- Extracted the general NSR-sector background setup with sector decomposition and
  ghost-picture assignment (`hilnsrdec`, `hnsrsuperdetail`), together with chiral
  GSO/modular-invariance assumptions.
- Extracted NSNS SCFT deformation by integrated `(1,1)` superprimary
  descendants (`defssuperns`) and the supersymmetric sigma-model form
  (`susynlsm`, `cpact`, `dzcurvdef`) including `H=dB` structure and quantum
  Weyl constraints leading to spacetime equations from
  `S_eff[G,B,Phi]` (`treeeff`).
- Extracted Calabi-Yau sigma-model structure:
  Kahler geometry (`kahlermet`, `kahlercond`), `(2,2)` superspace action
  (`twotwoact`, `twotwoaction`), R-symmetry/current decomposition
  (`rrsympsi`, `jjrsym`, `clcurr`), Ricci-flat condition and top-form
  constraints (`ricciflatkahler`, `logdetgh`, `hzz`), and flat-`B`/instanton
  phase effects (`deltasbfi`) with Kahler-class correction logic (`bkdelfk`).
- Extracted Green-Schwarz flat-background construction:
  supersymmetry transformations (`gsusy`), action decomposition
  (`gsactionone`, `gsaction`, `gsactiontwo`), `kappa`-symmetry and projector
  constraints (`kappasym`, `kappaproj`), and light-cone gauge reduction to free
  transverse fields (`lckappafx`, `slcsimp`, `sxthas`).
- Extracted superspace reformulation for general massless type-II backgrounds:
  superspace coordinates (`zmsupercod`), super-vielbein metric and super-`B`
  forms (`gscurv`, `emform`, `supbfiex`, `hdbsuper`, `eaform`), kappa-variation
  machinery (`kappazvar`, `delee`, `deleform`, `kapdeone`, `kapdetwo`,
  `delskagen`), and torsion/`H` constraint sets
  (`ommnsoon`, `torcons`, `hcons`) ensuring `kappa`-invariant GS action on
  on-shell type-II supergravity superspaces.

## Candidate Formalization Units
- `NsrSectorGsoPackage`
- `NsnsScftDeformationPackage`
- `SupersymmetricNsnsNlsmPackage`
- `NsnsTreeEffectiveActionPackage`
- `CalabiYauNlsmPackage`
- `CalabiYauRicciFlatPackage`
- `CalabiYauInstantonBFieldPackage`
- `GreenSchwarzFlatActionPackage`
- `GreenSchwarzLightConeGaugePackage`
- `GreenSchwarzSuperspaceConstraintPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringSuperBackgroundNsrHilbertGsoDecomposition`.
- Candidate new `AssumptionId`: `stringSuperBackgroundNsnsScftDeformation`.
- Candidate new `AssumptionId`: `stringSuperBackgroundNsnsNlsmSuperspaceAction`.
- Candidate new `AssumptionId`: `stringSuperBackgroundNsnsTreeEffectiveAction`.
- Candidate new `AssumptionId`: `stringSuperBackgroundCalabiYau22Structure`.
- Candidate new `AssumptionId`: `stringSuperBackgroundCalabiYauRicciFlatTopForm`.
- Candidate new `AssumptionId`: `stringSuperBackgroundCalabiYauInstantonBFieldPhase`.
- Candidate new `AssumptionId`: `stringSuperBackgroundGreenSchwarzKappaSymmetry`.
- Candidate new `AssumptionId`: `stringSuperBackgroundLightConeGaugeSpectrum`.
- Candidate new `AssumptionId`: `stringSuperBackgroundSuperspaceTorsionHConstraints`.

## Subsections
- [x] 9.1 General (NS,NS) backgrounds (p.184)
- [x] 9.2 Superstrings in Calabi-Yau spaces (p.186)
- [x] 9.3 Green-Schwarz formulation of the (effective) superstring (p.191)
- [x] 9.4 Superstring (effective) action in general massless backgrounds (p.194)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
