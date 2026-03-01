# Section 10: Closed superstring field theory

- Status: initial extraction complete
- Source page start: 198
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/SuperstringFieldTheory.lean`

## Reading Summary
- Extracted NS/R closed-super-SFT field-space constraints:
  BRST-nilpotent states in `H_0` with `b_0^- = L_0^- = 0`, chiral GSO
  projection, and auxiliary Ramond `-3/2`-picture completion
  (`hzerosuper`, `auxhzero`).
- Extracted off-shell superstring amplitude-chain structure on
  `Q-hat_{h,n}` with NS/R-dependent PCO counting and vertical-segment
  correction data; included degeneration/plumbing compatibility and averaged
  Ramond PCO insertion prescriptions (`offshellampsuper`, `pcocontdegen`,
  `avgpco`, `superampfactoroff`).
- Extracted 1PI effective-action formalism with picture-adjusted Siegel
  propagator and equivalent Legendre-transform statement; included Ramond
  propagator degeneracy control via picture-adjusting operators
  (`pictureadjustop`, `seigproppo`, `onepisuper`, `offshellgammasuper`,
  `bzeronpic`, `bzeronpica`).
- Extracted BV quantum-super-SFT package (ghost/picture grading, canonical BV
  pairing, geometric master equation, quantum master equation, and
  interaction-vertex geometry) (`ghnumsup`, `bvpairingaux`, `bvsftfnlsuper`,
  `sssftvert`, `geommassuper`, `quantumbvsupersft`).
- Extracted RR kinetic-sector treatment with auxiliary completion and matching
  to supergravity kinetic data (including type-IIB self-dual-sector handling)
  (`kinsupact`, `ffpropa`, `sugrakint`).
- Extracted super-SFT field equation and bracket packages from 1PI data,
  including flat-frame vertical-correction constructions and pp-wave massless
  all-order solution logic (`supersfteom`, `superstringbrack`,
  `geommassuperflat`, `twostringbracksuper`, `threestringbracksuper`,
  `ppwavesf`, `ffppss`, `mmppss`).

## Candidate Formalization Units
- `SuperSftFieldSpacePackage`
- `SuperSftOffShellAmplitudePackage`
- `SuperSftPlumbingCompatibilityPackage`
- `SuperSftOnePiPackage`
- `SuperSftRamondDegeneracyControlPackage`
- `SuperSftBvQuantumPackage`
- `SuperSftRrKineticPackage`
- `SuperSftFieldEquationPackage`
- `SuperSftFlatBracketPackage`
- `SuperSftPpWaveSolutionPackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringSuperSftFieldSpaceNsrAuxiliary`.
- Mapped `AssumptionId`: `stringSuperSftOffShellAmplitudeChain`.
- Mapped `AssumptionId`: `stringSuperSftRamondPlumbingPcoCompatibility`.
- Mapped `AssumptionId`: `stringSuperSftOnePiPictureAdjustedPropagator`.
- Mapped `AssumptionId`: `stringSuperSftRamondTowerRegularization`.
- Mapped `AssumptionId`: `stringSuperSftBvQuantumMasterEquation`.
- Mapped `AssumptionId`: `stringSuperSftRrKineticTermMatching`.
- Mapped `AssumptionId`: `stringSuperSftFieldEquationBracketPackage`.
- Mapped `AssumptionId`: `stringSuperSftFlatBracketVerticalCorrection`.
- Mapped `AssumptionId`: `stringSuperSftPpWaveSolutionPackage`.

## Subsections
- [x] 10.1 The space of NS and R string fields and off-shell superstring amplitudes (p.198)
- [x] 10.2 The 1PI effective action of superstring field theory (p.201)
- [x] 10.3 BV formulation of quantum superstring field theory (p.202)
- [x] 10.4 The kinetic term of the RR fields (p.204)
- [x] 10.5 The superstring field equation (p.206)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
