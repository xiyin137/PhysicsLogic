# Section 07: Superstring perturbation theory: the general formalism

- Status: initial extraction complete
- Source page start: 137
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/SuperstringPerturbation.lean`

## Reading Summary
- Extracted the superconformal-gauge superstring amplitude setup with supermoduli
  integration and FP insertions (`gchiex`, `tnuinteg`, `delfpsuper`,
  `superampprescnl`, `gnuma`), including even/odd moduli counting relations.
- Extracted reformulation on super Riemann surfaces (SRS) with transition-map
  constraints (`scgau`, `ggepki`, `scatransfchar`, `splittrans`) and explicit
  worldsheet diffeomorphism/reparameterization invariance of the formalism.
- Extracted SCFT deformation package on SRS (`deltpre`, `deltsup`) and puncture
  treatment: NS puncture/PCO relations (`nspuncmoduli`, `vphipicraise`,
  `vzeropicrais`) and Ramond-sector coordinate constraints (`vgramon`,
  `simprpunctrans`, `ramooddtransmap`).
- Extracted supermoduli-space dimension and integration data
  (`doddcount`, `discgluingoddmod`, `berezianform`, `codimoneint`), including
  codimension-one boundary/gluing corrections.
- Extracted superstring unitarity/factorization near degenerations via
  super-plumbing fixtures (`supplumb`, `ramondplumb`, `ampnearxxbsuper`,
  `factofrakn`, `loopfrakn`).
- Extracted PCO formalism and BRST relations (`pcoregdef`, `superamppco`,
  `brstomgpco`), plus spurious-singularity control from determinant/theta
  structure (`thetabetadic`, `betamodzer`, `betazmdet`) and the full contour
  with vertical integration (`verttaut`, `vertamp`, `fullpcoconts`, `pcocompat`).

## Candidate Formalization Units
- `SupermoduliGaugeFixingPackage`
- `SuperRiemannSurfaceTransitionPackage`
- `SupermoduliOddDirectionsPackage`
- `SupermoduliBerezinianIntegrationPackage`
- `SuperstringPlumbingFactorizationPackage`
- `PictureChangingFormalismPackage`
- `SpuriousSingularityControlPackage`
- `VerticalIntegrationCompatibilityPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringSuperPerturbativeGaugeFixingSupermoduli`.
- Candidate new `AssumptionId`: `stringSuperPerturbativeSrsReparameterization`.
- Candidate new `AssumptionId`: `stringSuperPerturbativeOddModuliCounting`.
- Candidate new `AssumptionId`: `stringSuperPerturbativeBerezinianIntegration`.
- Candidate new `AssumptionId`: `stringSuperPerturbativePlumbingFactorization`.
- Candidate new `AssumptionId`: `stringSuperPerturbativePcoFormalism`.
- Candidate new `AssumptionId`: `stringSuperPerturbativeSpuriousSingularityControl`.
- Candidate new `AssumptionId`: `stringSuperPerturbativeVerticalIntegration`.

## Subsections
- [x] 7.1 Superconformal gauge with supermoduli (p.137)
- [x] 7.2 Reformulation in terms of super Riemann surfaces (p.139)
- [x] 7.3 Superconformal field theory on a SRS (p.142)
- [x] 7.4 The supermoduli space (p.147)
- [x] 7.5 Unitarity of superstring amplitudes (p.152)
- [x] 7.6 The picture changing operator formalism (p.154)
- [x] 7.7 PCO from supermoduli and spurious singularities (p.157)
- [x] 7.8 The full PCO contour with vertical integration (p.159)

## Subsubsections
- [x] 7.3.1 Even and odd spin structures (p.143)
- [x] 7.3.2 NS punctures (p.143)
- [x] 7.3.3 R punctures (p.146)
- [x] 7.4.1 Odd moduli (p.147)
- [x] 7.4.2 Integration (p.149)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
