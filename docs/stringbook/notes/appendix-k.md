# Appendix K: RG flows in 2D

- Status: initial extraction complete
- Source page start: 753
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/RG/TwoDimensionalFlows.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional/SigmaModels.lean`

## Reading Summary
- Develops polynomial Landau-Ginzburg deformations of free scalar CFT, including scheme dependence, exact operator EOM in normal-ordering scheme, and IR flow to Virasoro minimal models for tuned polynomial potentials.
- Extends to `${\cal N}=2` Landau-Ginzburg models with superpotential `W(X)=X^k`, highlighting Wilsonian non-renormalization of `W` and IR flow to `${\cal N}=2` minimal models with chiral-primary spectrum/weights fixed by `U(1)_R`.
- Reviews `(2,2)` abelian GLSMs: vector multiplet, FI-theta term, auxiliary-field elimination, scalar potential, `U(1)_A` anomaly, and one-loop twisted effective superpotential constraints.
- Analyzes CY/LG phase structure in GLSM (`r>0` CY sigma-model phase, `r<0` LG-orbifold phase, `r=0` Coulomb branch and `θ` lifting), with matching IR central-charge accounting.
- Derives abelian dual descriptions with twisted chiral multipliers, quantum-corrected twisted superpotentials, and relation to mirror duality between `${\cal N}=2` cigar coset and `${\cal N}=2` Liouville theory.

## Candidate Formalization Units
- `LandauGinzburgMinimalModelFlow`: polynomial-even-potential LG flow interface to minimal-model central charge.
- `N2LandauGinzburgIRPackage`: non-renormalized superpotential plus `${\cal N}=2` minimal-model central-charge relation.
- `AxialAnomalyThetaShift`: GLSM `U(1)_A` anomaly theta-angle shift relation.
- `GlsmTwistedSuperpotentialOneLoop`: one-loop twisted-superpotential coefficient constraints.
- `CalabiYauLandauGinzburgPhasePackage`: FI-sign phase map (`CY` vs `LG orbifold`) plus central-charge agreement.
- `AbelianDualityTwistedSuperpotentialMatch`: dual twisted-superpotential matching up to linear/constant redefinitions.
- `CigarLiouvilleMirrorDuality`: mirror-equivalence interface between cigar and Liouville SCFT descriptions.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dLandauGinzburgMinimalModelFlow`.
- Candidate new `AssumptionId`: `cft2dN2LandauGinzburgNonRenormalization`.
- Candidate new `AssumptionId`: `cft2dGlsmAxialAnomalyThetaShift`.
- Candidate new `AssumptionId`: `cft2dGlsmTwistedSuperpotentialOneLoop`.
- Candidate new `AssumptionId`: `cft2dCalabiYauLandauGinzburgPhaseFlow`.
- Candidate new `AssumptionId`: `cft2dAbelianDualityTwistedSuperpotentialMatch`.
- Candidate new `AssumptionId`: `cft2dCigarLiouvilleMirrorDuality`.

## Subsections
- [x] K.1 Landau-Ginzburg models (p.753)
- [x] K.2 Gauged linear sigma models (p.754)
- [x] K.3 The flows to Calabi-Yau and Landau-Ginzburg models (p.757)
- [x] K.4 Abelian duality of $(2,2)$ theories (p.759)
- [x] K.5 Mirror duality between ${\cal N}=2$ cigar and Liouville CFT (p.761)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
