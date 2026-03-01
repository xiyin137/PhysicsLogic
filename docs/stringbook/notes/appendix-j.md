# Appendix J: Superconformal symmetry in two dimensions

- Status: initial extraction complete
- Source page start: 744
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/QFT/CFT/TwoDimensional/Superconformal.lean`, `PhysicsLogic/StringTheory/Worldsheet.lean`

## Reading Summary
- Introduces `(1,1)` superspace for worldsheet matter with real superfield `𝕏^μ`, superderivatives `D_θ,D_{\bar θ}`, and supercharges `Q_θ,Q_{\bar θ}`; component reduction reproduces the standard free action plus auxiliary-field terms.
- Derives holomorphic `${\cal N}=1` SCA from `T(z),G(z)` with OPE `G(z)G(0) ~ 2c/(3z^3) + 2T(0)/z` and mode relations `[L_n,G_r]`, `{G_r,G_s}`; distinguishes NS vs R mode moding and the Ramond zero-mode cylinder relation.
- Develops superconformal maps in `(z,θ)` superspace via covariance of `D_θ`, yielding finite/infinitesimal transformations and superprimary transformation laws.
- Presents `(2,2)` superspace chiral/antichiral constraints and reduction of the superspace sigma-model action to `(1,1)` form via coordinate/derivative redefinitions.
- Gives `${\cal N}=2` SCA OPE/mode algebra for `T,G^\pm,J`, then spectral-flow automorphisms (integer/half-integer flow, NS-R exchange), extended algebra generators, and chiral-primary descendants.
- Summarizes small `${\cal N}=4` SCA structure (`c=6k'`, `SU(2)_R` currents, supercurrents), unitarity constraints, and inner spectral-flow action.

## Candidate Formalization Units
- `Superspace11DerivativeAlgebra`: `(1,1)` superspace derivative/supercharge algebra interface.
- `N1SuperconformalAlgebraPackage`: `${\cal N}=1` SCA mode relations plus Ramond zero-mode cylinder relation.
- `Superspace22To11Reduction`: chiral `(2,2)` superspace constraint and `(1,1)` reduction map interface.
- `N2SuperconformalModeAlgebra`: `${\cal N}=2` mode relations for `L_n,G_r^\pm,J_n`.
- `N2SpectralFlowAutomorphism`: spectral-flow mode transformation interface.
- `SmallN4ModeAlgebra`: selected small `${\cal N}=4` mode and level-central-charge relations.
- `SmallN4SpectralFlow`: inner spectral-flow map interface for `${\cal N}=4`.

## Assumption Candidates
- Candidate new `AssumptionId`: `cft2dSuperspace11DerivativeAlgebra`.
- Candidate new `AssumptionId`: `cft2dN1SuperconformalAlgebra`.
- Candidate new `AssumptionId`: `cft2dSuperspace22ChiralReduction`.
- Candidate new `AssumptionId`: `cft2dN2SuperconformalAlgebra`.
- Candidate new `AssumptionId`: `cft2dN2SpectralFlowAutomorphism`.
- Candidate new `AssumptionId`: `cft2dN4SmallSuperconformalAlgebra`.
- Candidate new `AssumptionId`: `cft2dN4SpectralFlowInnerAutomorphism`.

## Subsections
- [x] J.1 $(1,1)$ superspace (p.744)
- [x] J.2 ${\cal N}=1$ superconformal algebra (p.745)
- [x] J.3 $(2,2)$ superspace (p.748)
- [x] J.4 ${\cal N}=2$ superconformal algebra (p.749)
- [x] J.5 ${\cal N}=4$ superconformal algebra (p.751)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
