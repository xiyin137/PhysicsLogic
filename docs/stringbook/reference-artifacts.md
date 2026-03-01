# Reference Artifacts

This document tracks the non-versioned source artifacts in
`references/stringbook/` and their formalization touchpoints.

`references/` is intentionally gitignored in this repository, so documentation
for those artifacts is maintained here.

## Code Repository Notebooks

| Notebook | Book focus | Lean module touchpoints |
| --- | --- | --- |
| `Code repository/2D local susy variations.nb` | Super-Polyakov local SUSY variations | `PhysicsLogic/StringTheory/SuperstringQuantization.lean` |
| `Code repository/2D superspace.nb` | Appendix J superspace identities | `PhysicsLogic/QFT/CFT/TwoDimensional/Superconformal.lean` |
| `Code repository/4D superspace.nb` | Appendix M 4D superspace | `PhysicsLogic/Symmetries/SuperPoincare.lean`, `PhysicsLogic/GeneralRelativity/Supergravity.lean` |
| `Code repository/BES equation.nb` | Section 23 BES equation checks | `PhysicsLogic/StringTheory/AdS5Integrability.lean` |
| `Code repository/Conformal blocks and bootstrap demo.nb` | Appendix E conformal blocks/bootstrap | `PhysicsLogic/QFT/CFT/TwoDimensional/ConformalBlocks.lean` |
| `Code repository/G2 conical geometry.nb` | Section 19.6.2 `G_2` conical metrics/forms | `PhysicsLogic/StringTheory/GeometricSingularities.lean` |
| `Code repository/GS kappa symmetry.nb` | Section 9 and 14 kappa symmetry structure | `PhysicsLogic/StringTheory/SuperstringGeneralBackgrounds.lean`, `PhysicsLogic/StringTheory/DBraneDynamicsTypeII.lean` |
| `Code repository/Instanton and anomalies.nb` | D-instantons and anomaly checks | `PhysicsLogic/StringTheory/DInstantons.lean`, `PhysicsLogic/StringTheory/Anomalies.lean` |
| `Code repository/Liouville CFT.nb` | Liouville and DSLST links | `PhysicsLogic/StringTheory/GeometricSingularities.lean`, `PhysicsLogic/StringTheory/SingularityCFTBridge.lean` |
| `Code repository/Type II basic worldsheet calculations.nb` | Section 6 superstring quantization calculations | `PhysicsLogic/StringTheory/SuperstringQuantization.lean` |
| `Code repository/Type II torus 4-graviton amplitude check.nb` | One-loop Type II 4-graviton checks | `PhysicsLogic/StringTheory/SuperstringExplicitComputations.lean` |
| `Code repository/conifold geometry.nb` | Section 19.5 conifold geometry checks | `PhysicsLogic/StringTheory/GeometricSingularities.lean` |
| `Code repository/gamma matrices.nb` | Appendix L spinor/gamma identities | `PhysicsLogic/Symmetries/Spinors.lean` |
| `Code repository/mirror TBA and wrapping corrections.nb` | Section 24 mirror TBA and wrapping | `PhysicsLogic/StringTheory/AdS5MirrorTBAQSC.lean` |
| `Code repository/special geometry.nb` | Appendix N special Kahler geometry | `PhysicsLogic/GeneralRelativity/Supergravity.lean`, `PhysicsLogic/StringTheory/GeometricSingularities.lean` |
| `Code repository/spinfield cocycles.nb` | NS/R spin fields and cocycles | `PhysicsLogic/StringTheory/SuperstringQuantization.lean` |
| `Code repository/string coupling conventions.nb` | Appendix A convention checks | `PhysicsLogic/StringTheory/Conventions.lean` |
| `Code repository/su(2|2) spin chain.nb` | Section 23 integrable spin-chain structure | `PhysicsLogic/StringTheory/AdS5Integrability.lean` |

## Figure Assets

`references/stringbook/figures/` contains:
- source notebooks used for figure generation (for example `JS.nb`,
  `TDL figures.nb`, `generating figures.nb`),
- rendered `pdf`/`eps` assets consumed by `string notes.tex`.

Guidance:
- treat rendered files as generated artifacts from notebook sources,
- preserve existing filenames (TeX references are filename-based),
- when figure updates support formalization, record equation-label provenance in
  `docs/stringbook/notes/*.md`.

## Related Documents

- `docs/stringbook/reading-index.md`
- `docs/stringbook/inventory.md`
- `docs/stringbook/notes/`
