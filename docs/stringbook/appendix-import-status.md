# String Book Appendix Import Status

This file tracks whether each appendix (`A` through `R`) is mapped to concrete
`PhysicsLogic` modules and whether those modules are re-exported through the
core aggregators (`PhysicsLogic.Core` -> `QuantumFieldTheory` / `StringTheory` / etc.).

Last audited: 2026-03-01 (local workspace audit).

| Appendix | Primary PhysicsLogic Targets | Aggregator Path |
|---|---|---|
| A | `PhysicsLogic/StringTheory/Conventions.lean` | `PhysicsLogic/StringTheory/Core.lean` -> `PhysicsLogic/StringTheory.lean` -> `PhysicsLogic/Core.lean` |
| B | `PhysicsLogic/QFT/PathIntegral/*`, `PhysicsLogic/QFT/BV/*` | `PhysicsLogic/QFT/PathIntegral.lean`, `PhysicsLogic/QFT/BV.lean` -> `PhysicsLogic/QuantumFieldTheory.lean` |
| C | `PhysicsLogic/QFT/BV/*`, `PhysicsLogic/QFT/PathIntegral/*` | `PhysicsLogic/QFT/BV.lean`, `PhysicsLogic/QFT/PathIntegral.lean` -> `PhysicsLogic/QuantumFieldTheory.lean` |
| D | `PhysicsLogic/QFT/Wightman/*`, `PhysicsLogic/QFT/Euclidean/WickRotation.lean`, `PhysicsLogic/QFT/CFT/*` | `PhysicsLogic/QFT/Wightman.lean`, `PhysicsLogic/QFT/Euclidean.lean`, `PhysicsLogic/QFT/CFT.lean` -> `PhysicsLogic/QuantumFieldTheory.lean` |
| E | `PhysicsLogic/QFT/CFT/TwoDimensional/*` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean` -> `PhysicsLogic/QFT/CFT.lean` |
| F | `PhysicsLogic/QFT/CFT/TwoDimensional/ModularInvariance.lean`, `PhysicsLogic/QFT/TQFT/*` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean`, `PhysicsLogic/QFT/TQFT.lean` |
| G | `PhysicsLogic/QFT/CFT/TwoDimensional/Examples.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional/Virasoro.lean` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean` |
| H | `PhysicsLogic/QFT/CFT/TwoDimensional/DefectsOrbifolds.lean`, `PhysicsLogic/QFT/TQFT/*` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean`, `PhysicsLogic/QFT/TQFT.lean` |
| I | `PhysicsLogic/QFT/CFT/TwoDimensional/SigmaModels.lean`, `PhysicsLogic/StringTheory/Backgrounds.lean` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean`, `PhysicsLogic/StringTheory/Core.lean` |
| J | `PhysicsLogic/QFT/CFT/TwoDimensional/Superconformal.lean`, `PhysicsLogic/StringTheory/Worldsheet.lean` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean`, `PhysicsLogic/StringTheory/Core.lean` |
| K | `PhysicsLogic/QFT/RG/TwoDimensionalFlows.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional/SigmaModels.lean` | `PhysicsLogic/QFT/RG.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional.lean` |
| L | `PhysicsLogic/Symmetries/Spinors.lean` | `PhysicsLogic/Symmetries.lean` -> `PhysicsLogic/Core.lean` |
| M | `PhysicsLogic/Symmetries/SuperPoincare.lean`, `PhysicsLogic/Symmetries/Poincare.lean` | `PhysicsLogic/Symmetries.lean` -> `PhysicsLogic/Core.lean` |
| N | `PhysicsLogic/GeneralRelativity/Supergravity.lean`, `PhysicsLogic/StringTheory/Backgrounds.lean` | `PhysicsLogic/GeneralRelativity.lean`, `PhysicsLogic/StringTheory/Core.lean` |
| O | `PhysicsLogic/QFT/PathIntegral/Anomalies.lean`, `PhysicsLogic/StringTheory/Anomalies.lean` | `PhysicsLogic/QFT/PathIntegral.lean`, `PhysicsLogic/StringTheory/Core.lean` |
| P | `PhysicsLogic/QFT/CFT/TwoDimensional/BoundaryCFT.lean` | `PhysicsLogic/QFT/CFT/TwoDimensional.lean` |
| Q | `PhysicsLogic/QFT/Euclidean/MatrixQuantumMechanics.lean` | `PhysicsLogic/QFT/Euclidean.lean` |
| R | `PhysicsLogic/StringTheory/Holography.lean` | `PhysicsLogic/StringTheory/Core.lean` |

## Audit Rule
- Any appendix import is considered complete only if:
  1. the target module path(s) exist in the repository,
  2. each target is reachable through an aggregator imported by `PhysicsLogic/Core.lean`,
  3. `docs/stringbook/notes/appendix-*.md` target lines match the active mapping.
