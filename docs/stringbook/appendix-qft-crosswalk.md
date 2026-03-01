# Appendix-to-QFT Crosswalk

This maps string-book appendices to existing `PhysicsLogic/QFT` workstreams, so
appendix extraction directly informs non-Papers core development.

## Core QFT Foundations
- Appendix B (Path integral): `PhysicsLogic/QFT/PathIntegral/*`
- Appendix C (Gauge-theory path integral/BV): `PhysicsLogic/QFT/BV/*`, `PhysicsLogic/QFT/PathIntegral/*`
- Appendix D (Local QFT basics): `PhysicsLogic/QFT/Wightman/*`, `PhysicsLogic/QFT/AQFT/*`

## CFT and 2D Structures
- Appendix E (2D CFT properties): `PhysicsLogic/QFT/CFT/Basic.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional/*`
- Appendix F (Riemann surfaces/modular invariance): `PhysicsLogic/QFT/CFT/TwoDimensional/ModularInvariance.lean`, `PhysicsLogic/QFT/TQFT/*`
- Appendix G (2D free fields): `PhysicsLogic/QFT/CFT/TwoDimensional/Examples.lean`, `PhysicsLogic/QFT/Wightman/WightmanFunctions.lean`
- Appendix H (Symmetries/defects/orbifolds): `PhysicsLogic/QFT/CFT/TwoDimensional/*`, `PhysicsLogic/QFT/TQFT/*`
- Appendix I (Lagrangian 2D CFT description): `PhysicsLogic/QFT/CFT/*`, `PhysicsLogic/QFT/PathIntegral/*`
- Appendix J (2D superconformal symmetry): `PhysicsLogic/QFT/CFT/TwoDimensional/Superconformal.lean`, `PhysicsLogic/QFT/CFT/TwoDimensional/Virasoro.lean`
- Appendix K (2D RG flows): `PhysicsLogic/QFT/RG/TwoDimensionalFlows.lean`, `PhysicsLogic/QFT/RG/*`, `PhysicsLogic/QFT/CFT/Bootstrap/*`

## Supersymmetry, Gravity, and Anomalies
- Appendix L (Spinors): `PhysicsLogic/Symmetries/Spinors.lean`, `PhysicsLogic/Symmetries/*`, `PhysicsLogic/QFT/BV/*`
- Appendix M (Super-Poincare/superspace): `PhysicsLogic/Symmetries/SuperPoincare.lean`, `PhysicsLogic/Symmetries/Poincare.lean`, `PhysicsLogic/QFT/*` supersymmetric extensions
- Appendix N (Supergravity): `PhysicsLogic/GeneralRelativity/Supergravity.lean`, `PhysicsLogic/GeneralRelativity/*`, `PhysicsLogic/StringTheory/*` background equations
- Appendix O (Anomalies): `PhysicsLogic/QFT/PathIntegral/Anomalies.lean`, `PhysicsLogic/QFT/BV/*`, `PhysicsLogic/StringTheory/Anomalies.lean`

## Boundary and Holography
- Appendix P (Boundary CFT): `PhysicsLogic/QFT/CFT/TwoDimensional/BoundaryCFT.lean`, `PhysicsLogic/QFT/CFT/*`, `PhysicsLogic/QFT/TQFT/*`
- Appendix Q (Matrix quantum mechanics): `PhysicsLogic/QFT/Euclidean/MatrixQuantumMechanics.lean`, `PhysicsLogic/QFT/Euclidean/*`, `PhysicsLogic/StringTheory/*`
- Appendix R (Holographic correlators): `PhysicsLogic/StringTheory/Holography.lean`, `PhysicsLogic/QFT/CFT/*`, `PhysicsLogic/SpaceTime/*`

## Integration Rule
- For each appendix note in `docs/stringbook/notes/appendix-*.md`, add:
  - target module(s) from this crosswalk,
  - minimal declarations to add/update,
  - assumption candidates (new or reused).
