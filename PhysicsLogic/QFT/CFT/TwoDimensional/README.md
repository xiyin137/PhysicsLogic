# 2D CFT Lane (`PhysicsLogic/QFT/CFT/TwoDimensional`)

This folder contains physics-first interface modules for two-dimensional CFT.
Declarations encode reusable structural packages via `PhysicsAssumption` labels.

## Modules
- `Virasoro.lean`: Virasoro algebra interfaces and basic highest-weight data.
- `OPE.lean`: operator-product expansion interfaces and consistency placeholders.
- `ConformalBlocks.lean`: BPZ/Virasoro-block interfaces and recursion package.
- `ModularInvariance.lean`: torus partition and modular-constraint interfaces.
- `Examples.lean`: reference examples (free boson, Ising, Liouville summaries).
- `DefectsOrbifolds.lean`: defect fusion, orbifold construction, and Narain data.
- `SigmaModels.lean`: NLSM Weyl-anomaly conditions, Buscher duality, and Liouville/coset interfaces.
- `ConformalManifolds.lean`: exactly-marginal conformal-manifold packages (including orbifold `C^2/Z_k` counting, Zamolodchikov metric normalization, `k=2` fixed-point distinction, and D1-D5/AdS3-CFT2 conformal-manifold and symmetric-orbifold loci).
- `Superconformal.lean`: `(1,1)`, `(2,2)`, `N=1,2,4` superconformal algebra interfaces.
- `BoundaryCFT.lean`: boundary-state, Cardy-channel, and free-field BCFT interfaces.

## Notes
- Section-19 orbifold-conformal-manifold content is shared with
  `PhysicsLogic/StringTheory/GeometricSingularities.lean` through
  `PhysicsLogic/StringTheory/SingularityCFTBridge.lean`.
- This lane avoids chapter-order mirroring; modules are grouped by reusable CFT
  physics structures.
