# Physics-First Organization

Book chapter order is useful for extraction, but formalization should be
organized by physics content and dependency structure.

## Development Lanes

1. Worldsheet Kinematics and CFT
- embeddings, worldsheet symmetries, gauge fixing, Virasoro/CFT structures
- target modules: `PhysicsLogic/StringTheory/Worldsheet.lean`, `PhysicsLogic/QFT/CFT/*`

2. Quantization and BRST/BV
- BRST complexes, Siegel constraints, cohomology, gauge-fixing consistency
- target modules: `PhysicsLogic/StringTheory/Quantization.lean`, `PhysicsLogic/QFT/BV/*`

3. Background Fields and Effective Actions
- sigma-model couplings `(G, B, Φ)`, beta-function constraints, spacetime EFT interfaces
- target modules: `PhysicsLogic/StringTheory/Backgrounds.lean`, `PhysicsLogic/QFT/PathIntegral/*`, `PhysicsLogic/QFT/RG/*`

4. Strings, Branes, and SFT
- open/closed sectors, D-brane constraints, string-field-theory structures
- target modules: `PhysicsLogic/StringTheory/*`, `PhysicsLogic/QFT/TQFT/*`

5. Dualities, Holography, Integrability
- AdS/CFT dictionaries, matrix-model interfaces, integrability constraints
- target modules: `PhysicsLogic/StringTheory/*`, `PhysicsLogic/QFT/CFT/*`, `PhysicsLogic/SpaceTime/*`

## Operational Rule
- Use chapter notes as source provenance only.
- Place new Lean declarations in the lane that best matches physics semantics.
- Link appendices through `appendix-qft-crosswalk.md` whenever they feed QFT modules.
- For path-integral/QFT actions, prefer complex-valued functionals unless a
  Euclidean/classical-real restriction is explicitly intended.
