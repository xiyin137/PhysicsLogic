# String Book Incorporation Roadmap

## Objective
- Translate the 850-page string book into incremental, auditable `PhysicsLogic` formal content.
- Keep extraction and formalization decoupled:
  - extraction/analysis artifacts live in `docs/stringbook/`
  - Lean formalization lands in `PhysicsLogic/StringTheory/` and existing modules as needed.
- Organize implementation by physics lanes (not by chapter order):
  - see `docs/stringbook/physics-organization.md`.

## Source Inputs
- `references/stringbook/string notes.tex`
- `references/stringbook/string notes.pdf`
- `references/stringbook/stringrefs.bib`
- Mathematica notebooks under:
  - `references/stringbook/Code repository/`
  - `references/stringbook/figures/`
- Appendix routing map:
  - `docs/stringbook/appendix-qft-crosswalk.md`

## Workflow Per Unit
1. Pick one unit from `reading-index.md` (one section or appendix).
2. Complete the corresponding note template in `docs/stringbook/notes/`.
3. Extract:
   - definition inventory
   - claim inventory (theorems/propositions/equations)
   - dependency chain to earlier units
   - candidate assumptions and whether each should become a new `AssumptionId`.
4. Implement Lean artifacts:
   - minimal declarations in `PhysicsLogic/StringTheory/` (or existing topical modules)
   - explicit assumptions via `PhysicsAssumption AssumptionId.*`
5. Run checks:
   - `./scripts/check_nonpapers_invariants.sh`
   - `./scripts/check_physics_assumptions_registry.sh`
   - `./scripts/check_physics_assumption_usage.sh`
   - `lake build PhysicsLogic.Core`
6. Record completion status + unresolved blockers in the unit note.

## Delivery Phases

### Phase 1: Foundations
- Sections 1-5
- Appendices B, D, E, F
- Goal: worldsheet basics, BRST/BV core vocabulary, perturbative amplitude backbone.
- QFT linkage focus:
  - B/C -> `QFT/PathIntegral`, `QFT/BV`
  - D/E/F -> `QFT/Wightman`, `QFT/CFT`

### Phase 2: Superstring Formalism
- Sections 6-10
- Appendices J, L, M, N
- Goal: superstring state spaces, GSO/BRST structure, supermoduli/PCO formal interfaces.
- QFT linkage focus:
  - J/K-style conformal algebra infrastructure -> `QFT/CFT/TwoDimensional`
  - L/M/N interfaces -> `Symmetries`, `QFT`, `GeneralRelativity`

### Phase 3: Branes and SFT
- Sections 11-16
- Appendices O, P
- Goal: D-brane/open-string/SFT structures and anomaly-aware assumptions.
- QFT linkage focus:
  - O -> anomaly handling in `QFT/PathIntegral`, `QFT/BV`
  - P -> boundary/operator data in `QFT/CFT`, `QFT/TQFT`

### Phase 4: Dualities and Geometry
- Sections 17-19
- Appendices H, I, K
- Goal: orientifolds, non-perturbative dualities, singularity transitions, geometric correspondences.
- QFT linkage focus:
  - H/I/K -> defects/orbifolds/RG into `QFT/CFT` and `QFT/RG`

### Phase 5: Holography and Integrability
- Sections 20-26
- Appendices Q, R, A, C, G
- Goal: AdS/CFT dictionary, integrable systems interfaces, matrix-model/holographic kinematics.
- QFT linkage focus:
  - Q/R/C/G -> `QFT/Euclidean`, `QFT/CFT`, and holographic kinematics interfaces

## Quality Gates
- No `axiom` declarations.
- No raw string-literal IDs for `PhysicsAssumption`.
- No non-Papers vacuous placeholders (`∃ ..., True`, `: True`, `→ True`).
- New assumptions must be:
  - added in `PhysicsLogic/Assumptions.lean`
  - added to `assumptionRegistry`
  - reflected in `ASSUMPTIONS.md`.
