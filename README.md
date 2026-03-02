# PhysicsLogic

PhysicsLogic encodes the logical architecture of theoretical physics in Lean 4.

The goal is explicitness, not full mathematical rigor:
- make assumptions visible,
- make framework dependencies explicit,
- make theorem statements sound at the abstraction level of physics reasoning.

Proof-heavy formalization is intentionally delegated to other repositories.

Built on [Mathlib](https://github.com/leanprover-community/mathlib4).  
Lean toolchain: `leanprover/lean4:v4.29.0-rc1`.

## Mission And Scope

PhysicsLogic is for parsing physics logic:
- which hypotheses are required,
- what each framework actually claims,
- how frameworks relate or conflict.

PhysicsLogic is not:
- a replacement for rigorous analysis/topology/operator-algebra formalization,
- a numerical/simulation codebase.

## Core Design: Tracked Physical Assumptions

All non-derived physical premises are tracked through:
- `PhysicsLogic/Assumptions.lean`
- `PhysicsAssumption` (traceability wrapper)
- `AssumptionId.*` (stable string IDs)
- `assumptionRegistry` (master human-readable registry)
- `ASSUMPTIONS.md` (generated project-wide catalog)

Canonical theorem style:

```lean
(h_phys : PhysicsAssumption AssumptionId.someFact P) : P := by
  exact h_phys
```

Rules:
- never use Lean `axiom` declarations,
- never pass raw string literals as `PhysicsAssumption` IDs,
- always use `AssumptionId.*`,
- keep IDs stable after introduction.

## Physics-First Modeling Conventions

- organize declarations by physics semantics and dependency structure, not source-book chapter order,
- model actions as functionals on configuration spaces; for generic QFT/path-integral layers allow complex-valued actions unless an explicit Euclidean/classical-real restriction is intended,
- model operators/states/functionals with operator/state/functional interfaces (not scalar stand-ins),
- use semantic unit aliases from `PhysicsLogic/Units/Basic.lean` (`MassScale`, `LengthScale`, `ActionScale`, `DimensionlessCoupling`, etc.),
- natural-unit interfaces (`c = ħ = 1`) are supported via `naturalUnitSystem`; keep explicit-unit interfaces when needed,
- avoid hard-coded approximate decimal literals in non-Papers core modules.

## Repository Layout

Top-level library entry points:
- `PhysicsLogic/Core.lean`: strict non-Papers aggregator.
- `PhysicsLogic/Papers.lean`: all paper formalizations.
- `PhysicsLogic.lean`: compatibility umbrella (`Core` + `Papers.AMPS`).

Core physics modules:
- `PhysicsLogic/SpaceTime/`
- `PhysicsLogic/Symmetries/`
- `PhysicsLogic/ClassicalMechanics/`
- `PhysicsLogic/ClassicalFieldTheory/`
- `PhysicsLogic/FluidMechanics/`
- `PhysicsLogic/GeneralRelativity/`
- `PhysicsLogic/Quantum/`
- `PhysicsLogic/QuantumInformation/`
- `PhysicsLogic/QFT/`
- `PhysicsLogic/StringTheory/`

Paper-oriented modules:
- `PhysicsLogic/Papers/` (Bell, AMPS, Phi4_2D, Coleman2D, VafaWitten, cTheorem, Kolmogorov, GlimmJaffe, Charge4eTSC)

## Setup

1. Install Lean toolchain manager (`elan`).
2. Clone this repository.
3. Download Mathlib cache:

```bash
lake exe cache get
```

4. Build strict core target:

```bash
lake build PhysicsLogic.Core
```

## Build Targets

Strict non-Papers build:

```bash
lake build PhysicsLogic.Core
```

All papers:

```bash
lake build PhysicsLogic.Papers
```

Compatibility umbrella:

```bash
lake build PhysicsLogic
```

Specific module examples:

```bash
lake build PhysicsLogic.QFT.Wightman
lake build PhysicsLogic.Papers.AMPS
```

Important:
- do not run `lake build` with no target in this repo,
- do not run `lake clean` (can invalidate downloaded caches and slow recovery).

## Invariant And Governance Scripts

Scripts are under `scripts/`:
- `assumptions_report.sh`
- `check_global_semantic_types.sh`
- `check_no_ambiguous_dimensionless_names.sh`
- `check_no_approx_decimals_core.sh`
- `check_no_hardcoded_critical_dimension_defs.sh`
- `check_no_new_nonpapers_sorry.sh`
- `check_nonpapers_invariants.sh`
- `check_nonpapers_sorry_budget.sh`
- `check_physics_assumption_usage.sh`
- `check_physics_assumptions_registry.sh`
- `check_qft_semantic_types.sh`
- `check_string_semantic_types.sh`
- `check_stringbook_appendix_imports.sh`
- `check_stringbook_note_coverage.sh`
- `stringbook_sync_notes.sh`
- `update_assumptions_catalog.sh`

Recommended local pre-push run:

```bash
./scripts/check_nonpapers_invariants.sh
./scripts/check_physics_assumptions_registry.sh
./scripts/check_physics_assumption_usage.sh
./scripts/assumptions_report.sh /tmp/assumptions_report.md
./scripts/update_assumptions_catalog.sh
./scripts/check_no_new_nonpapers_sorry.sh
./scripts/check_nonpapers_sorry_budget.sh
lake build PhysicsLogic.Core
```

## CI Policy

GitHub Actions workflow: `.github/workflows/ci.yml`.

CI enforces:
- no explicit Lean `axiom` declarations,
- no non-Papers `True` placeholders in declaration signatures,
- no vacuous `∃ ..., True` non-Papers patterns,
- no exact bare `field : Prop` in non-Papers structures,
- stringbook appendix import coverage is complete and reachable,
- stringbook note candidate coverage (units + assumptions) is tracked,
- string-theory semantic typing guardrails pass,
- qft semantic typing guardrails pass,
- global semantic typing guardrails pass,
- no approximate decimal literals in non-Papers core modules,
- no hard-coded critical-dimension definitions in non-Papers core modules,
- no ambiguous dimensionless field names in non-Papers core modules,
- all `PhysicsAssumption` labels are defined,
- all defined labels are listed in `assumptionRegistry`,
- `AssumptionId` string payloads are unique,
- no duplicate `AssumptionId` entries in `assumptionRegistry`,
- no raw string literal IDs in non-Papers `PhysicsAssumption` uses,
- assumptions usage report is generated and uploaded as CI artifact (`assumptions-report`),
- committed `ASSUMPTIONS.md` catalog is kept in sync with source,
- no newly added non-Papers `sorry`,
- non-Papers `sorry` count does not regress (when PR baseline is available),
- `lake build PhysicsLogic.Core`,
- `lake build PhysicsLogic.Papers`,
- `lake build PhysicsLogic`.

## Contributor Guidelines

When adding new results:
- prefer structure fields and explicit hypotheses over hidden assumptions,
- use `PhysicsAssumption AssumptionId.*` when a claim is physically motivated but not derived here,
- keep signatures informative and non-vacuous.

When adding a new physical assumption:
1. Add a new stable ID in `AssumptionId` (`PhysicsLogic/Assumptions.lean`).
2. Add a concise description in `assumptionRegistry`.
3. Use that ID at theorem/definition call sites.
4. Run the assumption guard scripts.

When touching non-Papers code:
- do not introduce `axiom`,
- do not introduce raw string literal assumption IDs,
- do not introduce new `sorry`.

## Notes On Papers

`PhysicsLogic/Papers` is intentionally looser than `Core`:
- paper modules may use stronger temporary placeholders while arguments are being translated,
- `Core` remains the strict target for architecture-level soundness.
