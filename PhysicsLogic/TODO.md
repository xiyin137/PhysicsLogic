# PhysicsLogic Module TODO — Architectural Review & Roadmap

(Formerly `Core/` — renamed to avoid confusion with rigorous formalization modules.)

## Vision

PhysicsLogic encodes the **logical architecture of theoretical physics** — making assumptions, structures, and inter-framework relationships explicit in Lean's type system. It is NOT about mathematical rigor (that belongs in RigorousQFT, StringGeometry, etc.) but about illuminating **what physics assumes and how different frameworks relate**. This module is for parsing physics papers, not for rigorous mathematical formalization.

Eliminating `axiom` and using `structure`/`def`/`variable` is essential because Lean axioms silently introduce assumptions invisible to the reader — the opposite of the project's goal.

---

## Update (2026-02-27)

Phase A and Phase B infrastructure work completed:

- **Build coverage fixed**: `PhysicsLogic.lean` now imports all core non-Papers aggregators (`SpaceTime`, `Symmetries`, `ClassicalMechanics`, `ClassicalFieldTheory`, `FluidMechanics`, `GeneralRelativity`, `Quantum`, `QuantumInformation`, `QuantumFieldTheory`) plus `Papers.AMPS`.
- **Hidden compile blockers fixed**: previously unvalidated modules now compile (`ClassicalFieldTheory/Scalar`, `ClassicalFieldTheory/Electromagnetic`, `ClassicalFieldTheory/Solitons`, `GeneralRelativity/Cosmology`, `GeneralRelativity/ReissnerNordstrom`).
- **QFT aggregation consistency fixed**: `QuantumFieldTheory.lean` now includes `QFT/Smatrix`; `QuantumInformation.lean` imports `Channels`.
- **Non-Papers `True` placeholders removed**: all structural `True` placeholders and vacuous `∃ ..., True` patterns removed from non-Papers modules.
- **Automated guards added**:
  - `scripts/check_nonpapers_invariants.sh`
  - `.github/workflows/ci.yml`
  - new `PhysicsLogic.Papers` aggregator target for full papers build

Current build status:
- `lake build PhysicsLogic` passes.
- `lake build PhysicsLogic.Papers` passes.

The sections below are retained as historical audit notes from earlier phases.

## Update (2026-02-28)

Phase C hardening started:

- Added strict non-Papers aggregator target: `PhysicsLogic.Core`.
- Kept `PhysicsLogic.lean` as compatibility umbrella (`PhysicsLogic.Core` + `Papers.AMPS`).
- CI now builds `PhysicsLogic.Core`, `PhysicsLogic.Papers`, and compatibility `PhysicsLogic`.
- `scripts/check_nonpapers_invariants.sh` no longer depends on a brittle line-based exclusion for `True`; it now checks structural signature patterns (`: True`, `→ True`) in non-Papers modules.
- Added diff-based no-regression guard: `scripts/check_no_new_nonpapers_sorry.sh` blocks newly introduced non-Papers `sorry`.
- Added non-Papers `sorry` budget guard: `scripts/check_nonpapers_sorry_budget.sh` blocks count regressions vs baseline.
- Added master assumptions file `PhysicsLogic/Assumptions.lean` with:
  - `PhysicsAssumption` wrapper (no extra proof power),
  - stable `AssumptionId.*` labels,
  - central `assumptionRegistry`.
- Added CI guard `scripts/check_physics_assumptions_registry.sh` ensuring assumption labels are defined and registered.
- Began rollout in core modules (`GeneralRelativity`, `QuantumInformation`, `QFT/Euclidean`, `QFT/RG`) by replacing implicit theorem placeholders with explicit labeled physical assumptions.

This separates core framework stability from papers churn while preserving backwards compatibility for existing import paths.

---

## Current Status

### Full codebase audit: COMPLETE

**Phase 1 — Axiom elimination (0 axioms across entire codebase)**

All ~273 axioms eliminated across ~40 files in the QFT/ directory. Every submodule builds cleanly.

| Submodule | Axioms Eliminated | Files | Status |
|-----------|------------------|-------|--------|
| PathIntegral/ | 65 | 8 | Done |
| Euclidean/ | 7 | 4 | Done |
| AQFT/ | 29 | 4 | Done |
| RG/ | 6 | 4 | Done |
| BV/ | 8 | 2 | Done |
| Smatrix/ | 35 | 4 | Done |
| TQFT/ | 17 | 5 | Done |
| CFT/Basic.lean | 18 | 1 | Done |
| CFT/Bootstrap/ | 46 | 3 | Done |
| CFT/TwoDimensional/ | 42 | 5 | Done |

Zero axioms across the entire PhysicsLogic directory, including all non-QFT modules.

**Phase 2 — Soundness audit (all files outside Papers/)**

Comprehensive audit of every definition, structure, axiom, and theorem statement for logical soundness. Categories of issues found and fixed:

#### Wightman & Euclidean QFT (most critical fixes)
- **W1 RelativisticCovariance**: removed spurious `∃ U` (unused existential made it trivially satisfiable)
- **W3 Locality**: added `domain : Set H` for unbounded field operators
- **W4 VacuumPropertiesAxiom**: fixed `∀ U` (all unitaries) → Poincaré representation `poincareUnitary`; added vacuum uniqueness; fixed `∀ phi` → `∃ phi` for cyclicity
- **ClusterDecomposition**: replaced `∃ combined` (trivially satisfiable) with actual (n+m)-point function
- **Haag's theorem**: was literally `¬∃ U, True = False`; restructured to proper no-go theorem
- **Spin-statistics**: was vacuous (no QFT parameter); now references WightmanQFT structure
- **PCT theorem**: added complex conjugation and point reversal
- **OS reflection positivity**: generalized from 2-point to arbitrary n-point configurations
- **AnalyticWightmanFunction**: replaced bare `Prop` with forward tube definition and boundary values
- **SchwingerFunctions.QFT**: removed vacuous `euclidean_invariant : Prop` and `reflection_positive : Prop`

#### RG, BV, Path Integral
- **PolchinskiFlow**: `satisfies_equation : Prop` → `cutoff_consistent : ∀ t, (actions t).cutoff.Λ = t`
- **WetterichFlow**: `satisfies_equation : Prop` → `regulator_ir_vanish : ∀ (p : ℝ), regulator 0 p = 0`
- **LPA/LPAprime**: removed bare `flow_equation : Prop`
- **CallanSymanzikData/CSOperatorMixing**: removed bare `Prop` fields (CS equation requires functional form)
- **RegularizedMeasure**: removed bare `measure_exists : Prop`
- **BV GaugeFixingFermion**: `field_dependent : True` → actual dependence condition on fields
- **BRSTFromBV**: removed bare `linear_in_antifields : Prop` and `field_independent_structure : Prop`
- **Instanton**: removed bare `is_critical : Prop` (requires functional derivatives to state)
- **EffectiveAction**: removed `onePIFromPathIntegral` (had computational `sorry` in `eval`)

#### Kontsevich-Segal, Quantum Information, Symmetries
- **KS_StateSpace**: `complete : Prop` → actual Cauchy completeness in seminorm topology; removed `locally_convex : Prop` (automatic); removed 3 `True` fields (`tensor_assoc`, `dual_dual`, `symmetric`)
- **Entanglement**: renamed misleading `product_separable`; removed `bound_entanglement_exists` (false for 2×2 systems per Horodecki 1996); dissolved `QubitEntanglementTheory` into standalone theorem
- **Lorentz**: fixed computational `sorry` in `lorentzInverse.matrix` with actual formula `η Λᵀ η`

#### Files verified sound (no changes needed)
SpaceTime/, QFT/AQFT/, QFT/CFT/, QFT/TQFT/, QFT/Smatrix/, GeneralRelativity/, ClassicalFieldTheory/, ClassicalMechanics/, FluidMechanics/, Quantum/, Symmetries/ (except Lorentz inverse fix)

**Build status**: `lake build PhysicsLogic` — 2418 jobs, all pass (only `sorry` warnings for deferred proofs).

---

## Remaining Issues

### Issue 1: Remaining `True` placeholders
Some `True` placeholders remain where the full statement requires infrastructure not yet available (e.g., nested Virasoro bracket computations in `VirasoroAlgebra.jacobi`). These are documented with comments.

### Issue 2: Intentional `Unit` data fields
`VirasoroGeneratorElement` and `AntiVirasoroGeneratorElement` intentionally keep `data : Unit` since they are formal generators of an abstract Lie algebra — the index `n : ℤ` is the meaningful data.

### Issue 3: Review sorry count
The `t_dual` definition in `CFT/TwoDimensional/Examples.lean` has a sorry for the weight proof (T-duality swaps momentum/winding). This is acceptable for PhysicsLogic but could be proved with some algebraic manipulation.

### Issue 4: Bare `Prop` fields with comments
Several bare `Prop` fields were removed and replaced with comments explaining why the mathematical content cannot yet be stated (e.g., PDEs requiring functional derivatives, CS equations requiring anomalous dimensions as functions of coupling). These could be revisited if the relevant mathematical infrastructure is developed.

---

## Design Principles

**Every module should follow the Wightman pattern:**

| Aspect | Wightman (Good) | Old AQFT (Bad, now fixed) |
|--------|----------------|--------------------------|
| Lean axioms | 0 | 29+ → 0 |
| Physical assumptions | Structure fields | Hidden in global axioms |
| Spacelike separation | Minkowski computation | `True` placeholder |
| Poincaré group | Imports from Symmetries | `Unit` type |
| Reader sees assumptions? | Yes | No |

**Soundness checklist for new definitions:**
- No `True` placeholders in structure fields (use meaningful conditions or omit with comment)
- No bare `Prop` fields carrying zero information
- No trivially satisfiable `∃ x, ...` patterns (existential must be constrained)
- No `sorry` in computational definitions (proof fields with `sorry` are acceptable)
- No `axiom` declarations
- No smuggled assumptions in bundled structures
