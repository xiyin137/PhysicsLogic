# PhysicsLogic

Encoding the logical architecture of theoretical physics in Lean 4 — making assumptions, structures, and inter-framework relationships explicit in the type system.

This project is not about mathematical rigor (proving theorems from first principles) but about **parsing the logical structure of physics**: what each framework assumes, what follows from what, and where different frameworks are mutually inconsistent.

Built on [Mathlib](https://github.com/leanprover-community/mathlib4). Lean 4 toolchain: `v4.29.0-rc1`.

## Structure

### Foundations

| Module | Contents |
|--------|----------|
| **SpaceTime/** | Manifolds, metrics, Minkowski space, causality, curvature, geodesics, conformal structure |
| **Symmetries/** | Lorentz group, Poincaré group, Lie algebras, representations, discrete symmetries |

### Classical Physics

| Module | Contents |
|--------|----------|
| **ClassicalMechanics/** | Lagrangian/Hamiltonian mechanics, phase space, canonical transforms, Hamilton-Jacobi, integrability, perturbation theory |
| **ClassicalFieldTheory/** | Scalar/electromagnetic/Yang-Mills fields, Euler-Lagrange equations, Noether's theorem, energy-momentum, solitons |
| **FluidMechanics/** | Euler and Navier-Stokes equations, vorticity, compressible flow, conservation laws |
| **GeneralRelativity/** | Einstein equations, energy conditions, Schwarzschild/Kerr/Reissner-Nordström black holes, cosmology, gravitational waves, singularities |

### Quantum Physics

| Module | Contents |
|--------|----------|
| **Quantum/** | Hilbert spaces, operators, composite systems, measurement |
| **QuantumInformation/** | Entanglement, entropy, channels, partial trace, correlations, information theorems |

### Quantum Field Theory

| Module | Contents |
|--------|----------|
| **QFT/Wightman/** | Wightman axioms, field operators, Wightman functions, PCT and spin-statistics theorems |
| **QFT/Euclidean/** | Osterwalder-Schrader axioms, Schwinger functions, Wick rotation |
| **QFT/AQFT/** | Algebraic QFT (Haag-Kastler axioms), nets of algebras, Haag's theorem |
| **QFT/PathIntegral/** | Functional integrals, regularization, Faddeev-Popov, instantons |
| **QFT/CFT/** | Conformal field theory, bootstrap, 2D CFT (Virasoro algebra, modular invariance, minimal models) |
| **QFT/RG/** | Renormalization group, Polchinski/Wetterich flows, local potential approximation |
| **QFT/BV/** | Batalin-Vilkovisky formalism, BRST cohomology |
| **QFT/Smatrix/** | S-matrix, LSZ reduction, crossing symmetry, optical theorem |
| **QFT/TQFT/** | Topological QFT, Atiyah axioms, cobordisms, Chern-Simons, Dijkgraaf-Witten |
| **QFT/KontsevichSegal/** | Kontsevich-Segal criterion for well-defined QFT |

### Papers

Formalizations of specific physics papers and arguments:

| File | Topic |
|------|-------|
| **Bell.lean** | Bell's theorem (CHSH inequality, quantum violation, no local hidden variables) |
| **AMPS.lean** | AMPS firewall paradox (unitarity vs EFT vs Page's theorem) |
| **Phi4_2D.lean** | φ⁴ theory in 2D |
| **Coleman2D.lean** | Coleman's theorem on symmetry breaking in 2D |
| **VafaWitten.lean** | Vafa-Witten theorem on parity conservation |
| **cTheorem.lean** | Zamolodchikov's c-theorem |
| **Kolmogorov.lean** | Kolmogorov's theory of turbulence |
| **GlimmJaffe/** | Glimm-Jaffe constructive QFT (lattice theory, reflection positivity, cluster expansions, correlation inequalities, hypercontractivity) |

Papers include `_clean.lean` (code only, no comments) and `_interpretation.md` (mathematical exposition) companion files.

## Design Principles

- **No `axiom` declarations.** All physical assumptions are structure fields, visible to the reader. Lean axioms silently pollute the global environment — the opposite of this project's goal.
- **No `True` placeholders.** Structure fields must carry information. If a condition cannot yet be stated, omit it with a comment explaining why.
- **No bare `Prop` fields.** Every propositional field must express a meaningful constraint.
- **No trivially satisfiable `∃ x, ...` patterns.** Existentials must be constrained.
- **No smuggled assumptions.** Computational results cannot be assumed in definitions or structures.
- **Definitions must be sound.** "Conceptually correct" is not good enough — definitions must be accurate and proper.

## Building

```
lake build PhysicsLogic
```

To build a specific module:

```
lake build PhysicsLogic.Papers.AMPS
lake build PhysicsLogic.QFT.Wightman
```

Do not run `lake build` without a target (causes cache issues). Do not run `lake clean` (risks clearing the Mathlib cache).
