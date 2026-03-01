# Section 21: M-theory and holography

- Status: initial extraction complete
- Source page start: 484
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/MTheoryHolography.lean`

## Reading Summary
- Organizes M-theory holography around M2 and M5 near-horizon geometries, with
  explicit radius/flux scaling (`R^6 M11^6 = 32 pi^2 N2`, `R^3 M11^3 = pi N5`)
  and AdS radii (`R/2`, `2R`).
- Relates the M2 dual to the IR fixed point of 3D `N=8` SYM, including the
  `osp(8|4)` closure and Coulomb-branch structure
  `(S^1 x R^7)/Z_2`, generalized to `(S^1 x R^7)^N/S_N`.
- Builds ABJM as the `U(N)_k x U(N)_{-k}` Chern-Simons-matter SCFT, including
  integer level quantization, M-theory dual `AdS_4 x S^7/Z_k`,
  `lambda = N/k`, and vacuum moduli `(C^4/Z_k)^N/S_N`.
- Records supersymmetry enhancement at `k=1,2` from `osp(6|4)` to `osp(8|4)`
  and topological `U(1)_T` structure.
- Summarizes the 6D `(0,2)` SCFT algebra/multiplets (`osp(2,6|4)`, `D[0,k]`),
  compactification to 5D maximal YM via `gYM^2=(2pi)^2 R_M`, instanton KK
  interpretation, and center-of-mass-quotiented vacuum moduli.

## Candidate Formalization Units
- `M2NearHorizonPackage`
- `M5NearHorizonPackage`
- `D2GaugeCouplingRelation`
- `N8SymIrFixedPointPackage`
- `N8SymCoulombBranchSU2Package`
- `N8SymCoulombBranchUNPackage`
- `ABJMLevelQuantizationPackage`
- `ABJMHolographicMapPackage`
- `ABJMVacuumModuliPackage`
- `ABJMKOneTwoEnhancementPackage`
- `SixDZeroTwoSuperconformalPackage`
- `SixDZeroTwoToFiveDPackage`
- `SixDZeroTwoVacuumModuliPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringMTheoryM2NearHorizonPackage`.
- Candidate new `AssumptionId`: `stringMTheoryM5NearHorizonPackage`.
- Candidate new `AssumptionId`: `stringMTheoryD2GaugeCouplingRelation`.
- Candidate new `AssumptionId`: `stringMTheoryN8SymIrFixedPointPackage`.
- Candidate new `AssumptionId`: `stringMTheoryN8SymCoulombBranchSU2`.
- Candidate new `AssumptionId`: `stringMTheoryN8SymCoulombBranchUN`.
- Candidate new `AssumptionId`: `stringMTheoryAbjmLevelQuantization`.
- Candidate new `AssumptionId`: `stringMTheoryAbjmAdS4OrbifoldDuality`.
- Candidate new `AssumptionId`: `stringMTheoryAbjmVacuumModuliSpace`.
- Candidate new `AssumptionId`: `stringMTheoryAbjmKOneTwoEnhancement`.
- Candidate new `AssumptionId`: `stringMTheorySixD02SuperconformalMultiplets`.
- Candidate new `AssumptionId`: `stringMTheorySixD02ToFiveDCompactification`.
- Candidate new `AssumptionId`: `stringMTheorySixD02VacuumModuli`.

## Subsections
- [x] 21.1 The decoupling limit of M2 and M5-branes (p.484)
- [x] 21.2 The 3D ${\cal N}=8$ SYM and SCFT (p.486)
- [x] 21.3 The ABJM theory (p.489)
- [x] 21.4 The 6D $(0,2)$ SCFT (p.501)

## Subsubsections
- [x] 21.1.1 M2-branes and AdS$_4\times S^7$ (p.484)
- [x] 21.1.2 M5-branes and AdS$_7\times S^4$ (p.485)
- [x] 21.3.1 Brane construction (p.490)
- [x] 21.3.2 M-theory description and decoupling limit (p.493)
- [x] 21.3.3 Moduli space of vacua (p.495)
- [x] 21.3.4 Supersymmetry from the bulk perspective (p.497)
- [x] 21.3.5 Topological charge and monopole operators (p.498)
- [x] 21.4.1 The superconformal algebra and multiplets (p.501)
- [x] 21.4.2 Relation to 5D gauge theory (p.503)
- [x] 21.4.3 Moduli space of vacua and effective theory (p.504)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
