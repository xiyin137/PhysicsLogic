# Section 03: Quantization of the bosonic string

- Status: initial extraction complete
- Source page start: 39
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/Quantization.lean`, `PhysicsLogic/StringTheory/Backgrounds.lean`

## Reading Summary
- Formal BRST setup: gauge fixing + ghosts yields nilpotent BRST operator; physical states are BRST-closed modulo BRST-exact representatives.
- Worldsheet specialization: BRST current/charge in \(bc\)+matter CFT, anomaly cancellation tied to total central charge \(c=0\), i.e. \(D=26\) in bosonic critical background.
- Siegel constraint plus BRST closure enforces \(L_0=\widetilde L_0=0\), level matching, and mass-shell relation \(m^2=\frac{4}{\alpha'}(N-1)\).
- Equivalence chain is established between BRST cohomology, light-cone spectrum, and old-covariant quantization; DDF operators provide explicit bridge.
- Background deformation is encoded both as generalized sigma-model couplings \((G,B,\Phi)\) and as CFT deformations; Weyl-invariance conditions lead to spacetime effective equations.

## Candidate Formalization Units
- `BRSTComplex` + `BRSTClosed`/`BRSTExact` interfaces.
- `SiegelConstraint` and abstract implication to level matching.
- `BosonicMassShell` relation for level \(N\).
- `BackgroundBetaSystem` interface linking worldsheet Weyl conditions to spacetime effective-field equations.

## Assumption Candidates
- `string.bosonic.brst_physical_states_cohomology`
- `string.bosonic.siegel_implies_level_matching`
- `string.bosonic.mass_spectrum_formula`
- `string.background.weyl_beta_vanishing`
- `string.background.beta_to_spacetime_eom`
- `string.background.c1_tachyon_massless`

## Subsections
- [x] 3.1 BRST quantization (p.39)
- [x] 3.2 BRST on the worldsheet (p.42)
- [x] 3.3 Siegel constraint and BRST cohomology (p.45)
- [x] 3.4 Equivalence to light cone gauge (p.49)
- [x] 3.5 Equivalence to old covariant quantization (p.52)
- [x] 3.6 DDF operators (p.53)
- [x] 3.7 Deforming the spacetime background (p.54)
- [x] 3.8 $c=1$ string theory (p.60)

## Subsubsections
- [x] 3.7.1 Generalized Polyakov path integral (p.54)
- [x] 3.7.2 Deforming the matter CFT (p.58)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
