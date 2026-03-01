# Section 02: The effective string and its quantization

- Status: initial extraction complete
- Source page start: 25
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/EffectiveString.lean`

## Reading Summary
- Introduces Nambu-Goto action from worldsheet embedding with diffeomorphism redundancy and derives long-wavelength transverse massless modes in static gauge.
- Extracts classical Regge scaling \(E^2 = 4\pi T J\) for folded rotating strings, motivating hadronic/string connections.
- Builds effective string expansion via induced metric and extrinsic curvature; clarifies which lower-weight corrections are removable/topological.
- Establishes classical equivalence of Nambu-Goto and Polyakov formulations via worldsheet metric equation of motion and conformal gauge.
- First quantization attempt via gauge-fixed Polyakov path integral identifies Weyl anomaly cancellation at \(D=26\) as criticality condition.

## Candidate Formalization Units
- `NambuGotoModel`: embedding and tension data.
- `ReggeTrajectoryLaw`: interface for rotating-string energy-spin relation.
- `PolyakovModel`: worldsheet metric + embedding with Virasoro-constraint channel.
- `CriticalBosonicCondition`: Weyl anomaly cancellation criterion.

## Assumption Candidates
- `string.effective.ng_polyakov_equivalence`
- `string.effective.regge_trajectory`
- `string.bosonic.critical_dimension_26`

## Subsections
- [x] 2.1 Nambu-Goto theory (p.25)
- [x] 2.2 The effective string (p.27)
- [x] 2.3 Polyakov's formalism (p.29)
- [x] 2.4 A first attempt at quantization (p.30)
- [x] 2.5 Critical string theory (p.34)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
