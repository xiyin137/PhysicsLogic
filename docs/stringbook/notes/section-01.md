# Section 01: Prologue

- Status: initial extraction complete
- Source page start: 18
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/Prologue.lean`

## Reading Summary
- Frames quantum gravity as a compatibility problem between general covariance and quantum mechanics, with asymptotic observables (S-matrix or AdS boundary observables) as the operational anchor.
- Uses the Weinberg-Witten obstruction as motivation that a local QFT stress-energy description is incompatible with massless spin-2 in the same framework.
- Reinterprets large-\(N\) Yang-Mills as weakly interacting flux strings (string splitting/joining amplitudes suppressed by \(1/N\)).
- Sets roadmap: bosonic string (including instability structure), BRST formulation, superstring extension, non-perturbative objects (D-branes), and holographic dualities.

## Candidate Formalization Units
- `WeinbergWittenCompatibility`: proposition-level interface for incompatibility between local stress tensor and emergent graviton in this abstraction layer.
- `LargeNYangMillsStringLimit`: records suppressed string interaction amplitudes at large \(N\).
- `AsymptoticObservableFramework`: separates asymptotically flat S-matrix observables from AdS boundary-source observables.

## Assumption Candidates
- `string.prologue.weinberg_witten_no_local_stress_tensor`
- `string.prologue.large_n_ym_weakly_coupled_flux_strings`

## Subsections
- [x] 1.1 The case of quantum gravity (p.18)
- [x] 1.2 Limitations of quantum field theory (p.20)
- [x] 1.3 Yang-Mills theory as a string theory (p.22)
- [x] 1.4 The road map (p.23)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
