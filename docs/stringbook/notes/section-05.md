# Section 05: Bosonic closed string field theory

- Status: initial extraction complete
- Source page start: 90
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/ClosedStringFieldTheory.lean`

## Reading Summary
- Introduces off-shell closed string fields in
  `H_0 = {Psi : b_0^- Psi = 0, L_0^- Psi = 0}` and constructs off-shell
  amplitudes by integrating a differential form `Omega[Psi_1,...,Psi_n]` over
  cycles `S_{h,n}` in `P-hat_{h,n}`.
- Extends `b`-ghost one-form insertions to include variations of local
  coordinate maps around punctures and proves the BRST identity
  `Omega[Q_B Psi] = - d Omega[Psi]`.
- Imposes plumbing-fixture compatibility of cycles near boundaries of moduli
  space, yielding off-shell factorization with Siegel-gauge propagator kernel
  `b_0^+ b_0^- / L_0^+`.
- Defines Siegel-gauge 1PI effective action and Legendre-transform relation to
  connected off-shell amplitudes; uses this framework to systematize mass/field
  renormalization and vacuum shifts.
- Builds classical closed SFT action with string vertices and string brackets,
  deriving equation of motion
  `E[Psi] = Q_B Psi + sum_{n>=2} (1/n!) [Psi^n] = 0`.
- Encodes geometric master equation into homotopy-Lie (`L_infinity`) identities
  for string brackets.
- Extracts low-derivative massless field dictionary in the flat-bracket frame
  relating SFT fields to covariant `G_{mu nu}`, `B_{mu nu}`, and `Phi`.
- Formulates background independence via infinitesimal maps between nearby CFT
  backgrounds preserving symplectic form and measure-weighted action.

## Candidate Formalization Units
- `ClosedStringFieldKinematicPackage`
- `OffShellAmplitudeCyclePackage`
- `BrstExteriorDerivativePackage`
- `PlumbingCycleCompatibilityPackage`
- `SiegelGaugePropagatorPackage`
- `OnePIEffectiveActionSiegelPackage`
- `ClassicalStringFieldEquationPackage`
- `StringBracketDualityPackage`
- `LInfinityHomotopyIdentityPackage`
- `MasslessFieldDictionaryPackage`
- `BackgroundIndependenceMapPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringSftClosedFieldSpaceHZero`.
- Candidate new `AssumptionId`: `stringSftOffShellAmplitudeCycle`.
- Candidate new `AssumptionId`: `stringSftBrstExteriorDerivativeIdentity`.
- Candidate new `AssumptionId`: `stringSftPlumbingCycleCompatibility`.
- Candidate new `AssumptionId`: `stringSftSiegelGaugePropagator`.
- Candidate new `AssumptionId`: `stringSftOnePiEffectiveActionSiegel`.
- Candidate new `AssumptionId`: `stringSftClassicalEquationWithBrackets`.
- Candidate new `AssumptionId`: `stringSftStringBracketDuality`.
- Candidate new `AssumptionId`: `stringSftLInfinityHomotopyIdentity`.
- Candidate new `AssumptionId`: `stringSftMasslessFieldDictionary`.
- Candidate new `AssumptionId`: `stringSftBackgroundIndependenceMap`.

## Subsections
- [x] 5.1 String field and off-shell amplitudes (p.90)
- [x] 5.2 1PI effective action in Siegel gauge (p.93)
- [x] 5.3 Classical string field theory (p.95)
- [x] 5.4 Batalin-Vilkovisky formalism (p.99)
- [x] 5.5 The BV formulation of quantum string field theory (p.101)
- [x] 5.6 String vertices and field redefinition (p.103)
- [x] 5.7 Perturbative classical solutions and diffeomorphism invariance (p.106)
- [x] 5.8 Background independence (p.112)

## Subsubsections
- [x] 5.7.1 Flat string brackets (p.106)
- [x] 5.7.2 Massless effective string field equations (p.108)
- [x] 5.7.3 Diffeomorphism transformation of string fields (p.110)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
