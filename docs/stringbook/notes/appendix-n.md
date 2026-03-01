# Appendix N: Supergravity

- Status: initial extraction complete
- Source page start: 779
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/GeneralRelativity/Supergravity.lean`, `PhysicsLogic/StringTheory/Backgrounds.lean`

## Reading Summary
- Introduces spinors in curved space via frame fields, curved gamma matrices, and spin connection compatibility with Levi-Civita geometry.
- Summarizes 11D supergravity field content (`e`, `C_3`, gravitino), local supersymmetry transformations, and the canonical 2-derivative action including the Chern-Simons term.
- Reviews type IIA/IIB supergravity field content and (pseudo-)actions in string frame, modified RR field strengths, and the IIB five-form self-duality constraint.
- Describes type I supergravity field content, Green-Schwarz-modified `H`-flux definition, gauge variation structure, and anomaly-cancellation requirements.
- Summarizes 4D `${\cal N}=2` supergravity couplings: special-Kahler vector-multiplet geometry, quaternionic-Kahler hypermultiplet geometry, gauging data, and scalar potential structure.
- Summarizes 4D `${\cal N}=1` supergravity couplings: Kahler target geometry, holomorphic Killing vectors/moment maps, gauge-kinetic constraints, and scalar potential decomposition.

## Candidate Formalization Units
- `CurvedSpinorGeometryCompatibility`: frame/metric/gamma compatibility package.
- `ElevenDSugraCorePackage`: 11D multiplet content and 4-form relation interface.
- `TypeIIAFormRelations`, `TypeIIBPseudoActionConstraints`: type II modified-form and self-duality interfaces.
- `TypeIGreenSchwarzHatH`: type I anomaly-canceling `Hhat` interface.
- `N2SpecialKahlerPotential`, `QuaternionicKahlerRicciRelation`: 4D `${\cal N}=2` geometry interfaces.
- `N2GaugedScalarPotentialDecomposition`: 4D `${\cal N}=2` gauged-potential decomposition interface.
- `N1SupergravityGaugeAndPotentialPackage`: 4D `${\cal N}=1` scalar-potential/gauge-kinetic package.

## Assumption Candidates
- Candidate new `AssumptionId`: `grSupergravityCurvedSpinorGeometry`.
- Candidate new `AssumptionId`: `grSupergravity11dCorePackage`.
- Candidate new `AssumptionId`: `stringSupergravityTypeIIAFormRelations`.
- Candidate new `AssumptionId`: `stringSupergravityTypeIIBPseudoActionConstraints`.
- Candidate new `AssumptionId`: `stringSupergravityTypeIGreenSchwarzHatH`.
- Candidate new `AssumptionId`: `grSupergravityN2SpecialKahlerPotential`.
- Candidate new `AssumptionId`: `grSupergravityN2QuaternionicRicciRelation`.
- Candidate new `AssumptionId`: `grSupergravityN2GaugedScalarPotential`.
- Candidate new `AssumptionId`: `grSupergravityN1GaugeAndPotentialPackage`.

## Subsections
- [x] N.1 Spinor fields in curved space (p.779)
- [x] N.2 11-dimensional supergravity (p.779)
- [x] N.3 Type II supergravity (p.780)
- [x] N.4 Type I supergravity (p.783)
- [x] N.5 4D ${\cal N}=2$ supergravity (p.784)
- [x] N.6 4D ${\cal N}=1$ supergravity (p.787)

## Subsubsections
- [x] N.5.1 Special K\"ahler geometry (p.785)
- [x] N.5.2 Quaternionic-K\"ahler geometry (p.786)
- [x] N.5.3 Recipes for gauging (p.787)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
