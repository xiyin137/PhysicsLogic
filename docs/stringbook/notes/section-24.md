# Section 24: Strings from ${\cal N}=4$ SYM II: mirror TBA and the quantum spectral curve

- Status: initial extraction complete
- Source page start: 573
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/AdS5MirrorTBAQSC.lean`

## Reading Summary
- Introduces the mirror model by double Wick rotation of AdS5xS5 magnons and
  motivates finite-volume spectra from mirror thermal observables.
- Derives one-species TBA, then excited-state quantization via zeros of
  `1+exp(-zeta)`, and generalizes to nested mirror Bethe-Yang systems.
- Classifies mirror Bethe strings (`bullet_n`, `oplus/ominus`, `n|yw`,
  `n|w`) and formulates coupled mirror-TBA equations with kernel/scattering
  data and fermionic chemical-potential signs.
- Rewrites mirror TBA into the T-hook Y-system and Hirota `T`-system,
  including analyticity-strip and branch-cut structure.
- Develops finite-volume excited-state energies and asymptotic conditions,
  including wrapping corrections and Konishi weak-coupling checks.
- Reformulates the spectral problem as the `Pmu` quantum spectral curve,
  with monodromy constraints, asymptotic power laws, weak-coupling Baxter
  reduction, and small-spin expansion logic.

## Candidate Formalization Units
- `MirrorDoubleWickMapPackage`
- `MirrorMagnonDispersionPackage`
- `OneSpeciesMirrorTBAPackage`
- `MirrorExcitedStateQuantizationPackage`
- `MirrorBetheYangFactorizationPackage`
- `MirrorBetheStringPackage`
- `MirrorMultiSpeciesTBAPackage`
- `MirrorYSystemPackage`
- `FiniteVolumeMirrorEnergyPackage`
- `KonishiWrappingCorrectionPackage`
- `QuantumSpectralCurvePMuPackage`
- `PMuAsymptoticPackage`
- `WeakCouplingBaxterPackage`
- `SmallSpinExpansionPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringAdS5MirrorDoubleWickMap`.
- Candidate new `AssumptionId`: `stringAdS5MirrorMagnonDispersion`.
- Candidate new `AssumptionId`: `stringAdS5MirrorSingleSpeciesTba`.
- Candidate new `AssumptionId`: `stringAdS5MirrorExcitedStateQuantization`.
- Candidate new `AssumptionId`: `stringAdS5MirrorBetheYangSystem`.
- Candidate new `AssumptionId`: `stringAdS5MirrorBetheStrings`.
- Candidate new `AssumptionId`: `stringAdS5MirrorTbaEquationSystem`.
- Candidate new `AssumptionId`: `stringAdS5MirrorYSystemHirota`.
- Candidate new `AssumptionId`: `stringAdS5MirrorFiniteVolumeEnergy`.
- Candidate new `AssumptionId`: `stringAdS5MirrorKonishiWrapping`.
- Candidate new `AssumptionId`: `stringAdS5MirrorQuantumSpectralCurvePMu`.
- Candidate new `AssumptionId`: `stringAdS5MirrorPMuAsymptotics`.
- Candidate new `AssumptionId`: `stringAdS5MirrorWeakCouplingBaxter`.
- Candidate new `AssumptionId`: `stringAdS5MirrorSmallSpinExpansion`.

## Subsections
- [x] 24.1 Mirror model and thermodynamic Bethe ansatz (p.573)
- [x] 24.2 Bethe strings of the mirror model (p.577)
- [x] 24.3 Mirror TBA (p.580)
- [x] 24.4 The $Y$-system (p.582)
- [x] 24.5 Excited states in finite volume and asymptotic conditions (p.585)
- [x] 24.6 The Konishi operator and wrapping corrections (p.588)
- [x] 24.7 The quantum spectral curve (p.591)
- [x] 24.8 Asymptotic conditions for the ${\bf P}\mu $-system (p.596)
- [x] 24.9 String spectrum from the quantum spectral curve (p.599)

## Subsubsections
- [x] 24.1.1 The case of one particle type (p.573)
- [x] 24.1.2 Excited states (p.575)
- [x] 24.1.3 TBA from Bethe-Yang equations (p.576)
- [x] 24.7.1 Hirota system in the ${\cal T}$-gauge (p.591)
- [x] 24.7.2 ${\bf T}$-gauge (p.592)
- [x] 24.7.3 ${\mathbb T}$-gauge (p.593)
- [x] 24.7.4 The ${\bf P}\mu $-system (p.594)
- [x] 24.9.1 Weak coupling limit (p.599)
- [x] 24.9.2 Small spin expansion (p.600)
- [x] 24.9.3 Konishi at strong coupling (p.602)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
