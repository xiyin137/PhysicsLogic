# Section 16: D-instantons

- Status: initial extraction complete
- Source page start: 333
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/DInstantons.lean`

## Reading Summary
- Extracted the non-perturbative D-instanton transseries setup for closed-string
  amplitudes: perturbative plus D-instanton sectors, moduli-space integration
  over D-instanton boundary conditions, disconnected-worldsheet
  exponentiation/decomposition, and the role of open-string boundary
  divergences in defining non-perturbative prescriptions (`ainstgend`,
  `acdecom`, `naiveacexp`).
- Extracted the `c=1` ZZ-instanton sector: instanton action
  `S_ZZ = 1/(2 g_s)`, matrix-model bounce-action matching, non-perturbative
  unitarity-deficit interpretation, leading `1 -> n` amplitude from disc
  one-point functions, and normalization matching to particle-hole amplitudes
  (`szzact`, `oneminusp`, `sinstconef`, `ninstampa`, `ninstmatch`).
- Extracted type-IIB D(-1)-instanton data: axio-dilaton action dictionary for
  `(n,m)` instantons, breaking of continuous axion shift to integer shifts,
  and instanton expansion of the four-supergraviton coupling function
  (`fstamp`, `leadingdinstiib`, `thetaxrela`, `leadingdinstiibb`,
  `discderiv`, `susydacond`, `vdkocq`, `vakaxocq`, `dadisconept`,
  `ampdssupsim`, `fonezero`).
- Extracted open+closed SFT treatment of D-instantons: D-instanton contribution
  as open-field functional integral in BV formalism, collective-mode/moduli
  reparameterization via open-field background independence, zero-weight mode
  subtleties, singular Siegel gauge, FP replacement by gauge-volume division,
  and contour/Wick-rotation handling (`dinstpertsft`, `openkinet`,
  `zeroweightbos`, `zeroweightsup`, `varkkin`, `infgauh`, `fpsub`,
  `kappaprop`, `ddspeccoup`, `thetachi`, `thetachiz`).
- Extracted normalization computations in the SFT framework:
  ZZ-instanton normalization from open-string zero-mode integrals and trace
  cancellation (`szzpertsft`, `tracezz`, `ceezz`), and type-IIB
  single-instanton zero-mode measure fixing yielding
  `N^(1,0) ~ tau_2^(-7/2)` and leading
  `f^(1,0) = 4 pi tau_2^(-3/2) + O(tau_2^(-5/2))`
  (`hodinstsup`, `osftinstdd`, `psizerocrelax`, `annusupdinst`,
  `siegsupinst`, `siegsupinstsub`, `xthetaidaa`, `cdtwosupaa`,
  `nonezerores`, `dinstiibres`).
- Extracted multi-D-instanton extension and IKKT reduction: `(k,0)` amplitude
  structure with `U(k)` Chan-Paton factors, matrix-valued zero modes, reduced
  supersymmetric matrix action, normalization in terms of IKKT matrix integral
  `Z(k)`, and resulting leading scaling for the four-supergraviton coupling
  (`leadingdinsmulti`, `siegsupinstsubmulti`, `sintexpxxkk`, `nkkzerores`).

## Candidate Formalization Units
- `DInstantonTransseriesPackage`
- `COneZzInstantonPackage`
- `TypeIIBDMinusOneInstantonPackage`
- `DInstantonOpenClosedSftZeroModePackage`
- `DInstantonNormalizationPackage`
- `MultipleDInstantonIkktPackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringDinstantonTransseriesAndModuliIntegral`.
- Mapped `AssumptionId`: `stringDinstantonCOneZzContributionAndNormalization`.
- Mapped `AssumptionId`: `stringDinstantonTypeIIBAxioDilatonExpansion`.
- Mapped `AssumptionId`: `stringDinstantonOpenClosedSftZeroModeGaugeFixing`.
- Mapped `AssumptionId`: `stringDinstantonNormalizationFromZeroModeMeasure`.
- Mapped `AssumptionId`: `stringDinstantonMultipleIkktIntegralScaling`.

## Subsections
- [x] 16.1 The effect of D-instantons (p.333)
- [x] 16.2 D-instantons in $c=1$ string theory (p.336)
- [x] 16.3 D-instantons in type IIB string theory (p.337)
- [x] 16.4 Open+closed string field theory of D-instantons (p.342)
- [x] 16.5 The normalization of D-instanton amplitudes (p.345)
- [x] 16.6 Multiple D-instantons (p.349)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
