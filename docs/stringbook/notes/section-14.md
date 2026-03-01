# Section 14: D-brane dynamics in type II superstring theory

- Status: initial extraction complete
- Source page start: 280
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/DBraneDynamicsTypeII.lean`

## Reading Summary
- Extracted open+closed type-II perturbation framework on super Riemann
  surfaces with boundary (BSRS): boundary supercoordinate transition rules,
  BSRS supermoduli dimensions, spin-structure counting/summation, amplitude
  normalization, and PCO/vertical-integration implementation (`dryzztrans`,
  `openclosedsupamp`, `normopensup`, `openclosedsupamppco`, `wtompcoop`).
- Extracted disc normalization and coupling dictionary for open superstrings on
  BPS D$p$-branes: ghost/matter disc correlator conventions, boundary-state
  normalization relation, massless NS gauge-boson vertex normalization, and
  `g_s`-`g_o` relation (`discnormsup`, `ndtwosup`, `vasupe`, `gsgosup`).
- Extracted disc open-string amplitudes on stacked branes: 3-gauge-boson
  reduced amplitude and YM vertex matching, 4-gauge-boson gamma-function
  structure, low-energy expansion, and leading `alpha'^2 t8 F^4` correction
  (`discuspthr`, `aredthrop`, `assupopeff`, `gymgobos`, `discfoursup`,
  `redufouraop`, `gammstexpa`, `seffteightf`).
- Extracted disc open+closed amplitudes with RR insertion: couplings to
  worldvolume gauge potential and transverse displacement, identifying
  Chern-Simons and RR-charge couplings (`coamprr`, `afdiscc`, `fdeltxdpc`).
- Extracted cylinder amplitudes in type II: spin-structure decomposition,
  open-channel trace form, NSNS/RR exchange split, modular rewrites, large
  distance massless term extraction, and exact NSNS-RR cancellation for
  parallel BPS D$p$-branes (`cylsupgen`, `epsopensupcyl`, `cylampint`,
  `zcylminu`, `arrnsns`).
- Extracted BPS D-brane effective action with supersymmetry and kappa symmetry:
  supersymmetry transformations, invariant `Pi` and `calF`, DBI+WZ form,
  kappa-projector construction, static+kappa gauge fixing, static action, and
  tension determination from matching (`dbrandusytrans`, `deltaagau`, `susydbi`,
  `sumwpsi`, `kappaax`, `upsidef`, `calpdefs`, `staticdp`, `kappafixlam`,
  `dbistatic`, `tpgssup`).
- Extracted coupling to general massless closed-string backgrounds: bosonic
  DBI+WZ action, RR coupling hierarchy, `mu_p = T_p`, and tension-coupling
  consistency with long-distance cylinder exchange (`bosacteff`, `sulkbf`,
  `mutprel`, `tpkapsup`).
- Extracted RR charge quantization: electric/magnetic dual brane sourcing,
  flux quantization, Dirac condition, minimal RR charge product, and physical
  type IIA/IIB coupling definitions (`dfpeom`, `magquant`, `sdprrt`,
  `diracquant`, `giibdef`, `giiadef`).
- Extracted supersymmetric wrapped/configured branes via kappa projector:
  general condition, D2 holomorphic-curve projectors, D3 special-Lagrangian
  projectors, and worldvolume-flux BPS/BIon solutions with F1-charge
  interpretation (`delkapeps`, `overepskap`, `kilinspia`, `upsidbra`,
  `upsidtwos`, `gamepsi`, `omegallspl`, `overepres`, `bionsusyc`,
  `kilsusybion`).
- Extracted non-Abelian effective theory for stacked D-branes and vacuum
  moduli: maximally supersymmetric adjoint field content, commutator
  potential, and geometric interpretation of diagonal scalar vevs
  (`nonabeff`, `xicacdp`).
- Extracted D0-brane scattering and bound-state dynamics: D0 mass and
  quantization, moving-D0 cylinder amplitude and long-distance expansion,
  effective `v^4/r^7` behavior, low-energy BFSS Hamiltonian/supercharge
  algebra, gauge constraint, center-of-mass split, and threshold bound-state
  statement (`tzeromass`, `thetacomdo`, `cylampdzeos`, `cylampdzeosimp`,
  `cabpsig`, `bfssham`, `xprescal`, `qqhdzer`, `hsplithp`).

## Candidate Formalization Units
- `OpenClosedTypeIIPerturbationPackage`
- `DiscOpenGaugeAmplitudePackage`
- `DiscOpenClosedRrCouplingPackage`
- `CylinderTypeIICancellationPackage`
- `BpsKappaSymmetricActionPackage`
- `BpsBackgroundCouplingPackage`
- `RrChargeDiracQuantizationPackage`
- `WrappedBraneSupersymmetryPackage`
- `D2HolomorphicCurveBpsPackage`
- `D3SpecialLagrangianBpsPackage`
- `WorldvolumeFluxBionPackage`
- `StackedDbraneNonAbelianPackage`
- `D0ScatteringBfssPackage`

## Assumption Candidates
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIOpenClosedPerturbation`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIDiscOpenGaugeAmplitudes`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIDiscOpenClosedRrCouplings`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIICylinderNsnsRrCancellation`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIBpsKappaSymmetricAction`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIBpsBackgroundCouplings`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIRrChargeDiracQuantization`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIWrappedBraneSupersymmetry`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIID2HolomorphicCurveBps`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIID3SpecialLagrangianBps`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIIWorldvolumeFluxBion`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIINonAbelianStackedEffectiveTheory`.
- Mapped `AssumptionId`: `stringDbraneDynamicsTypeIID0ScatteringBfssMatrixQM`.

## Subsections
- [x] 14.1 Open+closed superstring perturbation theory (p.280)
- [x] 14.2 Disc open string amplitudes (p.282)
- [x] 14.3 Disc open+closed string amplitudes (p.285)
- [x] 14.4 Cylinder amplitudes (p.286)
- [x] 14.5 BPS D-brane effective action (p.288)
- [x] 14.6 Some supersymmetric D-brane configurations (p.294)
- [x] 14.7 Non-Abelian effective gauge theory of stacked D-branes (p.298)
- [x] 14.8 Scattering and bound states of D0-branes (p.300)

## Subsubsections
- [x] 14.5.1 Supersymmetry and $\kappa $ symmetry (p.288)
- [x] 14.5.2 Coupling to massless closed string background (p.291)
- [x] 14.5.3 Quantization of RR charge (p.292)
- [x] 14.6.1 D2-brane wrapping a holomorphic curve (p.295)
- [x] 14.6.2 D3-brane wrapping a special Lagrangian subspace (p.295)
- [x] 14.6.3 Turning on the world volume field strength (p.296)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
