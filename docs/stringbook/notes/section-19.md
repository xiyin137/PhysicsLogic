# Section 19: Geometric singularities and transitions

- Status: initial extraction complete
- Source page start: 409
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/GeometricSingularities.lean`
- Cross-lane bridge target: `PhysicsLogic/StringTheory/SingularityCFTBridge.lean`
- QFT target: `PhysicsLogic/QFT/CFT/TwoDimensional/ConformalManifolds.lean`

## Reading Summary
- Extracted NS5 transverse-circle background and Buscher T-duality map to Taub-NUT
  geometry, including the orbifold limit `C^2/Z_k` and the NS5 position/moduli
  dictionary (`nsfivtanspp`, `uxsmear`, `pretduabush`, `adstdua`, `dwrtamet`,
  `macsnn`).
- Extracted `C^2/Z_k` orbifold `(4,4)` SCFT structure: supercurrents,
  twisted-sector chiral primaries, exactly marginal descendants, and conformal
  manifold geometry with ALE plus `B`-period coordinates in the `k=2` case
  (`ggtnfour`, `mmabstr`, `dscalm`, `mtwoaone`, `alefir`, `bfieflat`).
- Extracted singular-CFT and wrapped-brane physics near orbifold points,
  including exact BPS wrapped D2 mass formulas and `SU(k)` gauge enhancement,
  plus fractional-brane boundary-state constructions (`massdonesus`,
  `massdtwpt`, `wtbzero`, `bmzerwt`).
- Extracted DSLST double-scaling NS5 limit and exact worldsheet realization via
  `((SL(2,R)_k/U(1)) x (SU(2)_k/U(1)))/Z_k`, including detailed coset spectra,
  spectral-flow/selection constraints, cigar-Liouville mirror map, and massless
  six-dimensional field interpretation (`dslstcoupaa`, `slsucosntwo`,
  `mmmodspecsu`, `mmkzconstsl`, `ntwoliuvactsp`, `jmmquanum`, `specrrpara`).
- Extracted conifold geometry package: singular/deformed/resolved branches,
  period/prepotential relations, wrapped D3/D2 hypermultiplet resolution of EFT
  singularities, and Higgs/Coulomb branch transition interpretation in type IIB
  and IIA (`conifoldmetric`, `wideformcn`, `resconmet`, `fxdefomconfld`,
  `vpotconitra`, `ftconiwsinst`, `massdtwosb`).
- Extracted worldsheet instanton computation for resolved conifold Yukawa data,
  including holomorphic-map saddle classification, topological-twist
  localization, and degree-`k` coefficient result `a_k = 1/k^3`
  (`sinfirstevalws`, `zzrationalmap`, `resultantdef`, `formpathsswsinst`,
  `actionexpswsins`, `akinstres`).
- Extracted singular-conifold CFT description from GLSM dualization and
  `k=1` `N=2` Liouville effective limit at the conifold point (`yloci`).
- Extracted M-theory singularity package: `C^2/Z_k` orbifold localized gauge
  sector, `G_2` cone with triality-related smooth branches, calibrated
  three-cycles, complex modulus from `C_3` period plus volume, and triality-
  invariant quantum moduli curve (`sevndgacoup`, `conifigtwo`, `trialityab`,
  `smoothycone`, `tcomplmthe`, `etathreeprod`, `etatwothr`).

## Candidate Formalization Units
- `Ns5TaubNutDualityPackage`
- `OrbifoldTwistMarginalPackage`
- `OrbifoldConformalManifoldPackage`
- `OrbifoldWrappedBraneGaugeEnhancementPackage`
- `OrbifoldFractionalBranePackage`
- `DslstDoubleScalingPackage`
- `DslstSu2CosetPackage`
- `DslstSl2CosetPackage`
- `DslstLiouvilleMirrorPackage`
- `DslstMasslessSpectrumPackage`
- `ConifoldGeometryPackage`
- `ConifoldTypeIibTransitionPackage`
- `ConifoldTypeIiaTransitionPackage`
- `ConifoldWorldsheetInstantonPackage`
- `ConifoldSingularCftPackage`
- `MTheoryOrbifoldSingularityPackage`
- `MTheoryGTwoConePackage`
- `MTheoryQuantumModuliPackage`
- `OrbifoldSingularityCftBridgePackage`
- `DslstCosetCftBridgePackage`
- `CigarLiouvilleMirrorBridgePackage`
- `ConifoldInstantonNlsmBridgePackage`
- `OrbifoldConformalManifoldDimensionFormula`
- `ZamolodchikovMetricTwoPointNormalization`
- `OrbifoldKTwoModuliFixedPointDistinction`

## Assumption Candidates
- Mapped `AssumptionId`: `stringSingularityNs5TaubNutTDuality`.
- Mapped `AssumptionId`: `stringSingularityOrbifoldNFourTwistMarginal`.
- Mapped `AssumptionId`: `stringSingularityOrbifoldConformalManifoldSingularPoints`.
- Mapped `AssumptionId`: `stringSingularityOrbifoldWrappedDbraneGaugeEnhancement`.
- Mapped `AssumptionId`: `stringSingularityOrbifoldFractionalBraneBoundaryState`.
- Mapped `AssumptionId`: `stringDslstDoubleScalingCosetBackground`.
- Mapped `AssumptionId`: `stringDslstSu2CosetNTwoStructure`.
- Mapped `AssumptionId`: `stringDslstSl2CosetCigarSpectrum`.
- Mapped `AssumptionId`: `stringDslstCigarLiouvilleMirrorDuality`.
- Mapped `AssumptionId`: `stringDslstMasslessSpectrumSixDInterpretation`.
- Mapped `AssumptionId`: `stringConifoldGeometryDeformedResolvedMetrics`.
- Mapped `AssumptionId`: `stringConifoldTypeIibTransitionWrappedD3Hypermultiplet`.
- Mapped `AssumptionId`: `stringConifoldTypeIiaTransitionWrappedD2Hypermultiplet`.
- Mapped `AssumptionId`: `stringConifoldWorldsheetInstantonExpansion`.
- Mapped `AssumptionId`: `stringConifoldSingularCftGlsmLiouvilleLimit`.
- Mapped `AssumptionId`: `stringMTheoryOrbifoldSingularityGaugeSector`.
- Mapped `AssumptionId`: `stringMTheoryGTwoConeBranchesAssociativeCycles`.
- Mapped `AssumptionId`: `stringMTheoryQuantumModuliCurveTrialityInvariant`.

## Subsections
- [x] 19.1 NS5-branes and Taub-NUT space (p.409)
- [x] 19.2 $\mathbb {C}^2/\mathbb {Z}_k$ orbifolds (p.411)
- [x] 19.3 D-branes in orbifolds (p.416)
- [x] 19.4 Double scaled little string theory (p.418)
- [x] 19.5 Conifold in string theory (p.431)
- [x] 19.6 Singularities in M-theory (p.452)

## Subsubsections
- [x] 19.2.1 Twist fields and marginal deformations (p.412)
- [x] 19.2.2 Geometry of the conformal manifold (p.413)
- [x] 19.2.3 Singular CFT and massless D-branes (p.415)
- [x] 19.4.1 The ${\cal N}=2$ $SU(2)_k/U(1)$ coset CFT (p.420)
- [x] 19.4.2 The ${\cal N}=2$ $SL(2,\mathbb {R})_k/U(1)$ coset CFT (p.423)
- [x] 19.4.3 Relation to ${\cal N}=2$ Liouville theory (p.426)
- [x] 19.4.4 The worldsheet theory of double scaled LST (p.427)
- [x] 19.5.1 The conifold geometry (p.431)
- [x] 19.5.2 Conifold transition in type IIB string theory (p.433)
- [x] 19.5.3 Conifold in type IIA string theory (p.439)
- [x] 19.5.4 Worldsheet instantons (p.444)
- [x] 19.5.5 The singular CFT at the conifold point (p.451)
- [x] 19.6.1 Orbifold singularities in M-theory (p.452)
- [x] 19.6.2 $G_2$ holonomy and singularities (p.453)
- [x] 19.6.3 Quantum moduli space of M-theory vacua with conical asymptotics (p.456)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
