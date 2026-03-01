# Section 18: Non-perturbative dualities

- Status: initial extraction complete
- Source page start: 372
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/Dualities.lean`

## Reading Summary
- Extracted heterotic/type-I strong-weak duality dictionary in Einstein frame:
  opposite-dilaton identification, matching of effective couplings/tensions,
  heterotic fundamental string to type-I D1 map, NS5 to D5 map, and non-BPS
  state correspondence (`shetein`, `kappagymhet`, `stypeiein`,
  `kappagymtypei`, `phirelhetypei`, `hetitenrel`).
- Extracted NS5-brane sector: quantized `H`-flux, BPS type-II NS5 solution,
  Killing-spinor constraints, near-throat geometry with linear dilaton and
  `SU(2)_k` WZW structure, little-string-theory interpretation, and heterotic
  NS5/gauge-instanton interpolation with small-instanton limit
  (`hfluxquant`, `nsfiveans`, `susyvarnsf`, `hijkform`, `abeqnr`,
  `chsseneps`, `nsfivesol`, `einnsfive`, `tennsfive`, `nsfivesolnear`,
  `lstcft`, `hhatfluxquant`, `gauginovarc`, `strnsfivehet`, `hphisol`,
  `fijinst`, `phiddpro`, `aixynmhetnsf`, `instchquant`, `ephisol`).
- Extracted type-IIB S-duality content: low-energy `SL(2,R)` action on
  axio-dilaton/two-forms, exact `SL(2,Z)` conjecture, modular constraints on
  protected couplings, Laplace-type equation for `R^4` coefficient, and
  Eisenstein-series completion matching perturbative and D-instanton data
  (`iibsugsltwo`, `taudefsl`, `moobsltwor`, `abcdsltz`, `fourgravexactamp`,
  `mpliib`, `fzerotau`, `susydiffeqn`, `fzerosol`).
- Extracted `(p,q)`-string and 5-brane structure from duality orbits:
  D1 worldvolume electric-flux quantization, F1/D1 exchange under `S`,
  `(p,1)` and general `(p,q)` tension formulas, non-Abelian flux splitting,
  and 5-brane analogs under `SL(2,Z)` (`tfonedone`, `ldoneinduced`,
  `gaugegg`, `aoneperiod`, `paoneform`, `paoneformqu`, `tnoneone`,
  `tpqform`, `nonabfluxex`, `gaugfluxsplit`).
- Extracted black p-brane supergravity dictionaries: RR flux quantization,
  black D3 solution and radius dictionary, and general black p-brane metric,
  dilaton, field-strength, and warp-factor parameter relations
  (`fluxfn`, `dthransa`, `sfffrel`, `abdthsol`, `dthreekilling`, `frrsol`,
  `thbrradius`, `dthransasol`, `blackpbranemetric`, `blackpbranephif`,
  `fprsol`).
- Extracted D7/F-theory construction: axio-dilaton monodromies,
  `j(tau)`-based elliptic-fibration ansatz, supersymmetry constraints, K3
  elliptic realization, and Sen orientifold limit (`einmetsev`, `naivetau`,
  `eingensev`, `susyadil`, `killingmonod`, `jtau`, `jtauweier`,
  `ellipticcurve`, `senfg`, `sengeom`, `stwomono`, `senorient`).
- Extracted M-theory dictionary and substructures: 11D-to-IIA reduction,
  D0/KK momentum map and radius/Planck relations, M2/M5 tension maps,
  D6-KK-monopole uplift, M-theory to F-theory via elliptic-fiber limit, and
  protected higher-derivative terms from decompactification
  (`kkansel`, `einhred`, `kappaelv`, `rlevel`, `kappamelev`, `tmtwo`,
  `tmfifoa`, `kkmonopolem`, `fourdgeom`, `taurrten`, `mampiia`).
- Extracted heterotic M-theory chain: hetE/hetO circle T-duality with Wilson
  lines, strong-coupling hetE to M-theory on interval, boundary gauge-coupling
  dictionary, Horava-Witten bulk-boundary action and anomaly inflow, and
  heterotic instanton/M5 transition (`adeformeelat`, `hetegaugebkgrd`,
  `hetelat`, `aninhetoo`, `hetolatgen`, `hetogaugebkgrd`, `hetolat`,
  `tdualhetlat`, `ghetalphap`, `dimlesseoi`, `melvdefmhet`, `rahetecoup`,
  `gymbdry`, `bulkbdryelevact`, `gffrrpre`, `gffrr`, `cthbdrycond`,
  `cthgaug`, `delSanom`, `delGanom`, `delGanomxx`, `tfivebdry`,
  `tfivebdrynex`).
- Extracted D8/massive-IIA sector: T-dual axion monodromy interpretation,
  `F_0` quantization, Romans-mass deformation of IIA supergravity, scalar
  potential, and consistency of supersymmetric O8-D8 interval systems
  (`axionmonorom`, `fzeroquant`, `iiasugraactmassive`, `sdadeights`).

## Candidate Formalization Units
- `HeteroticTypeIDualityPackage`
- `TypeIINs5BpsPackage`
- `Ns5ThroatScftPackage`
- `HeteroticNs5InstantonPackage`
- `TypeIibSdualityPackage`
- `PqStringsFiveBranesPackage`
- `BlackPBranePackage`
- `D7FTheoryPackage`
- `MTheoryTypeIIACirclePackage`
- `M2M5DictionaryPackage`
- `D6KkMonopolePackage`
- `MTheoryHigherDerivativePackage`
- `HeteroticCircleTdualityPackage`
- `HeteroticStrongCouplingIntervalPackage`
- `HoravaWittenBoundaryPackage`
- `MassiveIiaRomansD8Package`

## Assumption Candidates
- Mapped `AssumptionId`: `stringDualityHeteroticTypeIStrongWeak`.
- Mapped `AssumptionId`: `stringDualityTypeIINS5BpsSoliton`.
- Mapped `AssumptionId`: `stringDualityNS5ThroatLittleStringScft`.
- Mapped `AssumptionId`: `stringDualityHeteroticNS5GaugeInstantonSmallInstanton`.
- Mapped `AssumptionId`: `stringDualityTypeIIBSdualityModularInvariantCouplings`.
- Mapped `AssumptionId`: `stringDualityPQStringsAndFiveBranes`.
- Mapped `AssumptionId`: `stringDualityBlackPBraneSupergravityDictionary`.
- Mapped `AssumptionId`: `stringDualityD7BraneFTheoryEllipticMonodromy`.
- Mapped `AssumptionId`: `stringDualityMTheoryTypeIIACircleRelation`.
- Mapped `AssumptionId`: `stringDualityM2M5BraneTensionDictionary`.
- Mapped `AssumptionId`: `stringDualityD6KaluzaKleinMonopoleUplift`.
- Mapped `AssumptionId`: `stringDualityMTheoryHigherDerivativeProtectedTerms`.
- Mapped `AssumptionId`: `stringDualityHeteroticE8SO32CircleTduality`.
- Mapped `AssumptionId`: `stringDualityHeteroticStrongCouplingMTheoryInterval`.
- Mapped `AssumptionId`: `stringDualityHoravaWittenBoundaryAnomalyInflow`.
- Mapped `AssumptionId`: `stringDualityMassiveIIARomansD8System`.

## Subsections
- [x] 18.1 Heterotic/type I duality (p.372)
- [x] 18.2 NS5-branes (p.374)
- [x] 18.3 S-duality of type IIB string theory (p.379)
- [x] 18.4 $(p,q)$-strings and 5-branes (p.382)
- [x] 18.5 Black $p$-branes (p.385)
- [x] 18.6 D7-branes and F-theory (p.388)
- [x] 18.7 M-theory (p.392)
- [x] 18.8 Heterotic M-theory (p.398)
- [x] 18.9 D8-branes and massive IIA string theory (p.405)

## Subsubsections
- [x] 18.2.1 NS5-branes in type II string theories (p.374)
- [x] 18.2.2 Worldsheet description of the NS5-brane throat (p.376)
- [x] 18.2.3 Heterotic NS5-brane and gauge instantons (p.377)
- [x] 18.7.1 M2 and M5-branes (p.393)
- [x] 18.7.2 Kaluza-Klein monopole (p.394)
- [x] 18.7.3 From M to F-theory (p.395)
- [x] 18.7.4 Corrections to 11D supergravity (p.396)
- [x] 18.8.1 T-duality between hetE and hetO theories (p.398)
- [x] 18.8.2 The strong coupling limit of hetE (p.400)
- [x] 18.8.3 The effective action of M-theory with boundary (p.402)
- [x] 18.8.4 Heterotic instanton and M5-brane (p.405)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
