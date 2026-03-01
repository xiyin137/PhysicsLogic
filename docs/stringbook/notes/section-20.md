# Section 20: The AdS/CFT correspondence

- Status: initial extraction complete
- Source page start: 458
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/AdSCFT.lean`

## Reading Summary
- Sets up D$p$-brane decoupling logic and specializes to the D3 near-horizon throat with smooth `AdS_5 x S^5` geometry.
- Records the core AdS/CFT parameter map `g_B = g_YM^2/(2pi)`, `lambda = 2 g_YM^2 N`, and `R^4/alpha'^2 = lambda`.
- Reviews `N=4` SYM superconformal structure (`psu(2,2|4)`), Coulomb-branch moduli space `(R^6)^N / S_N`, and W-boson mass relation.
- Connects probe D3-brane Born-Infeld expansion to Coulomb-branch low-energy `U(1)` effective theory.
- Derives Poincare-to-global AdS coordinate map and state/operator interpretation of global AdS energy as CFT scaling dimension.
- States holographic generating-functional dictionary and supergraviton/chiral-primary correspondences.
- Summarizes massive-string scaling at large coupling, folded-spinning-string large-spin twist asymptotics, and giant-graviton BPS/operator-dual structure.
- Develops Hawking-Page thermodynamic saddle analysis and strong-coupling thermal free-energy coefficient for `N=4` SYM.

## Candidate Formalization Units
- `D3DecouplingLimit`
- `AdSCFTParameterMap`
- `NFourSYMConformalPackage`
- `CoulombBranchVacuumPackage`
- `ProbeD3CoulombMatching`
- `PoincareGlobalCoordinateMap`
- `StateOperatorMapRelation`
- `AdSCFTDictionaryRelation`
- `SupergravitonChiralPrimaryPackage`
- `MassiveStringStrongCouplingScaling`
- `SpinningStringLargeSpinTwist`
- `GiantGravitonDualityPackage`
- `HawkingPageTransitionPackage`
- `NFourThermalStrongCouplingLimit`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringAdSCftD3DecouplingLimit`.
- Candidate new `AssumptionId`: `stringAdSCftParameterMap`.
- Candidate new `AssumptionId`: `stringAdSCftN4SymConformalPackage`.
- Candidate new `AssumptionId`: `stringAdSCftCoulombBranchVacuumPackage`.
- Candidate new `AssumptionId`: `stringAdSCftProbeD3CoulombMatching`.
- Candidate new `AssumptionId`: `stringAdSCftPoincareGlobalCoordinateMap`.
- Candidate new `AssumptionId`: `stringAdSCftStateOperatorMap`.
- Candidate new `AssumptionId`: `stringAdSCftDictionary`.
- Candidate new `AssumptionId`: `stringAdSCftSupergravitonChiralPrimaries`.
- Candidate new `AssumptionId`: `stringAdSCftMassiveStringScaling`.
- Candidate new `AssumptionId`: `stringAdSCftSpinningStringTwist`.
- Candidate new `AssumptionId`: `stringAdSCftGiantGravitonDuality`.
- Candidate new `AssumptionId`: `stringAdSCftHawkingPageTransition`.
- Candidate new `AssumptionId`: `stringAdSCftThermalStrongCoupling`.

## Subsections
- [x] 20.1 The decoupling limit of the black $p$-brane (p.458)
- [x] 20.2 ${\cal N}=4$ SYM as a superconformal field theory (p.460)
- [x] 20.3 Vacuum configurations (p.464)
- [x] 20.4 From Poincar\'e to global AdS (p.467)
- [x] 20.5 Holographic correlators (p.470)
- [x] 20.6 Supergraviton states (p.471)
- [x] 20.7 Massive string states (p.474)
- [x] 20.8 Giant gravitons (p.476)
- [x] 20.9 Black holes in AdS and thermodynamics (p.479)

## Subsubsections
- (none listed in TOC)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
