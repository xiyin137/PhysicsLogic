# Section 25: Holographic Wilson lines and confinement

- Status: initial extraction complete
- Source page start: 604
- Source files: `references/stringbook/string notes.tex`, `references/stringbook/string notes.pdf`, `references/stringbook/stringrefs.bib`
- Draft Lean target: `PhysicsLogic/StringTheory/WilsonLinesConfinement.lean`

## Reading Summary
- The section combines three physics lanes: Wilson-line observables in AdS/CFT,
  holographic QCD confinement models (Witten and Sakai-Sugimoto), and conifold
  gauge/gravity systems (Klebanov-Witten/Tseytlin/Strassler).
- For Maldacena-Wilson loops, strong-coupling expectation values are governed by
  regulated Nambu-Goto saddles; rectangular loops give
  `V(L) = -4π√λ/(Γ(1/4)^4 L)`.
- Cuspy lines connect to universal cusp data:
  `Δ_cusp(π-iC) -> (1/2) Γ_cusp C`, and at strong coupling
  `Δ_cusp(π-iC) ~ (√λ/(4π)) C`.
- Small-angle cusps define the bremsstrahlung function:
  `Δ_cusp(α) = -B α^2 + O(α^4)` and `A = 2π B`, with planar localization
  `B(λ,N) = (√λ/(4π^2)) I_2(√λ)/I_1(√λ) + O(N^-2)`.
- Witten’s D4-circle model gives a confining linear potential and explicit
  tension formulas in terms of `M_KK`, `g_4`, and geometric parameters.
- Sakai-Sugimoto adds flavor D8-branes, realizes chiral symmetry breaking via
  D8-anti-D8 connection, yields Skyrme-type pion action, captures `U(1)_A`
  anomaly with nonzero `η'` mass, and predicts scalar/vector meson scales.
- The conifold subsectors include KW SCFT and AdS5xT11 duality, KT logarithmic
  effective-rank running and cascade interpretation, and KS warped-deformed
  conifold resolution with confinement scale relations.

## Candidate Formalization Units
- `MaldacenaWilsonLoopSaddlePackage`
- `RectangularWilsonPotentialPackage`
- `CuspLargeAnglePackage`
- `BremsstrahlungFunctionPackage`
- `WittenCompactificationPackage`
- `WittenConfiningStringPackage`
- `D8HolonomyChiralPackage`
- `SakaiSugimotoPionActionPackage`
- `SakaiSugimotoEtaPrimeMassPackage`
- `SakaiSugimotoMesonSpectrumPackage`
- `KlebanovWittenConifoldPackage`
- `KlebanovWittenAdSDualPackage`
- `KlebanovTseytlinRunningPackage`
- `CascadeSeibergDualStepPackage`
- `KlebanovStrasslerConfinementPackage`

## Assumption Candidates
- Candidate new `AssumptionId`: `stringWilsonMaldacenaLoopSaddle`.
- Candidate new `AssumptionId`: `stringWilsonQuarkAntiquarkPotentialStrongCoupling`.
- Candidate new `AssumptionId`: `stringWilsonCuspLargeAngleRelation`.
- Candidate new `AssumptionId`: `stringWilsonBremsstrahlungFunction`.
- Candidate new `AssumptionId`: `stringWittenConfinementCircleData`.
- Candidate new `AssumptionId`: `stringWittenConfiningStringTension`.
- Candidate new `AssumptionId`: `stringSakaiSugimotoChiralSymmetryBreaking`.
- Candidate new `AssumptionId`: `stringSakaiSugimotoPionSkyrmeAction`.
- Candidate new `AssumptionId`: `stringSakaiSugimotoEtaPrimeMass`.
- Candidate new `AssumptionId`: `stringSakaiSugimotoMesonSpectrum`.
- Candidate new `AssumptionId`: `stringKlebanovWittenMarginalConifoldData`.
- Candidate new `AssumptionId`: `stringKlebanovWittenAdS5T11Duality`.
- Candidate new `AssumptionId`: `stringKlebanovTseytlinFluxRunning`.
- Candidate new `AssumptionId`: `stringKlebanovCascadeSeibergDualStep`.
- Candidate new `AssumptionId`: `stringKlebanovStrasslerConfinement`.

## Subsections
- [x] 25.1 Maldacena-Wilson lines in ${\cal N}=4$ SYM (p.604)
- [x] 25.2 Cuspy Wilson lines (p.605)
- [x] 25.3 Bremsstrahlung (p.608)
- [x] 25.4 Witten's model of holographic confinement (p.610)
- [x] 25.5 Sakai-Sugimoto model of holographic QCD (p.613)
- [x] 25.6 Klebanov-Witten theory (p.620)
- [x] 25.7 Holographic RG cascade (p.627)

## Subsubsections
- [x] 25.5.1 Chiral symmetry breaking (p.615)
- [x] 25.5.2 $U(1)_A$ anomaly and $\eta '$ meson (p.617)
- [x] 25.5.3 Hadron spectrum (p.619)
- [x] 25.6.1 D3-branes on the conifold (p.621)
- [x] 25.6.2 The holographic dual (p.624)
- [x] 25.6.3 From $S^5/\mathbb {Z}_2$ to $T^{1,1}$ (p.626)
- [x] 25.7.1 Fractional D3-branes (p.627)
- [x] 25.7.2 The RG cascade (p.630)
- [x] 25.7.3 The warped deformed conifold (p.633)

## Extraction Checklist
- [x] Definitions and notation captured
- [x] Main claims and equations extracted
- [x] Dependency chain to prior sections identified
- [x] Candidate Lean declarations drafted
- [x] Assumptions mapped to `PhysicsLogic/Assumptions.lean`
