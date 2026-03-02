import PhysicsLogic.QFT.Wightman.WightmanFunctions
import PhysicsLogic.Assumptions
import PhysicsLogic.SpaceTime.Causality
import PhysicsLogic.SpaceTime.Metrics
import PhysicsLogic.SpaceTime.Minkowski

namespace PhysicsLogic.QFT.Wightman

open SpaceTime Quantum

/-- Momentum lies in forward lightcone: p⁰ ≥ 0 and p² = (p⁰)² - |p⃗|² ≥ 0 -/
def inForwardLightcone {d : ℕ} [NeZero d] (p : Fin d → ℝ) : Prop :=
  p 0 ≥ 0 ∧ (p 0)^2 ≥ ∑ i : Fin d, if i = 0 then 0 else (p i)^2

/-- Momentum is on mass shell: (p⁰)² - |p⃗|² = m² -/
def onMassShell {d : ℕ} [NeZero d] (p : Fin d → ℝ) (m : ℝ) : Prop :=
  (p 0)^2 - (∑ i : Fin d, if i = 0 then 0 else (p i)^2) = m^2

/-- On-shell condition: a momentum p is on shell for mass m if E² - |p⃗|² = m².
    This is a DEFINITION of what "on-shell" means, not a claim about all momenta. -/
def isOnShell {d : ℕ} [NeZero d] (p : Fin d → ℝ) (m : ℝ) : Prop :=
  onMassShell p m ∧ p 0 ≥ 0

/-- Two regions are spacelike separated: for all x in R₁, y in R₂, (x-y)² < 0 (spacelike) -/
def spacelikeSeparated {d : ℕ} [NeZero d] (R₁ R₂ : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ R₁, ∀ y ∈ R₂,
    (x 0 - y 0)^2 < ∑ i : Fin d, if i = 0 then 0 else (x i - y i)^2

/-- Structure for test function support operations -/
structure TestFunctionSupportOps (d : ℕ) where
  /-- Test function support is contained in a region -/
  testFunctionSupport : SchwartzFunction d → Set (Fin d → ℝ)

/-- Shared dimension-generic Poincaré transformation alias. -/
abbrev PoincareTransformGen := SpaceTime.PoincareTransformGen

/-- Shared proper-orthochronous Lorentz marker alias. -/
abbrev RestrictedLorentzTransformGen := SpaceTime.RestrictedLorentzTransformGen

/-- Wightman Axiom W1: Relativistic covariance (Poincaré invariance).
    The Wightman functions are Poincaré invariant:
    W_n(Λx₁+a,...,Λxₙ+a) = W_n(x₁,...,xₙ)

    The existence of the unitary representation U(Λ,a) implementing this symmetry
    is part of the vacuum axiom (W4), which provides a specific Poincaré representation.
    Here we state the consequence for Wightman functions directly. -/
structure RelativisticCovariance (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d]
    (wft : WightmanFunctionTheory H d) where
  /-- Wightman functions are Poincaré invariant -/
  relativistic_covariance : ∀ (phi : FieldDistribution H d)
    (Lambda : LorentzTransformGen d) (a : Fin d → ℝ),
    ∀ (n : ℕ) (points : Fin n → (Fin d → ℝ)),
      wft.wightmanFunction phi n (fun i μ => ∑ ν, Lambda.matrix μ ν * points i ν + a μ) =
      wft.wightmanFunction phi n points

/-- Covariance phrased on bundled Poincaré elements `(Λ,a)`. -/
theorem RelativisticCovariance.poincare_covariance
    {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
    {wft : WightmanFunctionTheory H d}
    (h_cov : RelativisticCovariance H d wft)
    (phi : FieldDistribution H d)
    (g : PoincareTransformGen d)
    (n : ℕ)
    (points : Fin n → (Fin d → ℝ)) :
    wft.wightmanFunction phi n (fun i => g.apply (points i)) =
    wft.wightmanFunction phi n points := by
  have h_cov_raw :
      wft.wightmanFunction phi n
        (fun i μ => ∑ ν, g.lorentz.matrix μ ν * points i ν + g.translation μ) =
      wft.wightmanFunction phi n points :=
    h_cov.relativistic_covariance phi g.lorentz g.translation n points
  have h_rewrite :
      wft.wightmanFunction phi n (fun i => g.apply (points i)) =
      wft.wightmanFunction phi n
        (fun i μ => ∑ ν, g.lorentz.matrix μ ν * points i ν + g.translation μ) := by
    rfl
  exact h_rewrite.trans h_cov_raw

/-- W1 covariance restricted to proper-orthochronous Lorentz transformations.
This matches the standard physical statement before adding discrete symmetries. -/
structure RestrictedRelativisticCovariance
    (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d]
    (wft : WightmanFunctionTheory H d) where
  relativistic_covariance : ∀ (phi : FieldDistribution H d)
    (Lambda : RestrictedLorentzTransformGen d) (a : Fin d → ℝ),
    ∀ (n : ℕ) (points : Fin n → (Fin d → ℝ)),
      wft.wightmanFunction phi n
        (fun i μ => ∑ ν, Lambda.toLorentz.matrix μ ν * points i ν + a μ) =
      wft.wightmanFunction phi n points

/-- Full Lorentz covariance implies the restricted proper-orthochronous version. -/
def restricted_relativistic_covariance_of_relativistic_covariance
    {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
    {wft : WightmanFunctionTheory H d}
    (h_cov : RelativisticCovariance H d wft) :
    RestrictedRelativisticCovariance H d wft := by
  refine
    { relativistic_covariance := ?_ }
  intro phi Lambda a n points
  exact h_cov.relativistic_covariance phi Lambda.toLorentz a n points

/-- Appendix-D local-field Poincaré-covariance interface.
This records an explicit point action together with covariance of Wightman
functions under that action. -/
structure LocalFieldPoincareCovariance
    (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d]
    (wft : WightmanFunctionTheory H d) where
  poincarePointAction :
    LorentzTransformGen d → (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)
  action_formula : ∀ (Lambda : LorentzTransformGen d)
    (a x : Fin d → ℝ) (μ : Fin d),
    poincarePointAction Lambda a x μ = ∑ ν, Lambda.matrix μ ν * x ν + a μ
  covariance : ∀ (phi : FieldDistribution H d)
    (Lambda : LorentzTransformGen d) (a : Fin d → ℝ),
    ∀ (n : ℕ) (points : Fin n → (Fin d → ℝ)),
      wft.wightmanFunction phi n (fun i => poincarePointAction Lambda a (points i)) =
      wft.wightmanFunction phi n points

/-- Repackage local-field covariance on bundled Poincaré elements `(Λ,a)`. -/
theorem LocalFieldPoincareCovariance.poincare_covariance
    {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
    {wft : WightmanFunctionTheory H d}
    (h_cov : LocalFieldPoincareCovariance H d wft)
    (phi : FieldDistribution H d)
    (g : PoincareTransformGen d)
    (n : ℕ)
    (points : Fin n → (Fin d → ℝ)) :
    wft.wightmanFunction phi n
      (fun i => h_cov.poincarePointAction g.lorentz g.translation (points i)) =
    wft.wightmanFunction phi n points := by
  exact h_cov.covariance phi g.lorentz g.translation n points

/-- Build the Appendix-D local-field Poincaré-covariance interface from the
core relativistic-covariance axiom. -/
def local_field_poincare_covariance_of_relativistic_covariance
    {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
    {wft : WightmanFunctionTheory H d}
    (h_cov : RelativisticCovariance H d wft) :
    LocalFieldPoincareCovariance H d wft := by
  refine
    { poincarePointAction := fun Lambda a x μ => ∑ ν, Lambda.matrix μ ν * x ν + a μ
      action_formula := ?_
      covariance := ?_ }
  · intro Lambda a x μ
    rfl
  · intro phi Lambda a n points
    exact h_cov.relativistic_covariance phi Lambda a n points

/-- Wightman Axiom W2: Spectrum condition (positivity of energy-momentum).
    The joint spectrum of the energy-momentum operators (P⁰, P¹,...) lies in the
    closed forward lightcone V⁺ = {p | p⁰ ≥ 0, p² ≥ 0} where p² = (p⁰)² - ∑ᵢ(pⁱ)².

    Physical meaning: energy is bounded from below (stable vacuum). -/
structure SpectrumCondition (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d] where
  /-- The spectrum of the energy-momentum operators -/
  spectrum : Set (Fin d → ℝ)
  /-- All momenta in forward cone -/
  in_forward_cone : ∀ p ∈ spectrum, inForwardLightcone p
  /-- Vacuum has zero momentum -/
  vacuum_zero_momentum : (fun _ => 0) ∈ spectrum

/-- Wightman Axiom W3: Locality (microcausality).
    For smeared field operators with spacelike separated supports:
    [φ(f), ψ(g)] = 0 when supp(f) and supp(g) are spacelike separated.

    This is the mathematical expression of Einstein causality: measurements at
    spacelike separation cannot influence each other.

    The commutator relation holds on a dense invariant domain D ⊂ H, since
    field operators are generally unbounded. -/
structure Locality (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d]
    (ops : FieldOperatorOps H d) (supportOps : TestFunctionSupportOps d) where
  /-- The dense domain on which field operators are well-defined -/
  domain : Set H
  /-- Domain is nonempty -/
  domain_nonempty : domain.Nonempty
  /-- Fields at spacelike separation commute on the domain -/
  locality : ∀ (phi psi : SmearedFieldOperator H d)
    (f g : SchwartzFunction d)
    (_h_spacelike : spacelikeSeparated (supportOps.testFunctionSupport f)
                                      (supportOps.testFunctionSupport g))
    (state : H) (_h_domain : state ∈ domain),
    ops.smear phi f (ops.smear psi g state) =
    ops.smear psi g (ops.smear phi f state)

/-- Appendix-D microcausality commutator interface:
spacelike-separated smeared fields commute on a specified dense domain. -/
structure MicrocausalityCommutator
    (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d]
    (ops : FieldOperatorOps H d) (supportOps : TestFunctionSupportOps d) where
  domain : Set H
  domain_nonempty : domain.Nonempty
  commutator_vanishes : ∀ (phi psi : SmearedFieldOperator H d)
    (f g : SchwartzFunction d)
    (_h_spacelike : spacelikeSeparated (supportOps.testFunctionSupport f)
                                      (supportOps.testFunctionSupport g))
    (state : H) (_h_domain : state ∈ domain),
    ops.smear phi f (ops.smear psi g state) =
    ops.smear psi g (ops.smear phi f state)

/-- Build the Appendix-D microcausality commutator interface from the core
locality axiom. -/
def microcausality_commutator_of_locality
    {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
    {ops : FieldOperatorOps H d} {supportOps : TestFunctionSupportOps d}
    (h_loc : Locality H d ops supportOps) :
    MicrocausalityCommutator H d ops supportOps := by
  exact
    { domain := h_loc.domain
      domain_nonempty := h_loc.domain_nonempty
      commutator_vanishes := h_loc.locality }

/-- Structure for applying fields to vacuum -/
structure VacuumFieldOps (H : Type _) [QuantumStateSpace H] (d : ℕ) where
  /-- The vacuum state -/
  vacuum : H
  /-- Apply a sequence of smeared field operators to the vacuum:
      φ(f₁) φ(f₂) ... φ(fₙ) |0⟩ -/
  applyFieldsToVacuum : SmearedFieldOperator H d → (n : ℕ) → (Fin n → SchwartzFunction d) → H

/-- Wightman Axiom W4: Vacuum properties.
    - There is a unitary representation of the Poincaré group
    - |0⟩ is invariant under this representation
    - |0⟩ is the unique time-translation-invariant state (up to phase)
    - {φ(f₁)...φ(fₙ)|0⟩ : n ∈ ℕ, fᵢ ∈ S(ℝᵈ)} is dense in H

    This ensures the vacuum is the "ground state" and that all states can be
    created by applying field operators to the vacuum. -/
structure VacuumPropertiesAxiom (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d]
    (vfo : VacuumFieldOps H d) where
  /-- The Poincaré representation: a specific family of unitaries implementing
      the Poincaré symmetry, parameterized by (Lorentz transform, translation). -/
  poincareUnitary : LorentzTransformGen d → (Fin d → ℝ) → Quantum.UnitaryOp H
  /-- Vacuum is normalized -/
  vacuum_normalized : ‖vfo.vacuum‖ = 1
  /-- Vacuum is invariant under the Poincaré representation -/
  vacuum_poincare_invariant : ∀ (Λ : LorentzTransformGen d) (a : Fin d → ℝ),
    (poincareUnitary Λ a).op vfo.vacuum = vfo.vacuum
  /-- Uniqueness: any time-translation-invariant state is proportional to the vacuum.
      This ensures the vacuum is unique up to a phase. -/
  vacuum_unique : ∀ (ψ : H),
    (∀ (t : ℝ), (poincareUnitary (LorentzTransformGen.id d)
      (fun μ => if μ = 0 then t else 0)).op ψ = ψ) →
    ∃ (c : ℂ), ψ = c • vfo.vacuum
  /-- Cyclicity: there exists a field whose polynomial algebra on vacuum is dense in H.
      The span of {φ(f₁)...φ(fₙ)|0⟩ : n ∈ ℕ, fᵢ ∈ S(ℝᵈ)} is dense in H. -/
  vacuum_cyclicity : ∃ (phi : SmearedFieldOperator H d),
    ∀ (state : H) (ε : ℝ), ε > 0 →
    ∃ (n : ℕ) (test_funcs : Fin n → SchwartzFunction d),
      ‖state - vfo.applyFieldsToVacuum phi n test_funcs‖ < ε

/-- Complete Wightman QFT structure combining all axioms -/
structure WightmanQFT (H : Type _) [QuantumStateSpace H] (d : ℕ) [NeZero d] where
  /-- Wightman function theory -/
  wft : WightmanFunctionTheory H d
  /-- Field operator operations -/
  ops : FieldOperatorOps H d
  /-- Test function support operations -/
  supportOps : TestFunctionSupportOps d
  /-- Vacuum field operations -/
  vacuumFieldOps : VacuumFieldOps H d
  /-- Distribution to smeared operations -/
  distOps : DistributionToSmearedOps H d
  /-- W1: Relativistic covariance -/
  covariance : RelativisticCovariance H d wft
  /-- W2: Spectrum condition -/
  spectrum : SpectrumCondition H d
  /-- W3: Locality -/
  locality : Locality H d ops supportOps
  /-- W4: Vacuum properties (includes Poincaré representation) -/
  vacuumProps : VacuumPropertiesAxiom H d vacuumFieldOps
  /-- Wightman positivity -/
  positivity : WightmanPositivity H d wft
  /-- Cluster decomposition -/
  cluster : ClusterDecomposition H d wft

/-- Reeh-Schlieder theorem: vacuum is cyclic and separating for local algebras.
    For any bounded region O, the set {φ(f)|0⟩ | supp(f) ⊂ O} is dense in H.

    Remarkable consequence: local measurements can distinguish any two states!

    This is a THEOREM (provable from W1-W4), not an axiom itself. -/
theorem reeh_schlieder {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (qft : WightmanQFT H d)
  (phi : SmearedFieldOperator H d)
  (O : Set (Fin d → ℝ))
  (_h_bounded : ∃ R : ℝ, ∀ x ∈ O, ‖x‖ < R)
  (_h_nonempty : O.Nonempty)
  (h_phys : PhysicsAssumption AssumptionId.wightmanReehSchlieder
    (∀ (state : H) (ε : ℝ), ε > 0 →
      ∃ (n : ℕ) (test_funcs : Fin n → SchwartzFunction d),
        (∀ i, qft.supportOps.testFunctionSupport (test_funcs i) ⊆ O) ∧
        ‖state - qft.vacuumFieldOps.applyFieldsToVacuum phi n test_funcs‖ < ε)) :
  ∀ (state : H) (ε : ℝ), ε > 0 →
    ∃ (n : ℕ) (test_funcs : Fin n → SchwartzFunction d),
      (∀ i, qft.supportOps.testFunctionSupport (test_funcs i) ⊆ O) ∧
      ‖state - qft.vacuumFieldOps.applyFieldsToVacuum phi n test_funcs‖ < ε := by
  exact h_phys

/-- Temperedness: Wightman functions are tempered distributions.
    They satisfy polynomial growth bounds: |W_n(x)| ≤ C(1 + |x|)^N.

    This is automatic consequence of the spectrum condition (W2) and ensures that
    Fourier transforms (momentum space formulation) are well-defined.

    This is a THEOREM (provable from W2), not an axiom itself. -/
theorem temperedness {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (qft : WightmanQFT H d)
  (phi : FieldDistribution H d)
  (n : ℕ) :
  PhysicsAssumption AssumptionId.wightmanTemperedness
    (∃ (C N : ℝ), ∀ (points : Fin n → (Fin d → ℝ)),
      ‖qft.wft.wightmanFunction phi n points‖ ≤ C * (1 + ∑ i, ‖points i‖)^N) →
  ∃ (C N : ℝ), ∀ (points : Fin n → (Fin d → ℝ)),
    ‖qft.wft.wightmanFunction phi n points‖ ≤ C * (1 + ∑ i, ‖points i‖)^N := by
  intro h_phys
  exact h_phys

end PhysicsLogic.QFT.Wightman
