import PhysicsLogic.QFT.Wightman.Axioms
import PhysicsLogic.QFT.Wightman.WightmanFunctions
import PhysicsLogic.Assumptions

namespace PhysicsLogic.QFT.Wightman

open SpaceTime Quantum

/-- PCT theorem (Pauli-Lüders theorem): Every Lorentz-invariant QFT admits an
    antiunitary PCT operator Θ such that the Wightman functions satisfy:
    W_n(-xₙ,...,-x₁) = conj(W_n(x₁,...,xₙ))

    The key features are:
    - Point negation (from P and T combined)
    - Reversal of operator ordering (from T)
    - Complex conjugation (from the anti-unitary nature of Θ)

    P = parity (x⃗ → -x⃗), C = charge conjugation (particle ↔ antiparticle),
    T = time reversal (t → -t).

    This is a THEOREM (provable from W1-W4), not an axiom itself. -/
theorem pct_theorem {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (qft : WightmanQFT H d)
  (phi : FieldDistribution H d)
  (n : ℕ) (hn : n > 0) (points : Fin n → (Fin d → ℝ))
  (h_phys :
    PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.wightmanPctTheorem
      (qft.wft.wightmanFunction phi n
        (fun i μ => -points (⟨n - 1 - i.val, by omega⟩) μ) =
      (starRingEnd ℂ) (qft.wft.wightmanFunction phi n points))) :
  -- PCT: W_n(-xₙ,...,-x₁) = conj(W_n(x₁,...,xₙ))
  qft.wft.wightmanFunction phi n
    (fun i μ => -points (⟨n - 1 - i.val, by omega⟩) μ) =
  (starRingEnd ℂ) (qft.wft.wightmanFunction phi n points) := by
  exact h_phys

/-- Spin-statistics theorem: In a Wightman QFT, fields of integer spin must
    satisfy Bose commutation relations (commute) at spacelike separation,
    while fields of half-integer spin must satisfy Fermi anticommutation
    relations (anticommute) at spacelike separation.

    Integer spin (s ∈ ℤ): [φ(f), φ(g)] = 0 for spacelike-separated supports
    Half-integer spin (s ∈ ℤ + 1/2): {φ(f), φ(g)} = 0 for spacelike-separated supports

    This is a deep consequence of Lorentz covariance + locality + spectrum condition.

    This is a THEOREM (provable from W1-W3), not an axiom itself. -/
theorem spin_statistics {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (qft : WightmanQFT H d)
  (phi : SmearedFieldOperator H d)
  (spin : ℚ)  -- Spin as rational number (0, 1/2, 1, 3/2, ...)
  (h_nonneg : spin ≥ 0)
  (f g : SchwartzFunction d)
  (h_spacelike : spacelikeSeparated (qft.supportOps.testFunctionSupport f)
                                    (qft.supportOps.testFunctionSupport g))
  (h_phys :
    PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.wightmanSpinStatistics
      ((spin.den = 1 →
        ∀ state ∈ qft.locality.domain,
          qft.ops.smear phi f (qft.ops.smear phi g state) =
          qft.ops.smear phi g (qft.ops.smear phi f state)) ∧
      (spin.den = 2 →
        ∀ state ∈ qft.locality.domain,
          qft.ops.smear phi f (qft.ops.smear phi g state) =
          -(qft.ops.smear phi g (qft.ops.smear phi f state))))) :
  -- Integer spin → bosonic commutation at spacelike separation
  (spin.den = 1 →
    ∀ state ∈ qft.locality.domain,
      qft.ops.smear phi f (qft.ops.smear phi g state) =
      qft.ops.smear phi g (qft.ops.smear phi f state)) ∧
  -- Half-integer spin → fermionic anticommutation at spacelike separation
  (spin.den = 2 →
    ∀ state ∈ qft.locality.domain,
      qft.ops.smear phi f (qft.ops.smear phi g state) =
      -(qft.ops.smear phi g (qft.ops.smear phi f state))) := by
  exact h_phys

/-- Haag's theorem: In relativistic QFT, the free and interacting field theories
    cannot be unitarily equivalent in a way that preserves both the vacuum and
    the field operator correlations.

    More precisely: if the free and interacting theories have distinct Wightman
    functions, there is no unitary map V : H_free → H_int that simultaneously:
    (1) preserves inner products (is unitary)
    (2) maps the free vacuum to the interacting vacuum
    (3) makes the Wightman functions agree

    This is why naive interaction-picture perturbation theory is formal:
    the free and interacting Hilbert spaces are unitarily inequivalent.

    This is a THEOREM (provable from W1-W4), not an axiom itself. -/
theorem haag_theorem {H_free H_int : Type _}
  [QuantumStateSpace H_free] [QuantumStateSpace H_int] {d : ℕ} [NeZero d]
  (qft_free : WightmanQFT H_free d)
  (qft_int : WightmanQFT H_int d)
  (phi_free : FieldDistribution H_free d)
  (phi_int : FieldDistribution H_int d)
  (h_distinct : qft_free.wft.wightmanFunction phi_free ≠
                qft_int.wft.wightmanFunction phi_int)
  (h_phys :
    PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.wightmanHaagTheorem
      (¬∃ (V : H_free → H_int),
        (∀ ψ φ : H_free, innerProduct (V ψ) (V φ) = innerProduct ψ φ) ∧
        V qft_free.vacuumFieldOps.vacuum = qft_int.vacuumFieldOps.vacuum ∧
        (∀ (n : ℕ) (points : Fin n → (Fin d → ℝ)),
          qft_free.wft.wightmanFunction phi_free n points =
          qft_int.wft.wightmanFunction phi_int n points))) :
  ¬∃ (V : H_free → H_int),
    -- V is unitary (inner product preserving)
    (∀ ψ φ : H_free, innerProduct (V ψ) (V φ) = innerProduct ψ φ) ∧
    -- V maps free vacuum to interacting vacuum
    V qft_free.vacuumFieldOps.vacuum = qft_int.vacuumFieldOps.vacuum ∧
    -- V intertwines the Wightman functions (makes them agree)
    (∀ (n : ℕ) (points : Fin n → (Fin d → ℝ)),
      qft_free.wft.wightmanFunction phi_free n points =
      qft_int.wft.wightmanFunction phi_int n points) := by
  exact h_phys

end PhysicsLogic.QFT.Wightman
