# Bell's Theorem in Lean 4

This document is a mathematical exposition of the content formalized in `Bell_clean.lean`.

## Setup

A local hidden variable theory (LHVT) is defined by a finite set Λ, a probability distribution ρ on Λ (nonneg, sums to 1), and two deterministic outcome functions A, B : ℝ × Λ → {+1, −1}. Locality is structural: A takes only Alice's detector angle and λ, B takes only Bob's detector angle and λ. The predicted correlation is

    E(a, b) = Σ_λ ρ(λ) A(a,λ) B(b,λ).

The CHSH parameter for a correlation E at settings a, a′, b, b′ is

    S = E(a,b) + E(a,b′) + E(a′,b) − E(a′,b′).

## CHSH inequality (proven)

For any LHVT and any choice of settings, |S| ≤ 2.

The proof factors S as Σ_λ ρ(λ) f(λ) where f(λ) is the CHSH combination of the four products A(·,λ)B(·,λ). A case analysis over all 16 assignments of ±1 values shows |f(λ)| ≤ 2. The result then follows by the triangle inequality, nonnegativity of ρ, and normalization Σρ = 1.

## Quantum prediction (proven)

Define the singlet correlation E_QM(a,b) = −cos(a − b). This is bounded in [−1, 1].

At the settings a = 0, a′ = −π/2, b = 3π/4, b′ = −3π/4, the CHSH parameter evaluates to S_QM = 2√2. The computation reduces each of the four terms to ±√2/2 via the identities cos(π − x) = −cos x, cos(x + π) = −cos x, cos(−x) = cos x, and cos(π/4) = √2/2. Since √2 > 1, we get S_QM = 2√2 > 2.

## Bell's theorem (proven)

No LHVT reproduces E_QM. That is,

    ¬∃ LHVT, ∀ a b, E_LHVT(a,b) = −cos(a − b).

Proof: if such a theory existed, the CHSH inequality would give |S| ≤ 2 for its correlation, but since its correlation equals −cos(a − b) at all settings, this would force |S_QM| ≤ 2, contradicting S_QM > 2.

## Connection to quantum mechanics (axiomatized)

The file also defines the singlet density operator from the quantum library and states two further results that depend on the unproven lemma `singlet_pauli_correlation`:

1. The function −cos(a − b) equals the expectation value ⟨ψ⁻|(n̂(a) ⊗ n̂(b))|ψ⁻⟩ where n̂(φ) = cos φ σₓ + sin φ σᵧ is the spin observable at angle φ in the xy-plane and |ψ⁻⟩ is the singlet state.

2. Combining this identification with Bell's theorem: no LHVT reproduces the quantum mechanical expectation values for spin measurements on the singlet state.

The proofs of both statements are structurally complete — (2) reduces to Bell's theorem via (1), and (1) reduces to `singlet_pauli_correlation` — but the chain passes through an unproven sorry, so these are axiomatized rather than fully verified.

## What is and isn't proven

The core mathematical content — the CHSH inequality, the computation S_QM = 2√2 > 2, and the impossibility theorem — is fully machine-checked with no axioms beyond Lean's type theory and Mathlib. The only unverified claim is the identification of −cos(a − b) as the quantum expectation value for the singlet state, which bridges the abstract Hilbert space formalism to the concrete trigonometric function.
