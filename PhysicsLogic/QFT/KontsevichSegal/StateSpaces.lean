import PhysicsLogic.QFT.KontsevichSegal.Bordisms
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.QFT.KontsevichSegal

set_option linter.unusedVariables false

/- ============= FRÉCHET SPACES (NOT HILBERT!) ============= -/

/-- KS: State space on (d-1)-manifold is Fréchet space (NOT Hilbert!)
    Key difference from Atiyah-Segal: Path integral naturally gives Fréchet spaces
    versus Hilbert spaces in operator formalism -/
structure KS_StateSpace (d : ℕ) (bt : BordismTheory (d-1)) (Sig : bt.Bordism) where
  carrier : Type _
  add : carrier → carrier → carrier
  smul : ℂ → carrier → carrier
  zero : carrier
  /-- Fréchet topology: countable family of seminorms -/
  seminorms : ℕ → (carrier → ℝ)
  /-- Each seminorm is non-negative -/
  seminorm_nonneg : ∀ (n : ℕ) (ψ : carrier), seminorms n ψ ≥ 0
  /-- Seminorm of zero is zero -/
  seminorm_zero : ∀ (n : ℕ), seminorms n zero = 0
  /-- Completeness: every Cauchy sequence (in all seminorms) has a limit -/
  complete : ∀ (seq : ℕ → carrier),
    (∀ n ε, ε > 0 → ∃ N, ∀ i j, i ≥ N → j ≥ N →
      seminorms n (add (seq i) (smul (-1 : ℂ) (seq j))) < ε) →
    ∃ (lim : carrier), ∀ n ε, ε > 0 → ∃ N, ∀ i, i ≥ N →
      seminorms n (add (seq i) (smul (-1 : ℂ) lim)) < ε
  -- Local convexity is automatic for a topology defined by seminorms.

/-- Structure for state space operations -/
structure KS_StateSpaceOps (d : ℕ) (bt : BordismTheory (d-1)) where
  /-- Empty manifold gives ground field ℂ -/
  emptySpace : KS_StateSpace d bt bt.emptyBordism
  /-- The carrier of empty space is ℂ -/
  empty_is_C : emptySpace.carrier = ℂ
  /-- Monoidal structure (completed projective tensor product) -/
  tensor : (Sig₁ Sig₂ : bt.Bordism) →
    KS_StateSpace d bt Sig₁ → KS_StateSpace d bt Sig₂ →
    KS_StateSpace d bt (bt.disjointUnion Sig₁ Sig₂)
  -- Tensor product is associative up to natural isomorphism.
  -- Stating this precisely requires an isomorphism between the carrier types
  -- of tensor(tensor(V₁,V₂),V₃) and tensor(V₁,tensor(V₂,V₃)), which depends
  -- on the associativity of the bordism disjoint union.
  /-- Duality (continuous dual space) -/
  dual : (Sig : bt.Bordism) → KS_StateSpace d bt Sig →
    KS_StateSpace d bt (bt.reverseOrientation Sig)
  -- Dual of dual is naturally isomorphic to original (V ≅ V**).
  -- Stating this requires reverseOrientation to be an involution on Bordism.
  /-- Pairing for gluing (continuous bilinear map) -/
  pairing : (Sig : bt.Bordism) →
    (V : KS_StateSpace d bt Sig) →
    (V_dual : KS_StateSpace d bt (bt.reverseOrientation Sig)) →
    V.carrier → V_dual.carrier → ℂ
  /-- Pairing is non-degenerate -/
  pairing_nondegenerate : ∀ (Sig : bt.Bordism)
    (V : KS_StateSpace d bt Sig)
    (V_dual : KS_StateSpace d bt (bt.reverseOrientation Sig))
    (ψ : V.carrier),
    (∀ φ : V_dual.carrier, pairing Sig V V_dual ψ φ = 0) → ψ = V.zero
  -- Symmetric monoidal structure (V₁ ⊗ V₂ ≅ V₂ ⊗ V₁) requires
  -- commutativity of bordism disjoint union to state precisely.

end PhysicsLogic.QFT.KontsevichSegal
