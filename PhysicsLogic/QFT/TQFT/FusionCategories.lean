-- PhysicsLogic/QFT/TQFT/FusionCategories.lean
-- Algebraic data for fusion categories, braided fusion categories,
-- ribbon categories, and modular tensor categories.
--
-- These structures are STANDALONE (import only Mathlib, no manifold/CS dependency)
-- and encode the algebraic axioms: fusion rules, F-symbols (pentagon),
-- R-symbols (hexagon), twist (ribbon), and S-matrix (modularity).
--
-- The multiplicity-free case is used throughout (all fusion multiplicities N^c_{ab} ∈ {0,1}).
-- This covers SU(2)_k, Z_n, Ising, Fibonacci, and all TQFTs relevant to
-- charge-4e topological superconductors.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace PhysicsLogic.QFT.TQFT

open BigOperators

set_option autoImplicit false

/- ============= FUSION CATEGORIES ============= -/

/-- Algebraic data of a (semisimple, spherical, multiplicity-free) fusion category
    with `n` simple objects indexed by `Fin n`, where index 0 is the vacuum/unit object.

    This encodes:
    - Fusion rules N^k_{ij} with unit, commutativity, and associativity
    - Charge conjugation (duals)
    - Quantum dimensions (Perron-Frobenius eigenvector)
    - F-symbols (6j-symbols / associator) with the pentagon equation

    The pentagon equation is the fundamental consistency condition ensuring
    that the two paths for re-associating (a ⊗ b) ⊗ c ⊗ d are equal. -/
structure FusionCategoryData (n : ℕ) (hn : n ≥ 1) where
  /- === Fusion rules === -/

  /-- Fusion multiplicities: N^k_{ij} = multiplicity of X_k in X_i ⊗ X_j.
      X_i ⊗ X_j = ⊕_k N^k_{ij} · X_k -/
  N : Fin n → Fin n → Fin n → ℕ

  /-- Fusion with the vacuum is trivial: X_0 ⊗ X_j = X_j -/
  N_unit_left : ∀ (j k : Fin n),
    N ⟨0, by omega⟩ j k = if j = k then 1 else 0

  /-- Fusion is commutative: N^k_{ij} = N^k_{ji} -/
  N_comm : ∀ (i j k : Fin n), N i j k = N j i k

  /-- Fusion is associative: Σ_m N^m_{ij} · N^l_{mk} = Σ_m N^m_{jk} · N^l_{im} -/
  N_assoc : ∀ (i j k l : Fin n),
    ∑ m : Fin n, N i j m * N m k l =
    ∑ m : Fin n, N j k m * N i m l

  /- === Duals (charge conjugation) === -/

  /-- Dual (conjugate) of each simple object: X_i* = X_{dual i} -/
  dual : Fin n → Fin n

  /-- Vacuum is self-dual -/
  dual_unit : dual ⟨0, by omega⟩ = ⟨0, by omega⟩

  /-- Double dual is identity: (X*)* = X -/
  dual_involution : ∀ (i : Fin n), dual (dual i) = i

  /-- X_i ⊗ X_i* contains the vacuum: N^0_{i, dual(i)} ≥ 1 -/
  N_dual : ∀ (i : Fin n), N i (dual i) ⟨0, by omega⟩ ≥ 1

  /- === Quantum dimensions === -/

  /-- Quantum dimension of each simple object -/
  qdim : Fin n → ℝ

  /-- Quantum dimensions are positive -/
  qdim_pos : ∀ (i : Fin n), qdim i > 0

  /-- Vacuum has dimension 1 -/
  qdim_unit : qdim ⟨0, by omega⟩ = 1

  /-- Dual has same dimension: d_{i*} = d_i -/
  qdim_dual : ∀ (i : Fin n), qdim (dual i) = qdim i

  /-- Fusion-dimension consistency: d_i · d_j = Σ_k N^k_{ij} · d_k -/
  fusion_qdim : ∀ (i j : Fin n),
    qdim i * qdim j = ∑ k : Fin n, (N i j k : ℝ) * qdim k

  /- === F-symbols (associator / 6j-symbols) === -/

  /-- F-symbols in the multiplicity-free case: [F^{abc}_d]_{ef} ∈ ℂ.

      These are the matrix entries of the associator isomorphism
      (X_a ⊗ X_b) ⊗ X_c → X_a ⊗ (X_b ⊗ X_c)
      restricted to the X_d fusion outcome.

      The indices e, f are intermediate channels:
      - e: intermediate in (a ⊗ b) ⊗ c grouping, i.e. a ⊗ b → e, then e ⊗ c → d
      - f: intermediate in a ⊗ (b ⊗ c) grouping, i.e. b ⊗ c → f, then a ⊗ f → d

      Nonzero only when all four fusion channels are compatible:
      N^e_{ab} ≥ 1, N^d_{ec} ≥ 1, N^f_{bc} ≥ 1, N^d_{af} ≥ 1. -/
  F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ

  /-- F-symbols vanish when fusion channels are incompatible -/
  F_support : ∀ (a b c d e f : Fin n),
    (N a b e = 0 ∨ N e c d = 0 ∨ N b c f = 0 ∨ N a f d = 0) →
    F a b c d e f = 0

  /-- Pentagon equation (Mac Lane coherence for the associator):

      For all a, b, c, d, e, f, k, l:
        Σ_g [F^{fcd}_e]_{gl} · [F^{abg}_e]_{fk}
        = Σ_h [F^{abc}_g]_{fh} · [F^{ahd}_e]_{gl} · [F^{bcd}_l]_{hk}

      This ensures that the two paths for re-associating
      ((a ⊗ b) ⊗ c) ⊗ d → a ⊗ (b ⊗ (c ⊗ d))
      give the same result. -/
  pentagon : ∀ (a b c d e f k l : Fin n),
    ∑ g : Fin n, F f c d e g l * F a b g e f k =
    ∑ h : Fin n, F a b c k f h * F a h d e k l * F b c d l h k

/- ============= BRAIDED FUSION CATEGORIES ============= -/

/-- A braided fusion category extends a fusion category with R-symbols
    (braiding eigenvalues) satisfying the hexagon equations.

    The braiding c_{a,b} : X_a ⊗ X_b → X_b ⊗ X_a is encoded by
    its eigenvalues R^{ab}_c in each fusion channel X_a ⊗ X_b → X_c. -/
structure BraidedFusionCategoryData (n : ℕ) (hn : n ≥ 1)
    extends FusionCategoryData n hn where
  /- === R-symbols (braiding) === -/

  /-- R-symbols: R^{ab}_c is the braiding eigenvalue in the channel a ⊗ b → c.
      The braiding isomorphism c_{a,b} restricted to the X_c summand
      acts as multiplication by R^{ab}_c. -/
  R : Fin n → Fin n → Fin n → ℂ

  /-- R-symbols vanish for incompatible channels -/
  R_support : ∀ (a b c : Fin n), N a b c = 0 → R a b c = 0

  /-- R-symbols are nonzero for compatible channels -/
  R_nonzero : ∀ (a b c : Fin n), N a b c ≥ 1 → R a b c ≠ 0

  /-- Hexagon equation I:
      R^{ac}_e · [F^{cab}_d]_{ef} · R^{bc}_f
      = Σ_g [F^{acb}_d]_{eg} · R^{(ab)c→gc}_d · [F^{abc}_d]_{gf}

      Concretely in the multiplicity-free case:
      R^{ac}_e · F^{cab}_{d,e,f} · R^{bc}_f = Σ_g F^{acb}_{d,e,g} · R^{gc}_d · F^{abc}_{d,g,f} -/
  hexagon_I : ∀ (a b c d e f : Fin n),
    R a c e * F c a b d e f * R b c f =
    ∑ g : Fin n, F a c b d e g * R g c d * F a b c d g f

  /-- Hexagon equation II (with inverse braiding):
      (R^{ca}_e)⁻¹ · F^{cab}_{d,e,f} · (R^{cb}_f)⁻¹
      = Σ_g F^{acb}_{d,e,g} · (R^{cg}_d)⁻¹ · F^{abc}_{d,g,f} -/
  hexagon_II : ∀ (a b c d e f : Fin n),
    (R c a e)⁻¹ * F c a b d e f * (R c b f)⁻¹ =
    ∑ g : Fin n, F a c b d e g * (R c g d)⁻¹ * F a b c d g f

/- ============= RIBBON CATEGORIES ============= -/

/-- A ribbon category extends a braided fusion category with a twist
    (topological spin) satisfying the ribbon axiom.

    The twist θ_i encodes the topological spin of anyon X_i:
    θ_i = e^{2πi·h_i} where h_i is the conformal weight mod integers.

    Physically: dragging an anyon around a full 2π rotation
    produces the phase θ_i. -/
structure RibbonCategoryData (n : ℕ) (hn : n ≥ 1)
    extends BraidedFusionCategoryData n hn where
  /- === Twist / topological spin === -/

  /-- Topological spin (twist) of each simple object -/
  theta : Fin n → ℂ

  /-- Vacuum has trivial twist: θ_0 = 1 -/
  theta_unit : theta ⟨0, by omega⟩ = 1

  /-- Twist is a phase: |θ_i|² = 1 -/
  theta_phase : ∀ (i : Fin n), Complex.normSq (theta i) = 1

  /-- Dual has same twist: θ_{i*} = θ_i -/
  theta_dual : ∀ (i : Fin n), theta (dual i) = theta i

  /-- Ribbon axiom (twist-braiding relation):
      In compatible channels (N^c_{ab} ≥ 1):
      θ_c = R^{ab}_c · R^{ba}_c · θ_a · θ_b

      This connects the twist to the double-braiding (monodromy). -/
  twist_braiding : ∀ (a b c : Fin n),
    N a b c ≥ 1 →
    theta c = R a b c * R b a c * theta a * theta b

/- ============= MODULAR TENSOR CATEGORIES ============= -/

/-- A modular tensor category (MTC) extends a ribbon category with
    a non-degenerate S-matrix satisfying the Verlinde formula.

    The S-matrix encodes the mutual braiding statistics of anyons:
    S_{ij} is the normalized trace of the double braiding of X_i around X_j.

    Non-degeneracy (modularity) means: the only transparent object
    (one that braids trivially with everything) is the vacuum. -/
structure ModularCategoryData (n : ℕ) (hn : n ≥ 1)
    extends RibbonCategoryData n hn where
  /- === S-matrix === -/

  /-- Modular S-matrix: S_{ij} -/
  S : Fin n → Fin n → ℂ

  /-- S-matrix is symmetric: S_{ij} = S_{ji} -/
  S_symm : ∀ (i j : Fin n), S i j = S j i

  /-- S-matrix first row gives quantum dimensions: S_{0,i} = S_{0,0} · d_i -/
  S_qdim : ∀ (i : Fin n),
    S ⟨0, by omega⟩ i =
    S ⟨0, by omega⟩ ⟨0, by omega⟩ * (↑(qdim i) : ℂ)

  /-- S_{0,0} is real and positive (= 1/D where D is the total quantum dimension) -/
  S_00_pos : (S ⟨0, by omega⟩ ⟨0, by omega⟩).re > 0

  /-- S-matrix is unitary: Σ_j S_{ij} · S̄_{kj} = δ_{ik} -/
  S_unitary : ∀ (i k : Fin n),
    ∑ j : Fin n, S i j * starRingEnd ℂ (S k j) =
    if i = k then 1 else 0

  /-- Non-degeneracy (modularity): S-matrix is invertible.
      Equivalent to: the only transparent object is the vacuum. -/
  S_nondegenerate : ∀ (i : Fin n),
    (∀ (j : Fin n),
      S i j * S ⟨0, by omega⟩ ⟨0, by omega⟩ =
      S ⟨0, by omega⟩ j * S i ⟨0, by omega⟩) →
    i = ⟨0, by omega⟩

  /-- Verlinde formula: N^k_{ij} = Σ_m S_{im} · S_{jm} · S̄_{km} / S_{0m} -/
  verlinde : ∀ (i j k : Fin n),
    (N i j k : ℂ) =
    ∑ m : Fin n, S i m * S j m * starRingEnd ℂ (S k m) / S ⟨0, by omega⟩ m

  /- === Total quantum dimension === -/

  /-- Total quantum dimension squared: D² = Σ_i d_i².
      This is a field (rather than a def) because concrete instances may want
      to state the value directly. Constrained to equal the sum of d_i². -/
  total_dim_sq : ℝ
  total_dim_sq_pos : total_dim_sq > 0
  total_dim_sq_eq : total_dim_sq = ∑ i : Fin n, qdim i ^ 2

/- ============= CONVENIENCE DEFINITIONS ============= -/

variable {n : ℕ} {hn : n ≥ 1}

/-- Total quantum dimension squared for a fusion category -/
noncomputable def FusionCategoryData.totalDimSq
    (fc : FusionCategoryData n hn) : ℝ :=
  ∑ i : Fin n, fc.qdim i ^ 2

/-- Fusion with vacuum on the right: N^k_{j,0} = δ_{jk} -/
theorem FusionCategoryData.N_unit_right
    (fc : FusionCategoryData n hn) (j k : Fin n) :
    fc.N j ⟨0, by omega⟩ k = if j = k then 1 else 0 := by
  rw [fc.N_comm, fc.N_unit_left]

/-- The T-matrix (diagonal matrix of twists) for a ribbon category -/
noncomputable def RibbonCategoryData.T_matrix
    (rc : RibbonCategoryData n hn) (i j : Fin n) : ℂ :=
  if i = j then rc.theta i else 0

/-- Monodromy (double braiding): M^{ab}_c = R^{ab}_c · R^{ba}_c -/
noncomputable def BraidedFusionCategoryData.monodromy
    (bc : BraidedFusionCategoryData n hn) (a b c : Fin n) : ℂ :=
  bc.R a b c * bc.R b a c

/-- An object is transparent if it braids trivially with everything:
    M^{a,i}_c = 1 for all compatible channels -/
def BraidedFusionCategoryData.isTransparent
    (bc : BraidedFusionCategoryData n hn) (i : Fin n) : Prop :=
  ∀ (j c : Fin n), bc.N i j c ≥ 1 → bc.monodromy i j c = 1

/-- An anyon is abelian if it has quantum dimension 1 -/
def FusionCategoryData.isAbelian
    (fc : FusionCategoryData n hn) (i : Fin n) : Prop :=
  fc.qdim i = 1

/-- A fusion category is abelian if all anyons have dimension 1 -/
def FusionCategoryData.allAbelian
    (fc : FusionCategoryData n hn) : Prop :=
  ∀ (i : Fin n), fc.qdim i = 1

/-- An object is a boson: θ_i = 1, d_i = 1, and self-dual -/
def RibbonCategoryData.isBoson
    (rc : RibbonCategoryData n hn) (i : Fin n) : Prop :=
  rc.theta i = 1 ∧ rc.qdim i = 1 ∧ rc.dual i = i

/-- An object is a fermion: θ_i = -1, d_i = 1, and self-dual -/
def RibbonCategoryData.isFermion
    (rc : RibbonCategoryData n hn) (i : Fin n) : Prop :=
  rc.theta i = -1 ∧ rc.qdim i = 1 ∧ rc.dual i = i

/-- The vacuum is always a boson -/
theorem RibbonCategoryData.vacuum_is_boson
    (rc : RibbonCategoryData n hn) :
    rc.isBoson ⟨0, by omega⟩ :=
  ⟨rc.theta_unit, rc.qdim_unit, rc.dual_unit⟩

end PhysicsLogic.QFT.TQFT
