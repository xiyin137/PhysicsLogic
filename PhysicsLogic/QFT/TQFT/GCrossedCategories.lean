-- PhysicsLogic/QFT/TQFT/GCrossedCategories.lean
-- G-actions on fusion categories, G-crossed braided extensions,
-- anyon condensation, and gauging.
--
-- These structures encode the categorical operations needed for
-- symmetry-enriched topological phases and phase transitions between
-- topological orders.
--
-- Imports only FusionCategories.lean (and Mathlib), no manifold dependency.

import PhysicsLogic.QFT.TQFT.FusionCategories
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.Basic

namespace PhysicsLogic.QFT.TQFT

open BigOperators

set_option autoImplicit false

/- ============= G-ACTION ON A FUSION CATEGORY ============= -/

/-- A finite group G acting on a fusion category by permuting simple objects.

    Given a fusion category C with n simple objects, a G-action is a
    group homomorphism G → Aut(C), where each group element g acts as
    a permutation ρ_g : Fin n → Fin n that preserves fusion rules and
    quantum dimensions.

    We parametrize G by its order |G| and use Fin |G| as the set of
    group elements with addition mod |G| as the group operation
    (i.e., G = ℤ_{|G|}). For general groups, generalize accordingly. -/
structure GActionOnCategory (n : ℕ) (hn : n ≥ 1)
    (G_order : ℕ) (hG : G_order ≥ 1)
    (base : FusionCategoryData n hn) where
  /-- Action of group element g on anyon labels: ρ(g, a) -/
  rho : Fin G_order → Fin n → Fin n

  /-- Identity element acts trivially: ρ(0, a) = a -/
  rho_id : ∀ (a : Fin n), rho ⟨0, by omega⟩ a = a

  /-- Action is a group homomorphism: ρ(g, ρ(h, a)) = ρ(g+h mod |G|, a) -/
  rho_comp : ∀ (g h : Fin G_order) (a : Fin n),
    rho g (rho h a) =
    rho ⟨(g.val + h.val) % G_order, Nat.mod_lt _ (by omega)⟩ a

  /-- Action preserves the vacuum: ρ(g, 0) = 0 -/
  rho_vacuum : ∀ (g : Fin G_order),
    rho g ⟨0, by omega⟩ = ⟨0, by omega⟩

  /-- Action preserves fusion rules: N^{ρ(g,c)}_{ρ(g,a),ρ(g,b)} = N^c_{a,b} -/
  rho_preserves_fusion : ∀ (g : Fin G_order) (a b c : Fin n),
    base.N (rho g a) (rho g b) (rho g c) = base.N a b c

  /-- Action preserves quantum dimensions: d_{ρ(g,a)} = d_a -/
  rho_preserves_qdim : ∀ (g : Fin G_order) (a : Fin n),
    base.qdim (rho g a) = base.qdim a

/- ============= G-CROSSED BRAIDED TENSOR CATEGORY ============= -/

/-- G-crossed braided tensor category data.

    Given a fusion category C₀ with G-action, the G-crossed extension is:
    C_G = ⊕_{g ∈ G} C_g
    where C₀ is the original category (identity sector) and C_g (g ≠ e)
    are "defect sectors" containing symmetry defects/fluxes.

    Key properties:
    - GRADING: objects in C_g ⊗ C_h land in C_{gh}
    - G-CROSSED BRAIDING: braiding anyon a (in C₀) with defect σ (in C_g)
      sends a to ρ(g, a) — the anyon is permuted by the symmetry
    - Equal total dimension in each sector: D²_g = D²₀ for all g

    We encode the common case where each nontrivial defect sector has
    a single type of defect object (one simple object per sector). -/
structure GCrossedBraidedData (n : ℕ) (hn : n ≥ 1)
    (G_order : ℕ) (hG : G_order ≥ 1)
    (base : FusionCategoryData n hn)
    (action : GActionOnCategory n hn G_order hG base) where
  /-- Number of simple defect objects per nontrivial sector.
      For simplicity, we assume all nontrivial sectors have the
      same number of simple objects. -/
  defect_count : ℕ
  defect_count_pos : defect_count > 0

  /-- Quantum dimension of defect objects -/
  defect_qdim : Fin defect_count → ℝ
  defect_qdim_pos : ∀ (σ : Fin defect_count), defect_qdim σ > 0

  /-- Total dimension squared of the base sector C₀ -/
  D_sq_0 : ℝ
  D_sq_0_pos : D_sq_0 > 0
  D_sq_0_eq : D_sq_0 = ∑ i : Fin n, base.qdim i ^ 2

  /-- Equal total dimension in the defect sector: Σ_σ d_σ² = D²₀ -/
  D_sq_defect_eq :
    ∑ σ : Fin defect_count, defect_qdim σ ^ 2 = D_sq_0

  /-- Defect self-fusion: σ ⊗ σ' → C₀ with multiplicities N^a_{σ,σ'}.
      When σ and σ' are in conjugate sectors (g and g⁻¹), they fuse
      into the identity sector. -/
  defect_self_fusion : Fin defect_count → Fin defect_count → Fin n → ℕ

  /-- Fusion-dimension consistency for defects:
      d_σ · d_τ = Σ_a N^a_{σ,τ} · d_a -/
  defect_fusion_qdim : ∀ (σ τ : Fin defect_count),
    defect_qdim σ * defect_qdim τ =
    ∑ a : Fin n, (defect_self_fusion σ τ a : ℝ) * base.qdim a

  /-- G-crossed braiding outcome: when base anyon a is braided around
      a defect σ in sector C_g, the outgoing anyon is ρ(g, a).

      This is the defining property of G-crossed braiding:
      c_{a,σ} : a ⊗ σ → σ ⊗ ρ(g, a) -/
  gcrossed_braiding : Fin n → Fin defect_count → Fin n
  gcrossed_braiding_eq : ∀ (a : Fin n) (σ : Fin defect_count),
    ∃ (g : Fin G_order), gcrossed_braiding a σ = action.rho g a

/- ============= ANYON CONDENSATION ============= -/

/-- Data for anyon condensation: a transition C_parent → C_child obtained
    by condensing a bosonic anyon.

    Anyon condensation is the process of choosing a condensable algebra A
    (a boson that "proliferates" to become part of the vacuum).
    Other anyons either:
    - SURVIVE (deconfined): trivial monodromy with A
    - are CONFINED: nontrivial monodromy with A (removed from spectrum)
    - SPLIT: a single parent anyon becomes multiple child anyons

    The condensing anyon must satisfy:
    1. θ_A = 1 (boson)
    2. d_A = 1 (abelian / simple current)
    3. A = A* (self-dual)
    4. A ⊗ A ∋ vacuum -/
structure CondensableAlgebraData
    (n_parent : ℕ) (hn_parent : n_parent ≥ 1)
    (parent : RibbonCategoryData n_parent hn_parent)
    (n_child : ℕ) (hn_child : n_child ≥ 1)
    (child : FusionCategoryData n_child hn_child) where
  /-- The condensing anyon (index in parent theory) -/
  condensing : Fin n_parent

  /-- The condensing anyon is a boson -/
  condensing_is_boson : parent.isBoson condensing

  /-- Condensing anyon fuses with itself to contain the vacuum -/
  condensing_self_fuse :
    parent.N condensing condensing ⟨0, by omega⟩ ≥ 1

  /-- Monodromy sign of each parent anyon with the condensing anyon:
      +1 for deconfined anyons, -1 for confined anyons -/
  monodromy_sign : Fin n_parent → ℤ

  /-- Vacuum has trivial monodromy with condensate -/
  mono_vacuum : monodromy_sign ⟨0, by omega⟩ = 1

  /-- Condensing anyon has trivial monodromy with itself -/
  mono_self : monodromy_sign condensing = 1

  /-- Monodromy sign is ±1 -/
  mono_values : ∀ (a : Fin n_parent),
    monodromy_sign a = 1 ∨ monodromy_sign a = -1

  /-- Map from deconfined parent anyons to child anyons.
      `none` means the anyon is confined (removed).
      Multiple parent anyons may map to the same child anyon (identification).
      A parent anyon may also split (represented by having its own child index). -/
  deconfine_map : Fin n_parent → Option (Fin n_child)

  /-- Confined anyons (monodromy = -1) are removed -/
  confined_removed : ∀ (a : Fin n_parent),
    monodromy_sign a = -1 → deconfine_map a = none

  /-- Deconfined anyons (monodromy = +1) survive -/
  deconfined_survives : ∀ (a : Fin n_parent),
    monodromy_sign a = 1 → deconfine_map a ≠ none

  /-- Vacuum maps to vacuum -/
  deconfine_vacuum :
    deconfine_map ⟨0, by omega⟩ = some ⟨0, by omega⟩

  /-- Order of the simple current group generated by the condensing anyon -/
  condensation_order : ℕ
  condensation_order_pos : condensation_order > 0

  /-- Total dimension ratio: D²_parent = |A|² · D²_child -/
  dim_ratio :
    parent.totalDimSq =
    (condensation_order : ℝ) ^ 2 * child.totalDimSq

/- ============= GAUGING ============= -/

/-- Data for gauging (equivariantization): promoting a global symmetry G
    to a gauge symmetry.

    Given a G-crossed braided category C_G, gauging produces a new MTC
    C_G^G (the equivariantization). The anyons of C_G^G are "dyons":
    pairs of a C_G object with a representation of its stabilizer in G.

    Key physical content:
    - Gauging turns extrinsic defects into dynamical anyons
    - The resulting theory is a full MTC (modular)
    - D²_gauged = |G| · D²₀

    Example: gauging Z₂ on TY(Z₃) recovers SU(2)₄. -/
structure GaugingData
    (n : ℕ) (hn : n ≥ 1)
    (G_order : ℕ) (hG : G_order ≥ 1)
    (base : FusionCategoryData n hn)
    (action : GActionOnCategory n hn G_order hG base)
    (gcrossed : GCrossedBraidedData n hn G_order hG base action) where
  /-- Number of simple objects in the gauged (equivariantized) theory -/
  gauged_rank : ℕ
  gauged_rank_pos : gauged_rank ≥ 1

  /-- The gauged theory is a modular tensor category -/
  gauged_theory : ModularCategoryData gauged_rank gauged_rank_pos

  /-- Total dimension of gauged theory: D²_gauged = |G| · D²₀ -/
  gauged_dim :
    gauged_theory.total_dim_sq = (G_order : ℝ) * gcrossed.D_sq_0

/- ============= CONVENIENCE DEFINITIONS ============= -/

variable {n : ℕ} {hn : n ≥ 1}
variable {G_order : ℕ} {hG : G_order ≥ 1}
variable {base : FusionCategoryData n hn}

/-- An anyon is a fixed point of the G-action if ρ(g, a) = a for all g -/
def GActionOnCategory.isFixedPoint
    (act : GActionOnCategory n hn G_order hG base) (a : Fin n) : Prop :=
  ∀ (g : Fin G_order), act.rho g a = a

/-- A G-action is faithful if it has no non-vacuum fixed points
    (other than the vacuum, which is always fixed) -/
def GActionOnCategory.isFaithful
    (act : GActionOnCategory n hn G_order hG base) : Prop :=
  ∀ (g : Fin G_order), g ≠ ⟨0, by omega⟩ →
    ∃ (a : Fin n), act.rho g a ≠ a

/-- The non-abelian character of a G-crossed extension is extrinsic if
    all base anyons are abelian but some defect has d > 1 -/
def GCrossedBraidedData.isExtrinsicNonAbelian
    {action : GActionOnCategory n hn G_order hG base}
    (gc : GCrossedBraidedData n hn G_order hG base action) : Prop :=
  base.allAbelian ∧ ∃ (σ : Fin gc.defect_count), gc.defect_qdim σ > 1

end PhysicsLogic.QFT.TQFT
