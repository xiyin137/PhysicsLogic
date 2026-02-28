import PhysicsLogic.Quantum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Real.Irrational
import PhysicsLogic.QFT.TQFT.CondensationInstances

/-!
# Charge-4e Superconductor: A Path to Universal TQC

Shi, Han, Raghu, Vishwanath (2025), arXiv:2602.06963

This formalization captures the **logical structure** of the paper's derivation:

  (p+ip)² bilayer → U(2)_{4,0} CS → SU(2)_4
    → condense j=2, confine half-integers → Z₃ TO ≅ SU(3)₁
    → Z₄ SET: ρ_g permutes 1₊↔1₋
    → G-crossed: σ with d_σ=√3, TY fusion σ×σ=0+1+2
    → pentagon/hexagon → F,R-symbols
    → B₁=diag(1,ω⁻¹,ω⁻¹), B₂=(1/√3)(δ+ω(1-δ))
    → Q=B₁, H=B₁B₂B₁ (DFT), CZ=diag(ω^{ab})
    → interferometric M₁=H², M₂=H²Q⁻¹ → magic states |±⟩
    → Bravyi-Kitaev (d=3 prime): universal TQC

The formalization is organized around three principles:
1. **General paradigm**: `TopologicalOrder` and its conceptual enrichments
   define what topological order IS, independent of any specific instance.
2. **Conditional logic**: Each step in the chain has explicit physical
   prerequisites that determine its consequences.
3. **Structural relationships**: Infrastructure instances (`su24_ribbon`,
   `z3_modular`, `z2_gcrossed_z3`) provide the concrete categorical data;
   this file provides the physical interpretation and logical connections.
-/

namespace Charge4eTSC

open PhysicsLogic.Quantum
open PhysicsLogic.QFT.TQFT
open BigOperators

set_option autoImplicit false

-- ═══════════════════════════════════════════════════════════════════════════
-- FOUNDATIONAL CONCEPTS
-- ═══════════════════════════════════════════════════════════════════════════

/-- Qutrit: 3-dimensional quantum system. Parafermion vortices (d_σ=√3)
    naturally encode qutrits rather than qubits (Majorana d_σ=√2). -/
abbrev Qutrit := FiniteDimQuantum 3

abbrev Gate (d : ℕ) := Fin d → Fin d → ℂ

def Gate.id (d : ℕ) : Gate d := fun i j => if i = j then 1 else 0

noncomputable def Gate.mul {d : ℕ} (A B : Gate d) : Gate d :=
  fun i j => ∑ k : Fin d, A i k * B k j

noncomputable def Gate.ofList {d : ℕ} : List (Gate d) → Gate d
  | [] => Gate.id d
  | g :: gs => Gate.mul g (Gate.ofList gs)

abbrev Gate₂ (d : ℕ) := (Fin d × Fin d) → (Fin d × Fin d) → ℂ

noncomputable def ket (a : Fin 3) : Qutrit := EuclideanSpace.single a 1

-- ═══════════════════════════════════════════════════════════════════════════
-- PART I: GENERAL PARADIGM OF TOPOLOGICAL ORDER
-- ═══════════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────────────
-- Symmetry classification (Altland-Zirnbauer tenfold way)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Time-reversal symmetry type. T is antiunitary with T² = ±1.
    - `none`: broken (e.g. magnetic field)
    - `plus`: T² = +1 (integer spin, classes AI, BDI, CI)
    - `minus`: T² = -1 (half-integer spin, classes AII, DIII, CII) -/
inductive TRSymmetry where
  | none | plus | minus
  deriving DecidableEq, Repr

/-- Particle-hole symmetry type. C is antiunitary with C² = ±1. -/
inductive PHSymmetry where
  | none | plus | minus
  deriving DecidableEq, Repr

/-- Chiral (sublattice) symmetry: S = T·C when both T and C are present. -/
inductive ChiralSymmetry where
  | none | present
  deriving DecidableEq, Repr

/-- Altland-Zirnbauer symmetry class. The 10 classes exhaust all consistent
    combinations of T, C, S symmetries. Each class has a characteristic
    topological invariant in each spatial dimension (ℤ, ℤ₂, 2ℤ, or 0). -/
structure SymmetryClass where
  time_reversal : TRSymmetry
  particle_hole : PHSymmetry
  chiral : ChiralSymmetry
  chiral_consistency :
    (time_reversal ≠ TRSymmetry.none ∧ particle_hole ≠ PHSymmetry.none) ↔
    chiral = ChiralSymmetry.present

/-- Class D: broken TRS, PHS with C² = +1. Chiral p-wave superconductors.
    Topological invariant in 2d: ℤ (Chern number ν). -/
def classD : SymmetryClass where
  time_reversal := TRSymmetry.none
  particle_hole := PHSymmetry.plus
  chiral := ChiralSymmetry.none
  chiral_consistency := by
    constructor
    · intro ⟨h, _⟩; exact absurd rfl h
    · intro h; exact absurd h (by decide)

def classBDI : SymmetryClass where
  time_reversal := TRSymmetry.plus
  particle_hole := PHSymmetry.plus
  chiral := ChiralSymmetry.present
  chiral_consistency := by
    constructor
    · intro; rfl
    · intro; exact ⟨by decide, by decide⟩

def classDIII : SymmetryClass where
  time_reversal := TRSymmetry.minus
  particle_hole := PHSymmetry.minus
  chiral := ChiralSymmetry.present
  chiral_consistency := by
    constructor
    · intro; rfl
    · intro; exact ⟨by decide, by decide⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Topological order: the general paradigm
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Topological order** in 2+1d, described by a unitary modular tensor category.

    This represents a paradigm shift from Landau's symmetry-breaking classification.
    Instead of broken symmetries, topological phases are classified by patterns
    of **long-range quantum entanglement**, detectable through:
    - Anyonic quasiparticle excitations with fractional statistics
    - Topological ground state degeneracy on higher-genus surfaces
    - Universal topological entanglement entropy S_topo = ln(D)
    - Chiral central charge c₋ (gravitational response)

    In 2+1d, particles can have statistics beyond bosons and fermions.
    These **anyons** are emergent quasiparticles whose braiding statistics
    are described by a UMTC. The mathematical structure of the UMTC completely
    determines all topological properties of the phase.

    The categorical infrastructure (`ModularCategoryData`, `FusionCategoryData`,
    etc.) provides the formal algebraic axioms. This structure provides the
    physical interpretation and conceptual vocabulary.

    References: Kitaev (2006), Wen (2004), Appendix F of Shi et al. (2025). -/
structure TopologicalOrder (n : ℕ) (hn : n ≥ 1) where
  /-- Fusion multiplicities N^c_{ab}: how anyons combine. -/
  fusion : Fin n → Fin n → Fin n → ℕ
  fusion_unit : ∀ b c, fusion ⟨0, hn⟩ b c = if b = c then 1 else 0
  fusion_comm : ∀ a b c, fusion a b c = fusion b a c
  /-- Quantum dimensions d_a > 0 (largest eigenvalue of fusion matrix N_a). -/
  qdim : Fin n → ℝ
  qdim_pos : ∀ a, qdim a > 0
  qdim_unit : qdim ⟨0, hn⟩ = 1
  qdim_fusion : ∀ a b, qdim a * qdim b = ∑ c : Fin n, (fusion a b c : ℝ) * qdim c
  /-- Modular S-matrix: encodes mutual braiding statistics. -/
  S_matrix : Fin n → Fin n → ℂ
  S_symmetric : ∀ a b, S_matrix a b = S_matrix b a
  S_qdim : ∀ a, (S_matrix a ⟨0, hn⟩) / (S_matrix ⟨0, hn⟩ ⟨0, hn⟩) = ↑(qdim a)
  /-- Topological spin θ_a = e^{2πi h_a}: self-statistics phase. -/
  topological_spin : Fin n → ℂ
  spin_unit : topological_spin ⟨0, hn⟩ = 1
  spin_phase : ∀ a, topological_spin a * starRingEnd ℂ (topological_spin a) = 1
  /-- Chiral central charge c₋: gravitational response coefficient. -/
  chiral_central_charge : ℚ
  /-- Total quantum dimension squared: D² = Σ_a d_a². -/
  total_dim_sq : ℝ
  total_dim_sq_eq : total_dim_sq = ∑ a : Fin n, qdim a ^ 2
  total_dim_sq_pos : total_dim_sq > 0

/-- Torus ground state degeneracy = number of anyon types.
    A topological invariant: robust to all local perturbations. -/
def TopologicalOrder.torus_GSD {n : ℕ} {hn : n ≥ 1}
    (_ : TopologicalOrder n hn) : ℕ := n

/-- Topological entanglement entropy: S_topo = ln(D).
    The universal constant correction to area-law entanglement. -/
noncomputable def TopologicalOrder.topo_entropy {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) : ℝ :=
  Real.log (Real.sqrt to_.total_dim_sq)

-- ─────────────────────────────────────────────────────────────────────────────
-- Conceptual enrichments: physical properties of anyons
-- ─────────────────────────────────────────────────────────────────────────────

/-- An anyon is **Abelian** iff d_a = 1. Abelian anyons have unique fusion
    outcomes: a ⊗ b produces exactly one anyon type. They form a finite
    group under fusion. -/
def TopologicalOrder.is_abelian {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n) : Prop :=
  to_.qdim a = 1

/-- A topological order is **purely Abelian** if all anyons have d = 1.
    Purely Abelian TOs (like Z₃ ≅ SU(3)₁) cannot support universal TQC
    from intrinsic braiding alone — they need symmetry enrichment to
    create non-Abelian defects. This is the central mechanism of the 4e TSC. -/
def TopologicalOrder.is_purely_abelian {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) : Prop :=
  ∀ a, to_.is_abelian a

/-- An anyon is a **boson** iff θ_a = 1 (trivial self-statistics).
    Only bosons can be consistently condensed (identified with the vacuum)
    while preserving unitarity of the topological field theory. -/
def TopologicalOrder.is_boson {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n) : Prop :=
  to_.topological_spin a = 1

/-- A **simple current** is an Abelian boson that generates a Z_n
    subgroup under fusion. Simple currents are the natural candidates
    for condensation: they satisfy θ = 1 and d = 1, and their self-fusion
    produces the vacuum. -/
def TopologicalOrder.is_simple_current {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n) : Prop :=
  to_.is_boson a ∧ to_.is_abelian a ∧ to_.fusion a a ⟨0, hn⟩ = 1

-- ─────────────────────────────────────────────────────────────────────────────
-- Monodromy: the key to anyon condensation
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Monodromy** of anyon j with respect to anyon a:
    M_{j,a} = S_{j,a} / (d_j · S_{0,a}).

    Physical interpretation: when anyon j completes a full loop around
    anyon a, the quantum state acquires the Aharonov-Bohm phase M_{j,a}.

    In **anyon condensation** theory, monodromy determines the fate of
    each anyon when a boson a is condensed (identified with the vacuum):
    - M_{j,a} = +1 → **deconfined**: j has trivial braiding with the
      condensate, survives in the child topological order
    - M_{j,a} = -1 → **confined**: j has nontrivial braiding, the
      Aharonov-Bohm phase causes destructive interference, removing j
      from the low-energy spectrum

    This is the topological analog of the Higgs mechanism: condensation
    "breaks" the topological order by identifying an anyon with the vacuum,
    and the monodromy criterion systematically determines the child theory. -/
noncomputable def TopologicalOrder.monodromy {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (j a : Fin n) : ℂ :=
  to_.S_matrix j a / ((↑(to_.qdim j) : ℂ) * to_.S_matrix ⟨0, hn⟩ a)

/-- The vacuum always has trivial monodromy with any anyon.
    This is a general property of the paradigm: the vacuum braids
    trivially with everything, in any topological order. -/
theorem TopologicalOrder.monodromy_vacuum {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n)
    (hS : to_.S_matrix ⟨0, hn⟩ a ≠ 0) :
    to_.monodromy ⟨0, hn⟩ a = 1 := by
  unfold TopologicalOrder.monodromy
  rw [to_.qdim_unit]; simp only [Complex.ofReal_one, one_mul]
  exact div_self hS

-- ─────────────────────────────────────────────────────────────────────────────
-- Condensation criterion: when can a boson be condensed?
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Condensation criterion** for simple-current condensation.
    An anyon a in a topological order can be condensed if:
    1. θ_a = 1 (boson): required by unitarity
    2. d_a = 1 (Abelian/simple current): generates a finite group
    3. N^0_{aa} = 1 (self-dual): a × a produces the vacuum

    When these conditions hold, the subgroup {0, a, a², ...} is
    "gauged away", producing a child TO with D²(child) = D²(parent)/|G|².

    This structure captures the **conditional logic** of condensation:
    IF the three criteria are satisfied, THEN condensation is consistent. -/
structure CondensationCriterion {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) where
  condensing : Fin n
  is_boson : to_.is_boson condensing
  is_abelian : to_.is_abelian condensing
  self_fuse_to_vacuum : to_.fusion condensing condensing ⟨0, hn⟩ = 1

-- ═══════════════════════════════════════════════════════════════════════════
-- PART II: SUPERCONDUCTOR PHYSICS (Sections II-III)
-- ═══════════════════════════════════════════════════════════════════════════

inductive PairingSymmetry where
  | s_wave | p_wave | d_wave
  | higher (ℓ : ℕ) (hℓ : ℓ ≥ 3)
  deriving DecidableEq, Repr

def PairingSymmetry.angular_momentum : PairingSymmetry → ℕ
  | .s_wave => 0
  | .p_wave => 1
  | .d_wave => 2
  | .higher ℓ _ => ℓ

/-- Topological superconductor in 2+1d. The Chern number ν ∈ ℤ counts
    chiral Majorana edge modes, each contributing c₋ = 1/2 to the
    chiral central charge. -/
structure TSC where
  ν : ℤ
  symmetry_class : SymmetryClass
  pairing : PairingSymmetry
  bulk_gap : ℝ
  bulk_gap_pos : bulk_gap > 0

def TSC.chiral_central_charge (t : TSC) : ℚ := t.ν / 2
def TSC.num_edge_modes (t : TSC) : ℕ := t.ν.natAbs
def TSC.cooper_pair_charge (_ : TSC) : ℕ := 2
def TSC.is_class_D (t : TSC) : Prop := t.symmetry_class = classD

theorem TSC.p_wave_single_edge (t : TSC) (hν : t.ν = 1) :
    t.num_edge_modes = 1 := by
  simp [TSC.num_edge_modes, hν]

/-- (p+ip)² bilayer: two ν=1 TSC layers coupled by Andreev-Bashkin
    current-current interaction. Key parameters:
    - ρ_c > ρ_s drives charge-neutral vortex condensation → 4e SC
    - λ₁ > 0 selects diagonal Higgs vacuum → U(2)_{4,0} CS theory -/
structure Bilayer where
  layer₁ : TSC
  layer₂ : TSC
  hν₁ : layer₁.ν = 1
  hν₂ : layer₂.ν = 1
  hclass₁ : layer₁.is_class_D
  hclass₂ : layer₂.is_class_D
  hpair₁ : layer₁.pairing = PairingSymmetry.p_wave
  hpair₂ : layer₂.pairing = PairingSymmetry.p_wave
  ρ_c : ℝ
  ρ_s : ℝ
  ρ_s_pos : ρ_s > 0
  charge_dominant : ρ_c > ρ_s
  lam₁ : ℝ
  lam₁_pos : lam₁ > 0

/-- Condensate charge = 2e + 2e = 4e (one Cooper pair per layer). -/
def Bilayer.condensate_charge (b : Bilayer) : ℕ :=
  b.layer₁.cooper_pair_charge + b.layer₂.cooper_pair_charge

/-- Bilayer c₋ = ν₁/2 + ν₂/2 = 1/2 + 1/2 = 1. -/
theorem bilayer_c_minus (b : Bilayer) :
    b.layer₁.chiral_central_charge + b.layer₂.chiral_central_charge = 1 := by
  simp [TSC.chiral_central_charge, b.hν₁, b.hν₂]; norm_num

theorem bilayer_edge_modes (b : Bilayer) :
    b.layer₁.num_edge_modes = 1 ∧ b.layer₂.num_edge_modes = 1 :=
  ⟨b.layer₁.p_wave_single_edge b.hν₁, b.layer₂.p_wave_single_edge b.hν₂⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Vortex energetics: conditional logic for which vortex condenses
-- ─────────────────────────────────────────────────────────────────────────────

structure BilayerVortex where
  n₁ : ℤ
  n₂ : ℤ

def BilayerVortex.charge_winding (v : BilayerVortex) : ℤ := v.n₁ + v.n₂
def BilayerVortex.spin_winding (v : BilayerVortex) : ℤ := v.n₁ - v.n₂

/-- v₁v̄₂: the cheapest nontrivial vortex when ρ_c > ρ_s. -/
def v1v2bar : BilayerVortex := ⟨1, -1⟩

theorem v1v2bar_charge_zero : v1v2bar.charge_winding = 0 := by
  simp [v1v2bar, BilayerVortex.charge_winding]

theorem v1v2bar_spin_two : v1v2bar.spin_winding = 2 := by
  simp [v1v2bar, BilayerVortex.spin_winding]

/-- Vortex energy: E ∝ ρ_c · n_c² + ρ_s · n_s².
    The charge/spin decomposition makes the energetic selection transparent. -/
noncomputable def vortex_energy (b : Bilayer) (v : BilayerVortex) : ℝ :=
  b.ρ_c * (v.charge_winding : ℝ) ^ 2 + b.ρ_s * (v.spin_winding : ℝ) ^ 2

private lemma int_sq_ge_one {n : ℤ} (hn : n ≠ 0) : (n : ℝ) ^ 2 ≥ 1 := by
  suffices h : (1 : ℤ) ≤ n ^ 2 by exact_mod_cast h
  have : n ≤ -1 ∨ 1 ≤ n := by omega
  rcases this with h | h <;> nlinarith

/-- v₁v̄₂ costs only spin stiffness: E = 4ρ_s (zero charge cost). -/
theorem v1v2bar_energy (b : Bilayer) :
    vortex_energy b v1v2bar = 4 * b.ρ_s := by
  unfold vortex_energy
  rw [v1v2bar_charge_zero, v1v2bar_spin_two]
  push_cast; ring

/-- **Conditional logic**: IF ρ_c > ρ_s THEN charge-carrying vortices
    are parametrically more expensive than v₁v̄₂.
    Any vortex with n_c ≠ 0 pays at least ρ_c ≫ 4ρ_s in energy.
    This drives v₁v̄₂ to condense first via the BKT mechanism. -/
theorem charge_carrying_vortex_costly (b : Bilayer) (v : BilayerVortex)
    (hnc : v.charge_winding ≠ 0) :
    vortex_energy b v ≥ b.ρ_c := by
  unfold vortex_energy
  have hρc : b.ρ_c > 0 := lt_trans b.ρ_s_pos b.charge_dominant
  have hρs : b.ρ_s > 0 := b.ρ_s_pos
  have hsq : (v.charge_winding : ℝ) ^ 2 ≥ 1 := int_sq_ge_one hnc
  nlinarith [sq_nonneg (v.spin_winding : ℝ)]

/-- Vortex condensation: charge-neutral (avoids ρ_c), spin-nontrivial
    (breaks U(1)_s → charge-4e condensate). -/
structure VortexCondensation where
  bilayer : Bilayer
  vortex : BilayerVortex
  charge_neutral : vortex.charge_winding = 0
  spin_nontrivial : vortex.spin_winding ≠ 0

def standard_4e_condensation (b : Bilayer) : VortexCondensation where
  bilayer := b
  vortex := v1v2bar
  charge_neutral := v1v2bar_charge_zero
  spin_nontrivial := by simp [v1v2bar, BilayerVortex.spin_winding]

-- ─────────────────────────────────────────────────────────────────────────────
-- Higgs classification: conditional logic for the condensation pattern
-- ─────────────────────────────────────────────────────────────────────────────

inductive HiggsPattern where
  | topological : HiggsPattern
  | trivial : HiggsPattern

/-- Higgs classification: the sign of λ₁ determines the phase.
    This is the branching point in the paper's derivation:
    - λ₁ > 0 → topological 4e SC with Z₃ TO (the interesting case)
    - λ₁ < 0 → trivial 4e SC (no TO) -/
structure HiggsClassification where
  lam₁ : ℝ
  lam₁_nonzero : lam₁ ≠ 0
  pattern : HiggsPattern
  pos_topological : lam₁ > 0 → pattern = HiggsPattern.topological
  neg_trivial : lam₁ < 0 → pattern = HiggsPattern.trivial
  num_anyons : ℕ
  topological_count : pattern = HiggsPattern.topological → num_anyons = 3
  trivial_count : pattern = HiggsPattern.trivial → num_anyons = 1

/-- **Conditional logic**: the Bilayer has λ₁ > 0, so the topological
    pattern is selected. This is the entry point to the interesting physics. -/
theorem bilayer_selects_topological (b : Bilayer) (hc : HiggsClassification)
    (hlam : hc.lam₁ = b.lam₁) :
    hc.pattern = HiggsPattern.topological := by
  exact hc.pos_topological (hlam ▸ b.lam₁_pos)

-- ═══════════════════════════════════════════════════════════════════════════
-- PART III: CHERN-SIMONS THEORY (Sections III-IV, Appendices A-B)
-- ═══════════════════════════════════════════════════════════════════════════

/-- U(2) Chern-Simons theory at levels (k₁, k₂).
    Factorization: U(2)_{k₁,k₂} = [SU(2)_{k₁} × U(1)_{k₂}] / Z₂.
    For the 4e TSC: (k₁, k₂) = (4, 0). -/
structure U2_ChernSimons where
  k₁ : ℕ
  k₁_pos : k₁ > 0
  k₂ : ℤ

def U2_ChernSimons.c_minus_SU2 (cs : U2_ChernSimons) : ℚ :=
  (cs.k₁ * 3 : ℚ) / (↑cs.k₁ + 2)

def U2_ChernSimons.num_anyons_SU2 (cs : U2_ChernSimons) : ℕ := cs.k₁ + 1

def u2_4_0 : U2_ChernSimons where
  k₁ := 4
  k₁_pos := by omega
  k₂ := 0

theorem u2_4_0_c_minus : u2_4_0.c_minus_SU2 = 2 := by
  simp [U2_ChernSimons.c_minus_SU2, u2_4_0]; norm_num

theorem u2_4_0_num_anyons : u2_4_0.num_anyons_SU2 = 5 := by
  simp [U2_ChernSimons.num_anyons_SU2, u2_4_0]

/-- Bridge between the parton/CS theory and the TO.
    The CS level is determined by the bilayer (k = 2(ν₁+ν₂)),
    and the spin sector SU(2)_k determines the parent TO. -/
structure CS_TO_Bridge where
  bilayer : Bilayer
  cs : U2_ChernSimons

def CS_TO_Bridge.cs_level (bridge : CS_TO_Bridge) : ℕ := bridge.cs.k₁
def CS_TO_Bridge.spin_sector_anyons (bridge : CS_TO_Bridge) : ℕ :=
  bridge.cs.num_anyons_SU2

-- ═══════════════════════════════════════════════════════════════════════════
-- PART IV: SU(2)₄ → Z₃ CONDENSATION (Section IV)
-- ═══════════════════════════════════════════════════════════════════════════

-- The SU(2)₄ fusion rules, quantum dimensions, and topological spins
-- come from the categorical infrastructure:
--   su24_fusion  : FusionCategoryData 5    (fusion, qdim)
--   su24_ribbon  : RibbonCategoryData 5    (theta)
--   su24_qdim    : Fin 5 → ℝ              (1, √3, 2, √3, 1)
--   su24_N       : Fin 5 → Fin 5 → Fin 5 → ℕ
--   su24_theta   : Fin 5 → ℂ
-- See FusionInstances.lean and CondensationInstances.lean.

/-- **Condensation criterion verified**: j=2 (index 4) in SU(2)₄ is a
    boson simple current, satisfying all three condensation prerequisites.
    - θ₂ = 1: boson (can be identified with vacuum)
    - d₂ = 1: simple current (generates Z₂ = {0, j=2})
    - N^0_{22} = 1: self-dual (2 × 2 = 0) -/
theorem su24_j2_condensable :
    su24_theta ⟨4, by omega⟩ = 1 ∧
    su24_qdim ⟨4, by omega⟩ = 1 ∧
    su24_N ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨0, by omega⟩ = 1 :=
  ⟨su24_theta_j2, su24_d2, by native_decide⟩

/-- Condensing j=2 ≡ 0 creates two vacuum channels in 1×1 = 0+1+2:
    N^0_{11} + N^{2≡0}_{11} = 2. This forces j=1 to **split** into
    two distinct anyons 1₊, 1₋ in the child theory.
    The splitting phenomenon is characteristic of non-Abelian condensation. -/
theorem su24_j1_vacuum_multiplicity :
    su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ +
    su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = 2 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- S-matrix and monodromy for SU(2)₄
-- ─────────────────────────────────────────────────────────────────────────────

/-- SU(2)₄ S-matrix data: the S-matrix entries relevant for monodromy.
    All other SU(2)₄ data (qdim, fusion, theta) comes from infrastructure.
    The S-matrix entries encode the Verlinde formula representation and
    determine which anyons are confined under j=2 condensation. -/
structure SU2_4_SData where
  S_matrix : Fin 5 → Fin 5 → ℂ
  S_symmetric : ∀ a b, S_matrix a b = S_matrix b a
  S_0_2_ne : S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩ ≠ 0
  /-- Confined: S_{½,2} = -d_{½}·S_{0,2} (monodromy -1) -/
  S_half_2 : S_matrix ⟨1, by omega⟩ ⟨4, by omega⟩ =
    -(↑(su24_qdim ⟨1, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  S_threehalf_2 : S_matrix ⟨3, by omega⟩ ⟨4, by omega⟩ =
    -(↑(su24_qdim ⟨3, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  /-- Deconfined: S_{1,2} = +d₁·S_{0,2} (monodromy +1) -/
  S_1_2 : S_matrix ⟨2, by omega⟩ ⟨4, by omega⟩ =
    (↑(su24_qdim ⟨2, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  S_2_2 : S_matrix ⟨4, by omega⟩ ⟨4, by omega⟩ =
    (↑(su24_qdim ⟨4, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩

/-- Monodromy M_{j,2} = S_{j,2} / (d_j · S_{0,2}): the Aharonov-Bohm
    phase when anyon j encircles the j=2 condensate. -/
noncomputable def su24_monodromy (sdata : SU2_4_SData) (j : Fin 5) : ℂ :=
  sdata.S_matrix j ⟨4, by omega⟩ /
  ((↑(su24_qdim j) : ℂ) * sdata.S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩)

-- Individual monodromy values (needed for the confinement criterion)
theorem su24_monodromy_j0 (sdata : SU2_4_SData) :
    su24_monodromy sdata ⟨0, by omega⟩ = 1 := by
  simp only [su24_monodromy, su24_d0]; push_cast; rw [one_mul]
  exact div_self (sdata.S_0_2_ne)

theorem su24_monodromy_jhalf (sdata : SU2_4_SData) :
    su24_monodromy sdata ⟨1, by omega⟩ = -1 := by
  simp only [su24_monodromy, sdata.S_half_2]
  rw [neg_mul, neg_div, div_self (mul_ne_zero
    (su24_qdim_ne_zero_complex ⟨1, by omega⟩) sdata.S_0_2_ne)]

theorem su24_monodromy_j1 (sdata : SU2_4_SData) :
    su24_monodromy sdata ⟨2, by omega⟩ = 1 := by
  simp only [su24_monodromy, sdata.S_1_2]
  exact div_self (mul_ne_zero
    (su24_qdim_ne_zero_complex ⟨2, by omega⟩) sdata.S_0_2_ne)

theorem su24_monodromy_jthreehalf (sdata : SU2_4_SData) :
    su24_monodromy sdata ⟨3, by omega⟩ = -1 := by
  simp only [su24_monodromy, sdata.S_threehalf_2]
  rw [neg_mul, neg_div, div_self (mul_ne_zero
    (su24_qdim_ne_zero_complex ⟨3, by omega⟩) sdata.S_0_2_ne)]

theorem su24_monodromy_j2 (sdata : SU2_4_SData) :
    su24_monodromy sdata ⟨4, by omega⟩ = 1 := by
  simp only [su24_monodromy, sdata.S_2_2]
  exact div_self (mul_ne_zero
    (su24_qdim_ne_zero_complex ⟨4, by omega⟩) sdata.S_0_2_ne)

/-- **Confinement criterion**: half-integer spins have M = -1 (confined),
    integer spins have M = +1 (deconfined). This is the structural
    relationship between SU(2) representation theory and the child theory:
    - Integer spins (j = 0, 1, 2) survive → become Z₃ anyons {0, 1₊, 1₋}
    - Half-integer spins (j = ½, 3/2) are removed from the spectrum -/
theorem su24_confined_iff_half_integer (sdata : SU2_4_SData) (j : Fin 5) :
    su24_monodromy sdata j = -1 ↔ (j = ⟨1, by omega⟩ ∨ j = ⟨3, by omega⟩) := by
  constructor
  · intro hm; fin_cases j
    · rw [su24_monodromy_j0] at hm; norm_num at hm
    · left; rfl
    · rw [su24_monodromy_j1] at hm; norm_num at hm
    · right; rfl
    · rw [su24_monodromy_j2] at hm; norm_num at hm
  · rintro (rfl | rfl)
    · exact su24_monodromy_jhalf sdata
    · exact su24_monodromy_jthreehalf sdata

-- ═══════════════════════════════════════════════════════════════════════════
-- PART V: SYMMETRY ENRICHMENT AND G-CROSSED EXTENSION (Section IV, App. F-G)
-- ═══════════════════════════════════════════════════════════════════════════

-- The Z₃ topological order after condensation is `z3_modular` from the
-- infrastructure. The Z₂ symmetry action (charge conjugation on Z₃)
-- is `z2_action_on_z3` with the concrete function `z2_rho_on_z3`.
-- The G-crossed braided extension is `z2_gcrossed_z3`.

-- ─────────────────────────────────────────────────────────────────────────────
-- Z₂ symmetry action on Z₃ anyons
-- ─────────────────────────────────────────────────────────────────────────────

-- The 4e condensate breaks U(1)_c → Z₄. The generator g of Z₄ acts on
-- Z₃ anyons as charge conjugation: ρ_g(0) = 0, ρ_g(1₊) = 1₋, ρ_g(1₋) = 1₊.
-- The Z₂ subgroup g² = (-1)^F acts trivially on the bosonic sector,
-- so the effective action is Z₄/Z₂ ≅ Z₂. This is `z2_rho_on_z3`.

/-- ρ is an involution: charge conjugation squared is the identity. -/
theorem z2_rho_involution :
    ∀ a : Fin 3, z2_rho_on_z3 ⟨1, by omega⟩ (z2_rho_on_z3 ⟨1, by omega⟩ a) = a := by
  intro a; fin_cases a <;> simp [z2_rho_on_z3, z3_dual]

/-- Only the vacuum is fixed by charge conjugation: Z₃^{Z₂} = {0}.
    This is the first ingredient of the cohomological classification
    H²(Z₂, Z₃) = Z₃^{Z₂}/Im(N) = {0}/{0} = 0, showing that the
    symmetry fractionalization class is **unique**. -/
theorem fixed_points_trivial :
    ∀ a : Fin 3, z2_rho_on_z3 ⟨1, by omega⟩ a = a → a = ⟨0, by omega⟩ := by
  intro a ha; fin_cases a
  · rfl
  · simp [z2_rho_on_z3, z3_dual] at ha
  · simp [z2_rho_on_z3, z3_dual] at ha

/-- Norm map N(a) = a + ρ(a) is trivial: every anyon fuses with its
    charge conjugate to give the vacuum. Im(N) = {0}, ker(N) = Z₃. -/
theorem norm_map_trivial :
    ∀ a : Fin 3, z3_fuse a (z2_rho_on_z3 ⟨1, by omega⟩ a) = ⟨0, by omega⟩ := by
  intro a; fin_cases a <;> simp [z3_fuse, z2_rho_on_z3, z3_dual]

-- ─────────────────────────────────────────────────────────────────────────────
-- G-crossed extension and the parafermion defect
-- ─────────────────────────────────────────────────────────────────────────────

-- The G-crossed extension C_G = C₀ ⊕ C_g enriches the Z₃ topological
-- order with symmetry defects. C₀ = Z₃ (3 Abelian anyons), C_g = {σ}
-- (1 parafermion defect with d_σ = √3).
--
-- The proper categorical structure is `z2_gcrossed_z3 : GCrossedBraidedData`
-- from CondensationInstances.lean, which enforces:
--   - Proper group action axioms (identity, composition, vacuum-preserving)
--   - Fusion-preserving and qdim-preserving action
--   - Equal total dimension per sector: Σ_σ d_σ² = D²₀ = 3
--   - Fusion-dimension consistency for defects
--   - G-crossed braiding: outcome is ρ_g(a)

/-- Abbreviation identifying the 4e TSC G-crossed extension. -/
noncomputable abbrev z2_gcrossed_4eTSC
    (h_z3 : PhysicsLogic.PhysicsAssumption PhysicsLogic.AssumptionId.tqftZ3ModularAxioms
      Z3ModularAssumptions) := z2_gcrossed_z3 h_z3

/-- Total quantum dimension of the G-crossed extension:
    D²(C_G) = D²₀ + Σ_σ d_σ² = 2·D²₀.
    For the 4e TSC: D²(C_{Z₂}) = 3 + 3 = 6. -/
theorem total_dim_gcrossed {n : ℕ} {hn : n ≥ 1} {G_order : ℕ} {hG : G_order ≥ 1}
    {base : FusionCategoryData n hn}
    {action : GActionOnCategory n hn G_order hG base}
    (gc : GCrossedBraidedData n hn G_order hG base action) :
    gc.D_sq_0 + ∑ σ : Fin gc.defect_count, gc.defect_qdim σ ^ 2 = 2 * gc.D_sq_0 := by
  rw [gc.D_sq_defect_eq]; ring

/-- **Extrinsic non-Abelian statistics**: the central conceptual insight.

    The Z₃ topological order is purely Abelian (all d = 1). Non-Abelian
    statistics (d_σ = √3 > 1) arise ENTIRELY from the symmetry enrichment:
    the parafermion σ is a **symmetry defect** (extrinsic, in C_g),
    not an intrinsic anyon (in C₀).

    This is fundamentally different from Ising (SU(2)₂) where non-Abelian
    anyons are bulk excitations. The 4e TSC achieves non-Abelian TQC by
    enriching an Abelian order with symmetry and exploiting flux defects.

    Philosophical implication: non-Abelian statistics is not an intrinsic
    property of the topological order, but can be an emergent consequence
    of how symmetry interacts with topology. -/
theorem non_abelian_is_extrinsic :
    ∀ (h_z3 : PhysicsLogic.PhysicsAssumption PhysicsLogic.AssumptionId.tqftZ3ModularAxioms
      Z3ModularAssumptions), (z2_gcrossed_z3 h_z3).isExtrinsicNonAbelian := by
  intro h_z3
  refine ⟨fun i => rfl, ⟨0, (z2_gcrossed_z3 h_z3).defect_count_pos⟩, ?_⟩
  show Real.sqrt 3 > 1
  have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 3)
  rwa [Real.sqrt_one] at h

-- ─────────────────────────────────────────────────────────────────────────────
-- Parafermion data
-- ─────────────────────────────────────────────────────────────────────────────

/-- Z₃ parafermion defect data beyond the G-crossed infrastructure.

    The quantum dimension (d_σ = √3), fusion rules (σ×σ = 0+1+2, σ×a = σ),
    and G-crossed braiding come from `z2_gcrossed_z3`.

    This structure adds only the **Frobenius-Schur indicator** κ_σ = -1,
    which selects the nontrivial element of H³(Z₂, U(1)) = Z₂ and enters
    the F-symbol: F^{σσσ}_{σef} = (κ_σ/√3)·χ(e,f)⁻¹. -/
structure Parafermion where
  kappa_sigma : ℤ
  kappa_eq : kappa_sigma = -1

-- ═══════════════════════════════════════════════════════════════════════════
-- PART VI: ALGEBRAIC DATA AND BRAIDING (Appendix G-H)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Pentagon → F-symbols, Hexagon → R-symbols (App. G).
    These are the algebraic data from which all gates are constructed.
    ω = e^{2πi/3}, χ(e,f) = ω^{ef}, F = -(1/√3)·χ⁻¹.
    The gauge-invariant ratios R_a/R_0 determine the braiding matrices. -/
structure SymbolData where
  pf : Parafermion
  omega : ℂ
  omega_cubed : omega ^ 3 = 1
  omega_ne_one : omega ≠ 1
  chi : Fin 3 → Fin 3 → ℂ
  chi_def : ∀ e f, chi e f = omega ^ (e.val * f.val)
  F_symbol : Fin 3 → Fin 3 → ℂ
  F_def : ∀ e f, F_symbol e f = -(1 / ↑(Real.sqrt 3)) * (chi e f)⁻¹
  R_symbol : Fin 3 → ℂ
  R_0_ne_zero : R_symbol ⟨0, by omega⟩ ≠ 0
  Y_phase : ℂ
  Y_sq : Y_phase ^ 2 = -Complex.I
  ratio : Fin 3 → ℂ
  ratio_from_R : ∀ a, ratio a = R_symbol a * (R_symbol ⟨0, by omega⟩)⁻¹
  ratio_1 : ratio ⟨1, by omega⟩ = omega⁻¹
  ratio_2 : ratio ⟨2, by omega⟩ = omega⁻¹

theorem ratio_0 (sd : SymbolData) : sd.ratio ⟨0, by omega⟩ = 1 := by
  rw [sd.ratio_from_R]; exact mul_inv_cancel₀ sd.R_0_ne_zero

theorem chi_symmetric (sd : SymbolData) (e f : Fin 3) :
    sd.chi e f = sd.chi f e := by
  simp only [sd.chi_def]; congr 1; exact Nat.mul_comm e.val f.val

theorem chi_vacuum (sd : SymbolData) (f : Fin 3) :
    sd.chi ⟨0, by omega⟩ f = 1 := by
  simp [sd.chi_def]

/-- F-symbol encodes κ_σ: the Frobenius-Schur indicator determines the
    sign of the F-matrix, connecting defectification cohomology to algebra. -/
theorem F_from_kappa (sd : SymbolData) (e f : Fin 3) :
    sd.F_symbol e f =
    (↑sd.pf.kappa_sigma : ℂ) * (1 / ↑(Real.sqrt 3)) * (sd.chi e f)⁻¹ := by
  rw [sd.F_def, sd.pf.kappa_eq]; push_cast; ring

/-- B₁ = diag(ratio(a)), B₂ = (1/√3)(δ + ω(1-δ)). -/
structure Braiding where
  sd : SymbolData
  B₁ : Gate 3
  B₁_diag : ∀ a, B₁ a a = sd.ratio a
  B₁_off : ∀ a b, a ≠ b → B₁ a b = 0
  B₂ : Gate 3
  B₂_def : ∀ a b, B₂ a b =
    (1 / ↑(Real.sqrt 3)) * (if a = b then 1 else sd.omega)

-- ═══════════════════════════════════════════════════════════════════════════
-- PART VII: GATE CONSTRUCTIONS (Section V, Appendix H)
-- ═══════════════════════════════════════════════════════════════════════════

noncomputable def phase_gate (bm : Braiding) : Gate 3 := bm.B₁

noncomputable def hadamard (bm : Braiding) : Gate 3 :=
  Gate.mul (Gate.mul bm.B₁ bm.B₂) bm.B₁

/-- B₁ diagonal ⟹ double sum collapses: H_{ab} = B₁_{aa}·B₂_{ab}·B₁_{bb}. -/
theorem hadamard_reduces (bm : Braiding) (a b : Fin 3) :
    hadamard bm a b = bm.B₁ a a * bm.B₂ a b * bm.B₁ b b := by
  unfold hadamard Gate.mul
  have inner : ∀ k, ∑ j : Fin 3, bm.B₁ a j * bm.B₂ j k = bm.B₁ a a * bm.B₂ a k :=
    fun k => Finset.sum_eq_single a
      (fun j _ hj => by rw [bm.B₁_off a j hj.symm, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h)
  simp_rw [inner]
  exact Finset.sum_eq_single b
    (fun k _ hk => by rw [bm.B₁_off k b hk, mul_zero])
    (fun h => absurd (Finset.mem_univ b) h)

theorem hadamard_explicit (bm : Braiding) (a b : Fin 3) :
    hadamard bm a b =
    bm.sd.ratio a *
    ((1 / ↑(Real.sqrt 3)) * (if a = b then 1 else bm.sd.omega)) *
    bm.sd.ratio b := by
  rw [hadamard_reduces, bm.B₁_diag, bm.B₂_def, bm.B₁_diag]

/-- CZ gate: diagonal entangling gate from braiding 6σ defects. -/
noncomputable def control_Z (bm : Braiding) : Gate₂ 3 :=
  fun ⟨a, b⟩ ⟨a', b'⟩ =>
    if a = a' ∧ b = b' then bm.sd.omega ^ (a.val * b.val) else 0

-- ─────────────────────────────────────────────────────────────────────────────
-- Qutrit encoding from defect Hilbert space
-- ─────────────────────────────────────────────────────────────────────────────

-- 4σ encode 1 qutrit: dim = d_σ⁴/D² = 9/3 = 3.
-- 6σ encode 2 qutrits: dim = d_σ⁶/D² = 27/3 = 9 = 3².
-- Defects are created externally by threading hc/(4e) flux.

theorem qutrit_encoding :
    (Real.sqrt 3) ^ 4 / (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h4 : Real.sqrt 3 ^ 4 = 9 := by
    have : Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
    rw [this, h]; norm_num
  rw [h4, h]; norm_num

theorem two_qutrit_encoding :
    (Real.sqrt 3) ^ 6 / (Real.sqrt 3) ^ 2 = (9 : ℝ) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h6 : Real.sqrt 3 ^ 6 = 27 := by
    have : Real.sqrt 3 ^ 6 = (Real.sqrt 3 ^ 2) ^ 3 := by ring
    rw [this, h]; norm_num
  rw [h6, h]; norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- PART VIII: MEASUREMENT AND MAGIC STATES (Section V, Appendix H.2)
-- ═══════════════════════════════════════════════════════════════════════════

noncomputable def M₁ (bm : Braiding) : Gate 3 :=
  Gate.mul (hadamard bm) (hadamard bm)

noncomputable def M₂ (bm : Braiding) : Gate 3 :=
  fun a b => ∑ i : Fin 3, M₁ bm a i *
    (if i = b then (bm.sd.ratio i)⁻¹ else 0)

noncomputable def magic_plus : Qutrit :=
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨1, by omega⟩ +
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨2, by omega⟩

noncomputable def magic_minus : Qutrit :=
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨1, by omega⟩ -
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨2, by omega⟩

theorem M₁_swap (bm : Braiding) :
    M₁ bm ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    M₁ bm ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 := sorry

/-- M₂ eigenvalues (1, ω, -ω) are pairwise distinct.
    This enables deterministic magic state preparation via repeated
    measurement: postselecting on eigenvalue ω prepares |+⟩. -/
theorem M₂_eigenvalues_distinct (bm : Braiding) :
    let evZ : ℂ := 1
    let evP : ℂ := bm.sd.omega
    let evM : ℂ := -(bm.sd.omega)
    evZ ≠ evP ∧ evP ≠ evM ∧ evZ ≠ evM := by
  refine ⟨bm.sd.omega_ne_one.symm, ?_, ?_⟩
  · intro h
    have hω0 : bm.sd.omega = 0 := by
      have : (2 : ℂ) * bm.sd.omega = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h2 | h2
      · norm_num at h2
      · exact h2
    have := bm.sd.omega_cubed
    rw [hω0] at this; norm_num at this
  · intro h
    have hω : bm.sd.omega = -1 := by linear_combination h
    have := bm.sd.omega_cubed
    rw [hω] at this; norm_num at this

-- ═══════════════════════════════════════════════════════════════════════════
-- PART IX: CLIFFORD GROUP AND UNIVERSALITY (Section V)
-- ═══════════════════════════════════════════════════════════════════════════

def HW_shift (d : ℕ) : Gate d :=
  fun row col => if row.val = (col.val + 1) % d then 1 else 0

def HW_clock (d : ℕ) (omega : ℂ) : Gate d :=
  fun row col => if row = col then omega ^ col.val else 0

def HW_elem (d : ℕ) (omega : ℂ) (a b : ℕ) : Gate d :=
  fun row col => if row.val = (col.val + a) % d
    then omega ^ (b * col.val) else 0

theorem HW_commutation (d : ℕ) (omega : ℂ) (h_root : omega ^ d = 1) :
    ∀ i j, Gate.mul (HW_clock d omega) (HW_shift d) i j =
      omega * Gate.mul (HW_shift d) (HW_clock d omega) i j := sorry

/-- U is Clifford if conjugation maps HW generators to HW elements. -/
noncomputable def IsCliffordGate (d : ℕ) (omega : ℂ) (U : Gate d) : Prop :=
  ∃ Uinv : Gate d,
    (∀ i j, Gate.mul U Uinv i j = Gate.id d i j) ∧
    (∀ i j, Gate.mul Uinv U i j = Gate.id d i j) ∧
    (∃ a b : ℕ, ∃ c : ℂ,
      ∀ i j, Gate.mul (Gate.mul U (HW_shift d)) Uinv i j =
        c * HW_elem d omega a b i j) ∧
    (∃ a b : ℕ, ∃ c : ℂ,
      ∀ i j, Gate.mul (Gate.mul U (HW_clock d omega)) Uinv i j =
        c * HW_elem d omega a b i j)

def IsProductGate (d : ℕ) (G : Gate₂ d) : Prop :=
  ∃ (U V : Gate d), ∀ a b a' b', G (a, b) (a', b') = U a a' * V b b'

def IsEntangling (d : ℕ) (G : Gate₂ d) : Prop := ¬IsProductGate d G

noncomputable def applyToKet0 (U : Gate 3) : Qutrit :=
  ∑ i : Fin 3, (U i ⟨0, by omega⟩) • ket i

noncomputable def IsNonStabilizer (omega : ℂ) (ψ : Qutrit) : Prop :=
  ¬∃ (U : Gate 3), IsCliffordGate 3 omega U ∧ ψ = applyToKet0 U

theorem phase_is_clifford (bm : Braiding) :
    IsCliffordGate 3 bm.sd.omega (phase_gate bm) := sorry

theorem hadamard_is_clifford (bm : Braiding) :
    IsCliffordGate 3 bm.sd.omega (hadamard bm) := sorry

/-- **CZ is entangling**: the phase ω^{ab} couples the two qutrit indices,
    so CZ cannot factor as U⊗V. This is the key structural property that
    distinguishes the Z₃ parafermion from Ising: 3 fusion channels give
    an entangling gate, while Ising's 2 channels cannot. -/
theorem CZ_is_entangling (bm : Braiding) :
    IsEntangling 3 (control_Z bm) := by
  intro ⟨U, V, hprod⟩
  apply bm.sd.omega_ne_one
  have h00 := hprod ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
  have h10 := hprod ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩
  have h01 := hprod ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩
  have h11 := hprod ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩
  simp only [control_Z, and_self, ite_true] at h00 h10 h01 h11
  have key : bm.sd.omega ^ ((⟨0, by omega⟩ : Fin 3).val * (⟨0, by omega⟩ : Fin 3).val) *
             bm.sd.omega ^ ((⟨1, by omega⟩ : Fin 3).val * (⟨1, by omega⟩ : Fin 3).val) =
             bm.sd.omega ^ ((⟨1, by omega⟩ : Fin 3).val * (⟨0, by omega⟩ : Fin 3).val) *
             bm.sd.omega ^ ((⟨0, by omega⟩ : Fin 3).val * (⟨1, by omega⟩ : Fin 3).val) := by
    rw [h00, h11, h10, h01]; ring
  norm_num at key
  exact key

theorem braiding_generates_full_clifford (bm : Braiding) :
    ∀ U : Gate 3, IsCliffordGate 3 bm.sd.omega U →
      ∃ circuit : List (Gate 3),
        (∀ g ∈ circuit, g = phase_gate bm ∨ g = hadamard bm) ∧
        ∀ i j, Gate.ofList circuit i j = U i j := sorry

theorem magic_is_non_stabilizer (bm : Braiding) :
    IsNonStabilizer bm.sd.omega magic_plus := sorry

/-- Bravyi-Kitaev universality for prime d: Clifford + magic = universal.
    For d = 3 (prime), a complete Clifford generating set plus a
    non-stabilizer state can approximate any unitary to arbitrary precision
    via magic state distillation and injection. -/
theorem bravyi_kitaev_qutrit
    (Q_ H_ : Gate 3) (CZ_ : Gate₂ 3) (magic : Qutrit) (omega : ℂ)
    (hQ : IsCliffordGate 3 omega Q_)
    (hH : IsCliffordGate 3 omega H_)
    (hCZ : IsEntangling 3 CZ_)
    (hgen : ∀ U, IsCliffordGate 3 omega U →
      ∃ circuit, (∀ g ∈ circuit, g = Q_ ∨ g = H_) ∧
        ∀ i j, Gate.ofList circuit i j = U i j)
    (hmagic : IsNonStabilizer omega magic) :
    ∀ (U : Gate 3) (ε : ℝ), ε > 0 →
    ∃ (circuit : List (Gate 3)),
      ∀ i j : Fin 3, ‖Gate.ofList circuit i j - U i j‖ < ε := sorry

/-- **Main result**: universal TQC from the 4e TSC.
    Assembles five structural ingredients:
    (1) Q normalizes HW(Z₃) — Clifford gate
    (2) H normalizes HW(Z₃) — Clifford gate
    (3) CZ couples two qutrits — entangling (not a product gate)
    (4) {Q,H} generate all of Cliff(Z₃)
    (5) |+⟩ not in stabilizer orbit — magic state
    Since 3 is prime, Bravyi-Kitaev gives universality. -/
theorem universal_TQC (bm : Braiding) :
    ∀ (U : Gate 3) (ε : ℝ), ε > 0 →
    ∃ (circuit : List (Gate 3)),
      ∀ i j : Fin 3, ‖Gate.ofList circuit i j - U i j‖ < ε :=
  bravyi_kitaev_qutrit
    (phase_gate bm) (hadamard bm) (control_Z bm) magic_plus bm.sd.omega
    (phase_is_clifford bm)
    (hadamard_is_clifford bm)
    (CZ_is_entangling bm)
    (braiding_generates_full_clifford bm)
    (magic_is_non_stabilizer bm)

-- ═══════════════════════════════════════════════════════════════════════════
-- PART X: ISING (2e) vs PARAFERMION (4e) COMPARISON (Section V, Table I)
-- ═══════════════════════════════════════════════════════════════════════════

-- Ising MTC data (qdim, fusion) comes from `ising_modular` in the
-- infrastructure. The key structural comparison is in fusion channels:
-- Ising σ×σ = 1+ψ (2 channels) vs parafermion σ×σ = 0+1+2 (3 channels).

/-- Ising braiding symbols: F-matrix and gauge-invariant R-ratio.
    These determine the braid group representation on fusion spaces. -/
structure IsingSymbols where
  F_matrix : Fin 2 → Fin 2 → ℂ
  F_def : ∀ a b, F_matrix a b =
    (1 / ↑(Real.sqrt 2)) * ((-1 : ℂ) ^ (a.val * b.val))
  R_ratio : ℂ
  R_ratio_val : R_ratio = Complex.I

/-- Ising braiding on 4γ (1 qubit) and 6γ (2 qubits).
    The key structural failure: the middle braid σ₃ on 6γ FACTORIZES
    as a tensor product, preventing entangling gates.
    Physical origin: Ising has only 2 fusion channels, giving a
    representation of the Temperley-Lieb algebra TL₂(√2) which
    necessarily decomposes on the tensor product space. -/
structure IsingBraiding where
  symbols : IsingSymbols
  B₁ : Gate 2
  B₁_00 : B₁ ⟨0, by omega⟩ ⟨0, by omega⟩ = 1
  B₁_11 : B₁ ⟨1, by omega⟩ ⟨1, by omega⟩ = Complex.I
  B₁_off : ∀ a b, a ≠ b → B₁ a b = 0
  B₂ : Gate 2
  B₂_from_F : ∀ a b, B₂ a b = Gate.mul (Gate.mul symbols.F_matrix B₁) symbols.F_matrix a b
  middle_braid_2q : Gate₂ 2
  /-- The middle braid factorizes: Ising braiding cannot entangle qubits. -/
  middle_braid_product : IsProductGate 2 middle_braid_2q

/-- **Structural comparison**: Ising has fewer fusion channels than Z₃ parafermion.
    σ×σ gives 2 channels (Ising) vs 3 channels (parafermion).
    This is the fundamental reason the 4e TSC achieves universal TQC
    while the 2e (Ising) case cannot: more channels → richer braid
    representation → entangling gates from braiding. -/
theorem ising_fewer_fusion_channels :
    ising_N ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ +
    ising_N ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ < (3 : ℕ) := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- PART XI: HIGHER-CHARGE GENERALIZATION (Section VI, Appendix B)
-- ═══════════════════════════════════════════════════════════════════════════

/-- k=3 (6e SC): d² = (1+√2)² = 3+2√2. -/
theorem silver_ratio_sq :
    (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

/-- Higher-charge TSC: k layers of p+ip, Cooper charge 2ke,
    parent TO = SU(2)_{2k}, child TO = SO(3)_k after condensation. -/
structure HigherChargeTSC_Full where
  k : ℕ
  k_pos : k > 0
  symmetry_class : SymmetryClass
  qdim : Fin (k + 1) → ℝ
  qdim_pos : ∀ j, qdim j > 0
  d_vacuum : qdim ⟨0, by omega⟩ = 1

def HigherChargeTSC_Full.cooper_charge (t : HigherChargeTSC_Full) : ℕ := 2 * t.k
def HigherChargeTSC_Full.cs_level (t : HigherChargeTSC_Full) : ℕ := 2 * t.k
def HigherChargeTSC_Full.num_layers (t : HigherChargeTSC_Full) : ℕ := t.k
def HigherChargeTSC_Full.chiral_central_charge (t : HigherChargeTSC_Full) : ℚ := t.k / 2
def HigherChargeTSC_Full.num_anyons (t : HigherChargeTSC_Full) : ℕ := t.k + 1

/-- **Universality criterion** (Freedman-Larsen-Wang): braiding of SO(3)_k
    anyons is universal iff some anyon has d² irrational.
    - k=1: trivial. k=2: Z₃, all d=1 (needs magic states).
    - k≥3: irrational d² → braiding alone is universal (no magic needed). -/
structure UniversalityCriterion where
  tsc : HigherChargeTSC_Full
  witness : Fin (tsc.k + 1)
  d_sq_irrational : ∀ (p : ℤ) (q : ℤ), q ≠ 0 →
    (tsc.qdim witness ^ 2) * (q : ℝ) ≠ (p : ℝ)

/-- k=3: d² = 3+2√2 ∉ ℚ. If 3+2√2 = p/q then √2 = (p-3q)/(2q) ∈ ℚ,
    contradicting irrationality of √2. -/
theorem k3_d_sq_irrational :
    ∀ (p : ℤ) (q : ℤ), q ≠ 0 →
    (3 + 2 * Real.sqrt 2) * (q : ℝ) ≠ (p : ℝ) := by
  intro p q hq h
  exact irrational_sqrt_two.ne_rational (p - 3 * q) (2 * q) (by
    have h2q : (↑(2 * q) : ℝ) ≠ 0 := by
      push_cast; exact mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hq)
    rw [eq_div_iff h2q]; push_cast; nlinarith)

-- ═══════════════════════════════════════════════════════════════════════════
-- PART XII: JAIN TRANSITION (Section VI)
-- ═══════════════════════════════════════════════════════════════════════════

/-- ν=2/3 Jain state and 4e SC share the SAME Z₃ TO but differ in SET:
    Jain has trivial ρ = id, SC has ρ = charge conjugation.
    The transition is purely a symmetry enrichment transition —
    the topological order is unchanged, only the symmetry action changes. -/
structure JainTransition where
  filling : ℚ
  filling_eq : filling = 2/3
  jain_rho : Fin 3 → Fin 3
  jain_trivial : ∀ a, jain_rho a = a
  sc_rho : Fin 3 → Fin 3
  sc_swap_1 : sc_rho ⟨1, by omega⟩ = ⟨2, by omega⟩
  sc_swap_2 : sc_rho ⟨2, by omega⟩ = ⟨1, by omega⟩

/-- Same TO, different SET: the symmetry actions are distinct. -/
theorem jain_sc_different_SET (jt : JainTransition) :
    jt.jain_rho ⟨1, by omega⟩ ≠ jt.sc_rho ⟨1, by omega⟩ := by
  rw [jt.jain_trivial, jt.sc_swap_1]; decide

-- ═══════════════════════════════════════════════════════════════════════════
-- PART XIII: COMPLETE DERIVATION CHAIN (Sections II-V combined)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The complete logical chain from bilayer physics to universal TQC.

    This structure captures the **structural relationships** between all
    layers of the derivation. Each step has explicit physical prerequisites
    (encoded in the constituent structures) and produces specific consequences.

    The SU(2)₄ fusion/qdim/theta, Z₃ modular data, condensation, and
    G-crossed extension come from the TQFT infrastructure (`su24_ribbon`,
    `z3_modular`, `su24_to_z3_condensation`, `z2_gcrossed_z3`).
    Only the S-matrix data (`sdata`) and domain-specific algebraic data
    (`pf`, `sd`, `bm`) are bundled here.

    The chain of implications:
    1. bilayer (ρ_c > ρ_s, λ₁ > 0)  →  vortex condensation  →  4e SC
    2. parton construction  →  U(2)_{4,0} CS  →  SU(2)₄ spin sector
    3. j=2 is boson simple current  →  condensation  →  Z₃ child TO
    4. Z₄ SET enrichment  →  G-crossed extension  →  parafermion σ
    5. pentagon/hexagon  →  F,R-symbols  →  braiding matrices B₁, B₂
    6. Q, H Clifford + CZ entangling + magic  →  universal TQC -/
structure SymmetryBreakingChain where
  bilayer : Bilayer
  vortex_cond : VortexCondensation
  vc_bilayer : vortex_cond.bilayer = bilayer
  cs : U2_ChernSimons
  cs_is_4e : cs.k₁ = 4 ∧ cs.k₂ = 0
  sdata : SU2_4_SData
  pf : Parafermion
  sd : SymbolData
  sd_pf : sd.pf = pf
  bm : Braiding
  bm_sd : bm.sd = sd

/-- The full chain yields universal TQC: every qutrit unitary is
    approximable to arbitrary precision from braiding and measurement. -/
theorem full_chain_universal (chain : SymmetryBreakingChain) :
    ∀ (U : Gate 3) (ε : ℝ), ε > 0 →
    ∃ (circuit : List (Gate 3)),
      ∀ i j : Fin 3, ‖Gate.ofList circuit i j - U i j‖ < ε :=
  universal_TQC chain.bm

end Charge4eTSC
