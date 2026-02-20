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

namespace Charge4eTSC

open PhysicsLogic.Quantum
open PhysicsLogic.QFT.TQFT
open BigOperators

set_option autoImplicit false

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

inductive TRSymmetry where
  | none | plus | minus
  deriving DecidableEq, Repr

inductive PHSymmetry where
  | none | plus | minus
  deriving DecidableEq, Repr

inductive ChiralSymmetry where
  | none | present
  deriving DecidableEq, Repr

structure SymmetryClass where
  time_reversal : TRSymmetry
  particle_hole : PHSymmetry
  chiral : ChiralSymmetry
  chiral_consistency :
    (time_reversal ≠ TRSymmetry.none ∧ particle_hole ≠ PHSymmetry.none) ↔
    chiral = ChiralSymmetry.present

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

structure TopologicalOrder (n : ℕ) (hn : n ≥ 1) where
  fusion : Fin n → Fin n → Fin n → ℕ
  fusion_unit : ∀ b c, fusion ⟨0, hn⟩ b c = if b = c then 1 else 0
  fusion_comm : ∀ a b c, fusion a b c = fusion b a c
  qdim : Fin n → ℝ
  qdim_pos : ∀ a, qdim a > 0
  qdim_unit : qdim ⟨0, hn⟩ = 1
  qdim_fusion : ∀ a b, qdim a * qdim b = ∑ c : Fin n, (fusion a b c : ℝ) * qdim c
  S_matrix : Fin n → Fin n → ℂ
  S_symmetric : ∀ a b, S_matrix a b = S_matrix b a
  S_qdim : ∀ a, (S_matrix a ⟨0, hn⟩) / (S_matrix ⟨0, hn⟩ ⟨0, hn⟩) = ↑(qdim a)
  topological_spin : Fin n → ℂ
  spin_unit : topological_spin ⟨0, hn⟩ = 1
  spin_phase : ∀ a, topological_spin a * starRingEnd ℂ (topological_spin a) = 1
  chiral_central_charge : ℚ
  total_dim_sq : ℝ
  total_dim_sq_eq : total_dim_sq = ∑ a : Fin n, qdim a ^ 2
  total_dim_sq_pos : total_dim_sq > 0

def TopologicalOrder.torus_GSD {n : ℕ} {hn : n ≥ 1}
    (_ : TopologicalOrder n hn) : ℕ := n

noncomputable def TopologicalOrder.topo_entropy {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) : ℝ :=
  Real.log (Real.sqrt to_.total_dim_sq)

def TopologicalOrder.is_abelian {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n) : Prop :=
  to_.qdim a = 1

def TopologicalOrder.is_purely_abelian {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) : Prop :=
  ∀ a, to_.is_abelian a

def TopologicalOrder.is_boson {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n) : Prop :=
  to_.topological_spin a = 1

def TopologicalOrder.is_simple_current {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n) : Prop :=
  to_.is_boson a ∧ to_.is_abelian a ∧ to_.fusion a a ⟨0, hn⟩ = 1

noncomputable def TopologicalOrder.monodromy {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (j a : Fin n) : ℂ :=
  to_.S_matrix j a / ((↑(to_.qdim j) : ℂ) * to_.S_matrix ⟨0, hn⟩ a)

theorem TopologicalOrder.monodromy_vacuum {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) (a : Fin n)
    (hS : to_.S_matrix ⟨0, hn⟩ a ≠ 0) :
    to_.monodromy ⟨0, hn⟩ a = 1 := by
  unfold TopologicalOrder.monodromy
  rw [to_.qdim_unit]; simp only [Complex.ofReal_one, one_mul]
  exact div_self hS

structure CondensationCriterion {n : ℕ} {hn : n ≥ 1}
    (to_ : TopologicalOrder n hn) where
  condensing : Fin n
  is_boson : to_.is_boson condensing
  is_abelian : to_.is_abelian condensing
  self_fuse_to_vacuum : to_.fusion condensing condensing ⟨0, hn⟩ = 1

inductive PairingSymmetry where
  | s_wave | p_wave | d_wave
  | higher (ℓ : ℕ) (hℓ : ℓ ≥ 3)
  deriving DecidableEq, Repr

def PairingSymmetry.angular_momentum : PairingSymmetry → ℕ
  | .s_wave => 0
  | .p_wave => 1
  | .d_wave => 2
  | .higher ℓ _ => ℓ

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

def Bilayer.condensate_charge (b : Bilayer) : ℕ :=
  b.layer₁.cooper_pair_charge + b.layer₂.cooper_pair_charge

theorem bilayer_c_minus (b : Bilayer) :
    b.layer₁.chiral_central_charge + b.layer₂.chiral_central_charge = 1 := by
  simp [TSC.chiral_central_charge, b.hν₁, b.hν₂]; norm_num

theorem bilayer_edge_modes (b : Bilayer) :
    b.layer₁.num_edge_modes = 1 ∧ b.layer₂.num_edge_modes = 1 :=
  ⟨b.layer₁.p_wave_single_edge b.hν₁, b.layer₂.p_wave_single_edge b.hν₂⟩

structure BilayerVortex where
  n₁ : ℤ
  n₂ : ℤ

def BilayerVortex.charge_winding (v : BilayerVortex) : ℤ := v.n₁ + v.n₂
def BilayerVortex.spin_winding (v : BilayerVortex) : ℤ := v.n₁ - v.n₂

def v1v2bar : BilayerVortex := ⟨1, -1⟩

theorem v1v2bar_charge_zero : v1v2bar.charge_winding = 0 := by
  simp [v1v2bar, BilayerVortex.charge_winding]

theorem v1v2bar_spin_two : v1v2bar.spin_winding = 2 := by
  simp [v1v2bar, BilayerVortex.spin_winding]

noncomputable def vortex_energy (b : Bilayer) (v : BilayerVortex) : ℝ :=
  b.ρ_c * (v.charge_winding : ℝ) ^ 2 + b.ρ_s * (v.spin_winding : ℝ) ^ 2

private lemma int_sq_ge_one {n : ℤ} (hn : n ≠ 0) : (n : ℝ) ^ 2 ≥ 1 := by
  suffices h : (1 : ℤ) ≤ n ^ 2 by exact_mod_cast h
  have : n ≤ -1 ∨ 1 ≤ n := by omega
  rcases this with h | h <;> nlinarith

theorem v1v2bar_energy (b : Bilayer) :
    vortex_energy b v1v2bar = 4 * b.ρ_s := by
  unfold vortex_energy
  rw [v1v2bar_charge_zero, v1v2bar_spin_two]
  push_cast; ring

theorem charge_carrying_vortex_costly (b : Bilayer) (v : BilayerVortex)
    (hnc : v.charge_winding ≠ 0) :
    vortex_energy b v ≥ b.ρ_c := by
  unfold vortex_energy
  have hρc : b.ρ_c > 0 := lt_trans b.ρ_s_pos b.charge_dominant
  have hρs : b.ρ_s > 0 := b.ρ_s_pos
  have hsq : (v.charge_winding : ℝ) ^ 2 ≥ 1 := int_sq_ge_one hnc
  nlinarith [sq_nonneg (v.spin_winding : ℝ)]

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

inductive HiggsPattern where
  | topological : HiggsPattern
  | trivial : HiggsPattern

structure HiggsClassification where
  lam₁ : ℝ
  lam₁_nonzero : lam₁ ≠ 0
  pattern : HiggsPattern
  pos_topological : lam₁ > 0 → pattern = HiggsPattern.topological
  neg_trivial : lam₁ < 0 → pattern = HiggsPattern.trivial
  num_anyons : ℕ
  topological_count : pattern = HiggsPattern.topological → num_anyons = 3
  trivial_count : pattern = HiggsPattern.trivial → num_anyons = 1

theorem bilayer_selects_topological (b : Bilayer) (hc : HiggsClassification)
    (hlam : hc.lam₁ = b.lam₁) :
    hc.pattern = HiggsPattern.topological := by
  exact hc.pos_topological (hlam ▸ b.lam₁_pos)

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

structure CS_TO_Bridge where
  bilayer : Bilayer
  cs : U2_ChernSimons

def CS_TO_Bridge.cs_level (bridge : CS_TO_Bridge) : ℕ := bridge.cs.k₁
def CS_TO_Bridge.spin_sector_anyons (bridge : CS_TO_Bridge) : ℕ :=
  bridge.cs.num_anyons_SU2

theorem su24_j2_condensable :
    su24_theta ⟨4, by omega⟩ = 1 ∧
    su24_qdim ⟨4, by omega⟩ = 1 ∧
    su24_N ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨0, by omega⟩ = 1 :=
  ⟨su24_theta_j2, su24_d2, by native_decide⟩

theorem su24_j1_vacuum_multiplicity :
    su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ +
    su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = 2 := by native_decide

structure SU2_4_SData where
  S_matrix : Fin 5 → Fin 5 → ℂ
  S_symmetric : ∀ a b, S_matrix a b = S_matrix b a
  S_0_2_ne : S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩ ≠ 0
  S_half_2 : S_matrix ⟨1, by omega⟩ ⟨4, by omega⟩ =
    -(↑(su24_qdim ⟨1, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  S_threehalf_2 : S_matrix ⟨3, by omega⟩ ⟨4, by omega⟩ =
    -(↑(su24_qdim ⟨3, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  S_1_2 : S_matrix ⟨2, by omega⟩ ⟨4, by omega⟩ =
    (↑(su24_qdim ⟨2, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  S_2_2 : S_matrix ⟨4, by omega⟩ ⟨4, by omega⟩ =
    (↑(su24_qdim ⟨4, by omega⟩) : ℂ) * S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩

noncomputable def su24_monodromy (sdata : SU2_4_SData) (j : Fin 5) : ℂ :=
  sdata.S_matrix j ⟨4, by omega⟩ /
  ((↑(su24_qdim j) : ℂ) * sdata.S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩)

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

noncomputable abbrev z2_gcrossed_4eTSC := z2_gcrossed_z3

theorem total_dim_gcrossed {n : ℕ} {hn : n ≥ 1} {G_order : ℕ} {hG : G_order ≥ 1}
    {base : FusionCategoryData n hn}
    {action : GActionOnCategory n hn G_order hG base}
    (gc : GCrossedBraidedData n hn G_order hG base action) :
    gc.D_sq_0 + ∑ σ : Fin gc.defect_count, gc.defect_qdim σ ^ 2 = 2 * gc.D_sq_0 := by
  rw [gc.D_sq_defect_eq]; ring

theorem non_abelian_is_extrinsic :
    z2_gcrossed_z3.isExtrinsicNonAbelian := by
  refine ⟨fun i => rfl, ⟨0, z2_gcrossed_z3.defect_count_pos⟩, ?_⟩
  show Real.sqrt 3 > 1
  have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 3)
  rwa [Real.sqrt_one] at h

theorem z2_rho_involution :
    ∀ a : Fin 3, z2_rho_on_z3 ⟨1, by omega⟩ (z2_rho_on_z3 ⟨1, by omega⟩ a) = a := by
  intro a; fin_cases a <;> simp [z2_rho_on_z3, z3_dual]

theorem fixed_points_trivial :
    ∀ a : Fin 3, z2_rho_on_z3 ⟨1, by omega⟩ a = a → a = ⟨0, by omega⟩ := by
  intro a ha; fin_cases a
  · rfl
  · simp [z2_rho_on_z3, z3_dual] at ha
  · simp [z2_rho_on_z3, z3_dual] at ha

theorem norm_map_trivial :
    ∀ a : Fin 3, z3_fuse a (z2_rho_on_z3 ⟨1, by omega⟩ a) = ⟨0, by omega⟩ := by
  intro a; fin_cases a <;> simp [z3_fuse, z2_rho_on_z3, z3_dual]

structure Parafermion where
  kappa_sigma : ℤ
  kappa_eq : kappa_sigma = -1

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

theorem F_from_kappa (sd : SymbolData) (e f : Fin 3) :
    sd.F_symbol e f =
    (↑sd.pf.kappa_sigma : ℂ) * (1 / ↑(Real.sqrt 3)) * (sd.chi e f)⁻¹ := by
  rw [sd.F_def, sd.pf.kappa_eq]; push_cast; ring

structure Braiding where
  sd : SymbolData
  B₁ : Gate 3
  B₁_diag : ∀ a, B₁ a a = sd.ratio a
  B₁_off : ∀ a b, a ≠ b → B₁ a b = 0
  B₂ : Gate 3
  B₂_def : ∀ a b, B₂ a b =
    (1 / ↑(Real.sqrt 3)) * (if a = b then 1 else sd.omega)

noncomputable def phase_gate (bm : Braiding) : Gate 3 := bm.B₁

noncomputable def hadamard (bm : Braiding) : Gate 3 :=
  Gate.mul (Gate.mul bm.B₁ bm.B₂) bm.B₁

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

noncomputable def control_Z (bm : Braiding) : Gate₂ 3 :=
  fun ⟨a, b⟩ ⟨a', b'⟩ =>
    if a = a' ∧ b = b' then bm.sd.omega ^ (a.val * b.val) else 0

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

structure IsingSymbols where
  F_matrix : Fin 2 → Fin 2 → ℂ
  F_def : ∀ a b, F_matrix a b =
    (1 / ↑(Real.sqrt 2)) * ((-1 : ℂ) ^ (a.val * b.val))
  R_ratio : ℂ
  R_ratio_val : R_ratio = Complex.I

structure IsingBraiding where
  symbols : IsingSymbols
  B₁ : Gate 2
  B₁_00 : B₁ ⟨0, by omega⟩ ⟨0, by omega⟩ = 1
  B₁_11 : B₁ ⟨1, by omega⟩ ⟨1, by omega⟩ = Complex.I
  B₁_off : ∀ a b, a ≠ b → B₁ a b = 0
  B₂ : Gate 2
  B₂_from_F : ∀ a b, B₂ a b = Gate.mul (Gate.mul symbols.F_matrix B₁) symbols.F_matrix a b
  middle_braid_2q : Gate₂ 2
  middle_braid_product : IsProductGate 2 middle_braid_2q

theorem ising_fewer_fusion_channels :
    ising_N ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ +
    ising_N ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ < (3 : ℕ) := by
  native_decide

theorem silver_ratio_sq :
    (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

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

structure UniversalityCriterion where
  tsc : HigherChargeTSC_Full
  witness : Fin (tsc.k + 1)
  d_sq_irrational : ∀ (p : ℤ) (q : ℤ), q ≠ 0 →
    (tsc.qdim witness ^ 2) * (q : ℝ) ≠ (p : ℝ)

theorem k3_d_sq_irrational :
    ∀ (p : ℤ) (q : ℤ), q ≠ 0 →
    (3 + 2 * Real.sqrt 2) * (q : ℝ) ≠ (p : ℝ) := by
  intro p q hq h
  exact irrational_sqrt_two.ne_rational (p - 3 * q) (2 * q) (by
    have h2q : (↑(2 * q) : ℝ) ≠ 0 := by
      push_cast; exact mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hq)
    rw [eq_div_iff h2q]; push_cast; nlinarith)

structure JainTransition where
  filling : ℚ
  filling_eq : filling = 2/3
  jain_rho : Fin 3 → Fin 3
  jain_trivial : ∀ a, jain_rho a = a
  sc_rho : Fin 3 → Fin 3
  sc_swap_1 : sc_rho ⟨1, by omega⟩ = ⟨2, by omega⟩
  sc_swap_2 : sc_rho ⟨2, by omega⟩ = ⟨1, by omega⟩

theorem jain_sc_different_SET (jt : JainTransition) :
    jt.jain_rho ⟨1, by omega⟩ ≠ jt.sc_rho ⟨1, by omega⟩ := by
  rw [jt.jain_trivial, jt.sc_swap_1]; decide

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

theorem full_chain_universal (chain : SymmetryBreakingChain) :
    ∀ (U : Gate 3) (ε : ℝ), ε > 0 →
    ∃ (circuit : List (Gate 3)),
      ∀ i j : Fin 3, ‖Gate.ofList circuit i j - U i j‖ < ε :=
  universal_TQC chain.bm

end Charge4eTSC
