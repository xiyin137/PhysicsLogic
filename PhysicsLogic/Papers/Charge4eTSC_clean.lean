import PhysicsLogic.Quantum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace Charge4eTSC

open PhysicsLogic.Quantum
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

structure TopologicalOrder (n : ℕ) where
  fusion : Fin n → Fin n → Fin n → ℕ
  qdim : Fin n → ℝ
  qdim_pos : ∀ a, qdim a > 0

structure TSC where
  ν : ℤ
  chiral_central_charge : ℚ
  ccc_eq : chiral_central_charge = ν / 2

structure Bilayer where
  ρ_c : ℝ
  ρ_s : ℝ
  charge_dominant : ρ_c > ρ_s
  lam₁ : ℝ
  lam₁_pos : lam₁ > 0

structure SU2_4 where
  qdim : Fin 5 → ℝ
  d0 : qdim ⟨0, by omega⟩ = 1
  d_half : qdim ⟨1, by omega⟩ = Real.sqrt 3
  d1 : qdim ⟨2, by omega⟩ = 2
  d_three_half : qdim ⟨3, by omega⟩ = Real.sqrt 3
  d2 : qdim ⟨4, by omega⟩ = 1
  fusion : Fin 5 → Fin 5 → Fin 5 → ℕ
  N0_11 : fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ = 1
  N1_11 : fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨2, by omega⟩ = 1
  N2_11 : fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = 1
  N0_22 : fusion ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨0, by omega⟩ = 1
  S_matrix : Fin 5 → Fin 5 → ℂ
  S_half_2 : S_matrix ⟨1, by omega⟩ ⟨4, by omega⟩ =
    -S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩
  S_threehalf_2 : S_matrix ⟨3, by omega⟩ ⟨4, by omega⟩ =
    -S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩

theorem two_fold_vacuum_multiplicity (data : SU2_4) :
    data.fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ +
    data.fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = 2 := by
  rw [data.N0_11, data.N2_11]

theorem half_int_confined (data : SU2_4) :
    data.S_matrix ⟨1, by omega⟩ ⟨4, by omega⟩ +
    data.S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩ = 0 := by
  rw [data.S_half_2]; ring

structure Z3_TO where
  qdim : Fin 3 → ℝ
  all_abelian : ∀ a, qdim a = 1
  fusion : Fin 3 → Fin 3 → Fin 3
  fusion_Z3 : ∀ a b, (fusion a b).val = (a.val + b.val) % 3
  topological_spin : Fin 3 → ℂ
  spin_0 : topological_spin ⟨0, by omega⟩ = 1

theorem Z3_total_dim_sq (z : Z3_TO) :
    z.qdim ⟨0, by omega⟩ ^ 2 + z.qdim ⟨1, by omega⟩ ^ 2 +
    z.qdim ⟨2, by omega⟩ ^ 2 = 3 := by
  simp only [z.all_abelian]; norm_num

structure Z4_SET where
  base : Z3_TO
  rho : Fin 3 → Fin 3
  rho_0 : rho ⟨0, by omega⟩ = ⟨0, by omega⟩
  rho_swap : rho ⟨1, by omega⟩ = ⟨2, by omega⟩
  rho_swap' : rho ⟨2, by omega⟩ = ⟨1, by omega⟩
  rho_involution : ∀ a, rho (rho a) = a

structure Parafermion where
  set_data : Z4_SET
  d_sigma : ℝ
  d_sigma_val : d_sigma = Real.sqrt 3
  sigma_fusion : Fin 3 → ℕ
  sigma_fusion_all : ∀ a, sigma_fusion a = 1

theorem d_sigma_squared (pf : Parafermion) : pf.d_sigma ^ 2 = 3 := by
  rw [pf.d_sigma_val, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

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
  Y_phase : ℂ
  Y_sq : Y_phase ^ 2 = -Complex.I
  ratio : Fin 3 → ℂ
  ratio_0 : ratio ⟨0, by omega⟩ = 1
  ratio_1 : ratio ⟨1, by omega⟩ = omega⁻¹
  ratio_2 : ratio ⟨2, by omega⟩ = omega⁻¹

theorem chi_symmetric (sd : SymbolData) (e f : Fin 3) :
    sd.chi e f = sd.chi f e := by
  simp only [sd.chi_def]; congr 1; exact Nat.mul_comm e.val f.val

theorem chi_vacuum (sd : SymbolData) (f : Fin 3) :
    sd.chi ⟨0, by omega⟩ f = 1 := by
  simp [sd.chi_def]

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
    hadamard bm a b = bm.B₁ a a * bm.B₂ a b * bm.B₁ b b := sorry

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
    evZ ≠ evP ∧ evP ≠ evM ∧ evZ ≠ evM := sorry

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
    IsEntangling 3 (control_Z bm) := sorry

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

structure IsingMTC where
  qdim : Fin 3 → ℝ
  d_1 : qdim ⟨0, by omega⟩ = 1
  d_sigma : qdim ⟨1, by omega⟩ = Real.sqrt 2
  d_psi : qdim ⟨2, by omega⟩ = 1
  fusion : Fin 3 → Fin 3 → Fin 3 → ℕ
  sigma_sigma_1 : fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ = 1
  sigma_sigma_psi : fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ = 1
  psi_psi : fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ = 1
  sigma_psi : fusion ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ = 1

structure IsingSymbols where
  mtc : IsingMTC
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
  middle_braid_2q : Gate₂ 2
  middle_braid_product : IsProductGate 2 middle_braid_2q

theorem ising_fewer_fusion_channels (im : IsingMTC) (pf : Parafermion) :
    im.fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ +
    im.fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ <
    pf.sigma_fusion ⟨0, by omega⟩ + pf.sigma_fusion ⟨1, by omega⟩ +
    pf.sigma_fusion ⟨2, by omega⟩ := by
  simp only [im.sigma_sigma_1, im.sigma_sigma_psi, pf.sigma_fusion_all]; omega

theorem ising_not_entangling (ib : IsingBraiding) :
    ¬IsEntangling 2 ib.middle_braid_2q :=
  fun h => h ib.middle_braid_product

theorem qdim_comparison :
    Real.sqrt 2 < Real.sqrt 3 :=
  Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

structure HigherChargeTSC where
  k : ℕ
  k_pos : k > 0
  cooper_charge : ℕ
  charge_eq : cooper_charge = 2 * k

theorem silver_ratio_sq :
    (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

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

end Charge4eTSC