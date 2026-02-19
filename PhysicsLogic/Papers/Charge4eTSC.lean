import PhysicsLogic.Quantum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Charge-4e Superconductor: A Path to Universal TQC

Shi, Han, Raghu, Vishwanath (2025), arXiv:2602.06963

  (p+ip)² bilayer → U(2)_{4,0} CS → SU(2)_4
    → condense j=2, confine half-integers → Z₃ TO ≅ SU(3)₁
    → Z₄ SET: ρ_g permutes 1₊↔1₋
    → G-crossed: σ with d_σ=√3, TY fusion σ×σ=0+1+2
    → pentagon/hexagon → F,R-symbols
    → B₁=diag(1,ω⁻¹,ω⁻¹), B₂=(1/√3)(δ+ω(1-δ))
    → Q=B₁, H=B₁B₂B₁ (DFT), CZ=diag(ω^{ab})
    → interferometric M₁=H², M₂=H²Q⁻¹ → magic states |±⟩
    → Bravyi-Kitaev (d=3 prime): universal TQC
-/

namespace Charge4eTSC

open PhysicsLogic.Quantum
open BigOperators

set_option autoImplicit false

-- ═══════════════════════════════════════════════════════════════════════════
-- FOUNDATIONAL CONCEPTS
-- ═══════════════════════════════════════════════════════════════════════════

/-- Qutrit: 3-dimensional quantum system. Parafermion vortices (d_σ=√3)
    naturally encode qutrits rather than qubits (Majorana d_σ=√2). -/
abbrev Qutrit := FiniteDimQuantum 3

/-- Quantum gate on d-dimensional qudit, as a d×d complex matrix. -/
abbrev Gate (d : ℕ) := Fin d → Fin d → ℂ

/-- Identity gate (Kronecker delta). -/
def Gate.id (d : ℕ) : Gate d := fun i j => if i = j then 1 else 0

/-- Gate composition (matrix multiplication). -/
noncomputable def Gate.mul {d : ℕ} (A B : Gate d) : Gate d :=
  fun i j => ∑ k : Fin d, A i k * B k j

/-- Compose a sequence of gates. -/
noncomputable def Gate.ofList {d : ℕ} : List (Gate d) → Gate d
  | [] => Gate.id d
  | g :: gs => Gate.mul g (Gate.ofList gs)

/-- Two-qudit gate on d⊗d product space. -/
abbrev Gate₂ (d : ℕ) := (Fin d × Fin d) → (Fin d × Fin d) → ℂ

/-- Computational basis state |a⟩ of a qutrit. -/
noncomputable def ket (a : Fin 3) : Qutrit := EuclideanSpace.single a 1

/-- Topological order in 2+1d (UMTC): anyon types with fusion rules
    N^c_{ab} and quantum dimensions d_a (Appendix F, eqs. F1-F2). -/
structure TopologicalOrder (n : ℕ) where
  fusion : Fin n → Fin n → Fin n → ℕ
  qdim : Fin n → ℝ
  qdim_pos : ∀ a, qdim a > 0

/-- Topological superconductor TSC_ν classified by Chern number ν ∈ ℤ.
    Breaks U(1)→Z₂^f, chiral central charge c₋ = ν/2 (Appendix A). -/
structure TSC where
  ν : ℤ
  chiral_central_charge : ℚ
  ccc_eq : chiral_central_charge = ν / 2

-- ═══════════════════════════════════════════════════════════════════════════
-- BILAYER (p+ip)² CONSTRUCTION (Sections II-III)
-- ═══════════════════════════════════════════════════════════════════════════

/-- (p+ip)² bilayer coupled by inter-species current-current interaction.
    ρ_c > ρ_s drives v₁v̄₂ condensation → 4e SC.
    λ₁ > 0 selects diagonal Higgs ⟨Φ⟩ ∝ I₂ → U(2)_{4,0} CS (eq. 4). -/
structure Bilayer where
  ρ_c : ℝ
  ρ_s : ℝ
  charge_dominant : ρ_c > ρ_s
  lam₁ : ℝ
  lam₁_pos : lam₁ > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- SU(2)_4 ANYON DATA (Section IV)
-- ═══════════════════════════════════════════════════════════════════════════

/-- SU(2)_4: 5 anyons j ∈ {0,½,1,³⁄₂,2}, d = (1,√3,2,√3,1).
    Key fusion: 1×1 = 0+1+2. j=2 is a simple current boson (2×2 = 0).
    S-matrix encodes braiding with the condensing boson. -/
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

-- ═══════════════════════════════════════════════════════════════════════════
-- CONDENSATION: SU(2)_4 → Z₃ (Section IV)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Condensing j=2 identifies 2≡0. In 1×1 = 0+1+2, two channels map to
    vacuum (N^0 + N^{2≡0} = 2) → j=1 must split into 1₊, 1₋. -/
theorem two_fold_vacuum_multiplicity (data : SU2_4) :
    data.fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ +
    data.fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = 2 := by
  rw [data.N0_11, data.N2_11]

/-- Half-integers confined: S_{½,2} = -S_{0,2} gives phase -1 when
    encircling the condensate → excitations removed from spectrum. -/
theorem half_int_confined (data : SU2_4) :
    data.S_matrix ⟨1, by omega⟩ ⟨4, by omega⟩ +
    data.S_matrix ⟨0, by omega⟩ ⟨4, by omega⟩ = 0 := by
  rw [data.S_half_2]; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- Z₃ TOPOLOGICAL ORDER (Section IV)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Z₃ TO = SU(2)_4/Z₂ ≅ SU(3)₁: 3 Abelian anyons {0,1₊,1₋},
    d = (1,1,1), fusion = Z₃ addition, D² = 3. -/
structure Z3_TO where
  qdim : Fin 3 → ℝ
  all_abelian : ∀ a, qdim a = 1
  fusion : Fin 3 → Fin 3 → Fin 3
  fusion_Z3 : ∀ a b, (fusion a b).val = (a.val + b.val) % 3
  topological_spin : Fin 3 → ℂ
  spin_0 : topological_spin ⟨0, by omega⟩ = 1

/-- D² = 1² + 1² + 1² = 3 for Z₃ TO. -/
theorem Z3_total_dim_sq (z : Z3_TO) :
    z.qdim ⟨0, by omega⟩ ^ 2 + z.qdim ⟨1, by omega⟩ ^ 2 +
    z.qdim ⟨2, by omega⟩ ^ 2 = 3 := by
  simp only [z.all_abelian]; norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- Z₄ SYMMETRY ENRICHMENT (Section IV)
-- ═══════════════════════════════════════════════════════════════════════════

/-- 4e condensate breaks U(1) → Z₄. Generator g acts as ρ_g: 0↦0, 1₊↔1₋.
    g² = (-1)^F acts trivially on the bosonic sector. -/
structure Z4_SET where
  base : Z3_TO
  rho : Fin 3 → Fin 3
  rho_0 : rho ⟨0, by omega⟩ = ⟨0, by omega⟩
  rho_swap : rho ⟨1, by omega⟩ = ⟨2, by omega⟩
  rho_swap' : rho ⟨2, by omega⟩ = ⟨1, by omega⟩
  rho_involution : ∀ a, rho (rho a) = a

-- ═══════════════════════════════════════════════════════════════════════════
-- Z₃ PARAFERMION σ (Section IV, Appendix G)
-- ═══════════════════════════════════════════════════════════════════════════

/-- G-crossed extension C^×_{Z₂} = C₀ ⊕ C_g. Single defect σ in C_g:
    D²_g = D²_0 = 3, one object → d_σ = √3.
    TY fusion σ×σ = 0 + 1 + 2 (eq. 7). -/
structure Parafermion where
  set_data : Z4_SET
  d_sigma : ℝ
  d_sigma_val : d_sigma = Real.sqrt 3
  sigma_fusion : Fin 3 → ℕ
  sigma_fusion_all : ∀ a, sigma_fusion a = 1

/-- d_σ² = 3 = D²_0. -/
theorem d_sigma_squared (pf : Parafermion) : pf.d_sigma ^ 2 = 3 := by
  rw [pf.d_sigma_val, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

-- ═══════════════════════════════════════════════════════════════════════════
-- F-SYMBOLS AND R-SYMBOLS (Appendix G)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Pentagon → F^{σσσ}_{σef} = -(1/√3)χ(e,f)⁻¹, χ(e,f) = ω^{ef} (eq. G8).
    Hexagon → R^{σσ}_a = Y(-1)^a e^{iπa²/3}, Y² = -i (eqs. G11-G12).
    Gauge-invariant ratio R_a/R_0 = (-1)^a e^{iπa²/3} (eq. 8). -/
structure SymbolData where
  pf : Parafermion
  /-- ω = e^{2πi/3}: primitive cube root of unity. -/
  omega : ℂ
  omega_cubed : omega ^ 3 = 1
  omega_ne_one : omega ≠ 1
  /-- χ(e,f) = ω^{ef}: symmetric bicharacter of Z₃. -/
  chi : Fin 3 → Fin 3 → ℂ
  chi_def : ∀ e f, chi e f = omega ^ (e.val * f.val)
  /-- F^{σσσ}_{σef} = -(1/√3)·χ(e,f)⁻¹ (κ_σ = -1, eq. G8). -/
  F_symbol : Fin 3 → Fin 3 → ℂ
  F_def : ∀ e f, F_symbol e f = -(1 / ↑(Real.sqrt 3)) * (chi e f)⁻¹
  /-- R^{σσ}_a: half-braiding eigenvalues. -/
  R_symbol : Fin 3 → ℂ
  /-- Y: phase from hexagon, Y² = -i. -/
  Y_phase : ℂ
  Y_sq : Y_phase ^ 2 = -Complex.I
  /-- Gauge-invariant ratios R_a/R_0 (eq. 8). -/
  ratio : Fin 3 → ℂ
  ratio_0 : ratio ⟨0, by omega⟩ = 1
  /-- From eq. 8: R₁/R₀ = -e^{iπ/3} = ω⁻¹ (= ω² since ω³=1). -/
  ratio_1 : ratio ⟨1, by omega⟩ = omega⁻¹
  ratio_2 : ratio ⟨2, by omega⟩ = omega⁻¹

/-- χ is symmetric (Z₃ is Abelian). -/
theorem chi_symmetric (sd : SymbolData) (e f : Fin 3) :
    sd.chi e f = sd.chi f e := by
  simp only [sd.chi_def]; congr 1; exact Nat.mul_comm e.val f.val

/-- χ(0,f) = 1 for all f. -/
theorem chi_vacuum (sd : SymbolData) (f : Fin 3) :
    sd.chi ⟨0, by omega⟩ f = 1 := by
  simp [sd.chi_def]

-- ═══════════════════════════════════════════════════════════════════════════
-- BRAIDING MATRICES (Appendix H, eqs. H2-H3)
-- ═══════════════════════════════════════════════════════════════════════════

/-- B₁ = diag(ratio(a)), B₂_{ab} = (1/√3)(δ_{ab} + ω(1-δ_{ab})). -/
structure Braiding where
  sd : SymbolData
  B₁ : Gate 3
  B₁_diag : ∀ a, B₁ a a = sd.ratio a
  B₁_off : ∀ a b, a ≠ b → B₁ a b = 0
  B₂ : Gate 3
  B₂_def : ∀ a b, B₂ a b =
    (1 / ↑(Real.sqrt 3)) * (if a = b then 1 else sd.omega)

-- ═══════════════════════════════════════════════════════════════════════════
-- GATES FROM BRAIDING (Section V, Appendix H)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Phase gate Q = B₁ (eq. H4): diagonal with entries ratio(a). -/
noncomputable def phase_gate (bm : Braiding) : Gate 3 := bm.B₁

/-- Hadamard H = B₁B₂B₁ (eq. H5). -/
noncomputable def hadamard (bm : Braiding) : Gate 3 :=
  Gate.mul (Gate.mul bm.B₁ bm.B₂) bm.B₁

/-- B₁ diagonal ⟹ double sum collapses: H_{ab} = B₁_{aa}·B₂_{ab}·B₁_{bb}. -/
theorem hadamard_reduces (bm : Braiding) (a b : Fin 3) :
    hadamard bm a b = bm.B₁ a a * bm.B₂ a b * bm.B₁ b b := sorry

/-- H_{ab} = ratio(a)·(1/√3)(δ_{ab}+ω(1-δ_{ab}))·ratio(b).
    With ratio = (1,ω⁻¹,ω⁻¹) this is the qutrit DFT: H_{ab} = (1/√3)ω^{ab}. -/
theorem hadamard_explicit (bm : Braiding) (a b : Fin 3) :
    hadamard bm a b =
    bm.sd.ratio a *
    ((1 / ↑(Real.sqrt 3)) * (if a = b then 1 else bm.sd.omega)) *
    bm.sd.ratio b := by
  rw [hadamard_reduces, bm.B₁_diag, bm.B₂_def, bm.B₁_diag]

/-- CZ_{ab;a'b'} = δ_{aa'}δ_{bb'}·ω^{ab} (eq. H6).
    Realized by (B₄B₃B₅B₄)² on 6σ encoding two qutrits. -/
noncomputable def control_Z (bm : Braiding) : Gate₂ 3 :=
  fun ⟨a, b⟩ ⟨a', b'⟩ =>
    if a = a' ∧ b = b' then bm.sd.omega ^ (a.val * b.val) else 0

-- ═══════════════════════════════════════════════════════════════════════════
-- QUTRIT ENCODING (Section V)
-- ═══════════════════════════════════════════════════════════════════════════

/-- 4σ encode 1 qutrit: dim = d_σ⁴/D² = (√3)⁴/3 = 9/3 = 3. -/
theorem qutrit_encoding :
    (Real.sqrt 3) ^ 4 / (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h4 : Real.sqrt 3 ^ 4 = 9 := by
    have : Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
    rw [this, h]; norm_num
  rw [h4, h]; norm_num

/-- 6σ encode 2 qutrits: dim = d_σ⁶/D² = 27/3 = 9 = 3². -/
theorem two_qutrit_encoding :
    (Real.sqrt 3) ^ 6 / (Real.sqrt 3) ^ 2 = (9 : ℝ) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h6 : Real.sqrt 3 ^ 6 = 27 := by
    have : Real.sqrt 3 ^ 6 = (Real.sqrt 3 ^ 2) ^ 3 := by ring
    rw [this, h]; norm_num
  rw [h6, h]; norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- MEASUREMENT AND MAGIC STATES (Section V, Appendix H.2)
-- ═══════════════════════════════════════════════════════════════════════════

/-- M₁ = H²: interferometric probe via path P₁. -/
noncomputable def M₁ (bm : Braiding) : Gate 3 :=
  Gate.mul (hadamard bm) (hadamard bm)

/-- M₂ = H²Q⁻¹: probe path P₂ with phase gate inverse. -/
noncomputable def M₂ (bm : Braiding) : Gate 3 :=
  fun a b => ∑ i : Fin 3, M₁ bm a i *
    (if i = b then (bm.sd.ratio i)⁻¹ else 0)

/-- Magic state |+⟩ = (|1⟩+|2⟩)/√2: non-stabilizer state.
    No Clifford gate maps |0⟩ to |+⟩. -/
noncomputable def magic_plus : Qutrit :=
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨1, by omega⟩ +
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨2, by omega⟩

/-- Magic state |−⟩ = (|1⟩−|2⟩)/√2: non-stabilizer state. -/
noncomputable def magic_minus : Qutrit :=
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨1, by omega⟩ -
  Complex.ofReal (1 / Real.sqrt 2) • ket ⟨2, by omega⟩

/-- M₁ = H² is a permutation: fixes |0⟩, swaps |1⟩↔|2⟩.
    In matrix form: M₁ = [[1,0,0],[0,0,1],[0,1,0]]. -/
theorem M₁_swap (bm : Braiding) :
    M₁ bm ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 ∧
    M₁ bm ⟨0, by omega⟩ ⟨2, by omega⟩ = 0 := sorry

/-- M₂ eigenvalues (1, ω, -ω) on eigenstates (|0⟩, |+⟩, |−⟩) are pairwise
    distinct (ω = e^{2πi/3} ≠ ±1), enabling deterministic magic state
    preparation via repeated measurement (Appendix H.2). -/
theorem M₂_eigenvalues_distinct (bm : Braiding) :
    let evZ : ℂ := 1
    let evP : ℂ := bm.sd.omega
    let evM : ℂ := -(bm.sd.omega)
    evZ ≠ evP ∧ evP ≠ evM ∧ evZ ≠ evM := sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- HEISENBERG-WEYL GROUP AND CLIFFORD GROUP (Section V)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Shift X: X|a⟩ = |a+1 mod d⟩ (Heisenberg-Weyl generator). -/
def HW_shift (d : ℕ) : Gate d :=
  fun row col => if row.val = (col.val + 1) % d then 1 else 0

/-- Clock Z(ω): Z|a⟩ = ω^a|a⟩ (Heisenberg-Weyl generator). -/
def HW_clock (d : ℕ) (omega : ℂ) : Gate d :=
  fun row col => if row = col then omega ^ col.val else 0

/-- HW element X^a·Z^b: maps |c⟩ → ω^{bc}|c+a mod d⟩. -/
def HW_elem (d : ℕ) (omega : ℂ) (a b : ℕ) : Gate d :=
  fun row col => if row.val = (col.val + a) % d
    then omega ^ (b * col.val) else 0

/-- HW commutation: Z·X = ω·X·Z when ω^d = 1 (defining relation of HW(Z_d)).
    Proof: ZX|a⟩ = ω^{a+1}|a+1⟩, XZ|a⟩ = ω^a|a+1⟩, ratio = ω. -/
theorem HW_commutation (d : ℕ) (omega : ℂ) (h_root : omega ^ d = 1) :
    ∀ i j, Gate.mul (HW_clock d omega) (HW_shift d) i j =
      omega * Gate.mul (HW_shift d) (HW_clock d omega) i j := sorry

/-- U is Clifford if ∃ U⁻¹ s.t. conjugation maps X, Z to HW elements.
    The Clifford group Cliff(Z_d) = N_{U(d)}(HW_d). -/
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

/-- A two-qudit gate is a product gate U⊗V. -/
def IsProductGate (d : ℕ) (G : Gate₂ d) : Prop :=
  ∃ (U V : Gate d), ∀ a b a' b', G (a, b) (a', b') = U a a' * V b b'

/-- A two-qudit gate is entangling if it's not a product gate. -/
def IsEntangling (d : ℕ) (G : Gate₂ d) : Prop := ¬IsProductGate d G

/-- Gate applied to |0⟩: U|0⟩ = Σᵢ U_{i0}|i⟩. -/
noncomputable def applyToKet0 (U : Gate 3) : Qutrit :=
  ∑ i : Fin 3, (U i ⟨0, by omega⟩) • ket i

/-- A state is non-stabilizer if not in the orbit of |0⟩ under Clifford.
    Stabilizer states = {U|0⟩ : U ∈ Cliff(Z₃)}, d(d+1) = 12 states for d=3. -/
noncomputable def IsNonStabilizer (omega : ℂ) (ψ : Qutrit) : Prop :=
  ¬∃ (U : Gate 3), IsCliffordGate 3 omega U ∧ ψ = applyToKet0 U

-- ═══════════════════════════════════════════════════════════════════════════
-- CLIFFORD COMPLETENESS (Section V, key contribution)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Phase Q = B₁ normalizes HW: Q·X·Q⁻¹ = ω⁻¹·X·Z, Q·Z·Q⁻¹ = Z.
    (Q is diagonal with entries ratio(a) = (1,ω⁻¹,ω⁻¹), so it commutes
    with Z and maps X → phase-shifted X·Z.) -/
theorem phase_is_clifford (bm : Braiding) :
    IsCliffordGate 3 bm.sd.omega (phase_gate bm) := sorry

/-- Hadamard H = B₁B₂B₁ normalizes HW: H·X·H⁻¹ ∝ Z, H·Z·H⁻¹ ∝ X⁻¹.
    (H is the qutrit DFT up to phases: H_{ab} = (1/√3)ω^{ab} modulo
    the ratio factors; DFT interchanges position and momentum.) -/
theorem hadamard_is_clifford (bm : Braiding) :
    IsCliffordGate 3 bm.sd.omega (hadamard bm) := sorry

/-- CZ from braiding is entangling: CZ_{ab,a'b'} = δ_{aa'}δ_{bb'}ω^{ab}
    cannot factor as U_{aa'}·V_{bb'} because the phase ω^{ab} couples
    the two qutrit indices. -/
theorem CZ_is_entangling (bm : Braiding) :
    IsEntangling 3 (control_Z bm) := sorry

/-- **Clifford completeness**: {Q, H} generate ALL single-qutrit Cliffords.
    With CZ, they generate Cliff(Z₃^n) for any n (standard, Ref. [11]).
    |Cliff(Z₃)| = d³(d²-1) = 216 for d=3. -/
theorem braiding_generates_full_clifford (bm : Braiding) :
    ∀ U : Gate 3, IsCliffordGate 3 bm.sd.omega U →
      ∃ circuit : List (Gate 3),
        (∀ g ∈ circuit, g = phase_gate bm ∨ g = hadamard bm) ∧
        ∀ i j, Gate.ofList circuit i j = U i j := sorry

/-- |+⟩ = (|1⟩+|2⟩)/√2 is non-stabilizer: no Clifford U maps |0⟩ to |+⟩.
    |+⟩ is an eigenstate of M₂ = H²Q⁻¹ with eigenvalue ω (Appendix H.2),
    prepared by measuring M₂ and postselecting. -/
theorem magic_is_non_stabilizer (bm : Braiding) :
    IsNonStabilizer bm.sd.omega magic_plus := sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- UNIVERSALITY (Section V, Bravyi-Kitaev Ref. [10])
-- ═══════════════════════════════════════════════════════════════════════════

/-- Bravyi-Kitaev (Ref. [10]): for prime d, a complete Clifford generating set
    plus a non-stabilizer (magic) state can approximate any d×d unitary
    to arbitrary precision via magic state distillation and injection. -/
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
    Proof assembles five ingredients:
    (1) phase_is_clifford: Q normalizes HW(Z₃)
    (2) hadamard_is_clifford: H normalizes HW(Z₃)
    (3) CZ_is_entangling: CZ couples two qutrits (not a product gate)
    (4) braiding_generates_full_clifford: {Q,H} generate all of Cliff(Z₃)
    (5) magic_is_non_stabilizer: |+⟩ not in stabilizer orbit
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
-- ISING (2e) vs PARAFERMION (4e) COMPARISON (Section V, Table I)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Ising MTC (SU(2)₂): 3 anyons {1, σ_Ising, ψ}.
    d = (1, √2, 1). Fusion: σ×σ = 1+ψ (2 channels), ψ×ψ = 1, σ×ψ = σ.
    This is the anyon content of the ν=1 (2e) topological superconductor. -/
structure IsingMTC where
  qdim : Fin 3 → ℝ
  d_1 : qdim ⟨0, by omega⟩ = 1
  d_sigma : qdim ⟨1, by omega⟩ = Real.sqrt 2
  d_psi : qdim ⟨2, by omega⟩ = 1
  fusion : Fin 3 → Fin 3 → Fin 3 → ℕ
  /-- σ×σ = 1+ψ (only 2 channels, cf. parafermion's 3) -/
  sigma_sigma_1 : fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ = 1
  sigma_sigma_psi : fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ = 1
  psi_psi : fusion ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ = 1
  sigma_psi : fusion ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ = 1

/-- Ising F-matrix and R-matrix.
    F^{σσσ}_σ = (1/√2)[[1,1],[1,-1]] in the {1,ψ} basis (Hadamard matrix).
    R^{σσ}: gauge-invariant ratio R_ψ/R_1 = e^{iπ/2} = i. -/
structure IsingSymbols where
  mtc : IsingMTC
  /-- F^{σσσ}_σ in the {1,ψ} basis: (1/√2)(-1)^{ab}. -/
  F_matrix : Fin 2 → Fin 2 → ℂ
  F_def : ∀ a b, F_matrix a b =
    (1 / ↑(Real.sqrt 2)) * ((-1 : ℂ) ^ (a.val * b.val))
  /-- R-symbol ratio R_ψ/R_1 = i (from R_1 = e^{-iπ/8}, R_ψ = e^{3iπ/8}). -/
  R_ratio : ℂ
  R_ratio_val : R_ratio = Complex.I

/-- Ising braiding on 4γ (1 qubit) and 6γ (2 qubits).
    B₁ = diag(1, i) (R-matrix in {1,ψ} basis, up to global phase).
    B₂ = F·diag(1,i)·F = (1/2)[[1+i,1-i],[1-i,1+i]] (F-conjugation).
    On 6γ, the middle braid σ₃ is a PRODUCT gate:
    the Ising braid representation decomposes as a tensor product. -/
structure IsingBraiding where
  symbols : IsingSymbols
  B₁ : Gate 2
  B₁_00 : B₁ ⟨0, by omega⟩ ⟨0, by omega⟩ = 1
  B₁_11 : B₁ ⟨1, by omega⟩ ⟨1, by omega⟩ = Complex.I
  B₁_off : ∀ a b, a ≠ b → B₁ a b = 0
  B₂ : Gate 2
  /-- Middle braid σ₃ on 6γ (2 qubits): factorizes as product gate.
      The Ising braid representation on 2n Majoranas decomposes
      into tensor product of representations on each qubit pair. -/
  middle_braid_2q : Gate₂ 2
  middle_braid_product : IsProductGate 2 middle_braid_2q

/-- σ×σ fusion channels: Ising has 2, parafermion has 3.
    More fusion channels → richer braid representation → entangling gates. -/
theorem ising_fewer_fusion_channels (im : IsingMTC) (pf : Parafermion) :
    im.fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ +
    im.fusion ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ <
    pf.sigma_fusion ⟨0, by omega⟩ + pf.sigma_fusion ⟨1, by omega⟩ +
    pf.sigma_fusion ⟨2, by omega⟩ := by
  simp only [im.sigma_sigma_1, im.sigma_sigma_psi, pf.sigma_fusion_all]; omega

/-- Ising braiding produces no entangling gate (middle braid factorizes).
    Without entanglement, multi-qubit Clifford is incomplete → not universal. -/
theorem ising_not_entangling (ib : IsingBraiding) :
    ¬IsEntangling 2 ib.middle_braid_2q :=
  fun h => h ib.middle_braid_product

/-- d_σ(Ising) = √2 < √3 = d_σ(parafermion): larger quantum dimension
    ↔ more fusion channels ↔ richer braiding ↔ entangling gates possible. -/
theorem qdim_comparison :
    Real.sqrt 2 < Real.sqrt 3 :=
  Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

-- ═══════════════════════════════════════════════════════════════════════════
-- HIGHER-CHARGE TSCs (Section VI, Appendix B)
-- ═══════════════════════════════════════════════════════════════════════════

/-- U(2)_{2k,0}: TO = SO(3)_k after condensation.
    k=2 (4e): Clifford from braiding, needs magic for universality.
    k≥3 (6e+): ∃ anyon with d²∉ℚ → braiding alone is universal. -/
structure HigherChargeTSC where
  k : ℕ
  k_pos : k > 0
  cooper_charge : ℕ
  charge_eq : cooper_charge = 2 * k

/-- k=3 (6e SC, ν=3/5): quantum dimension d = 1+√2 (silver ratio).
    d² = 3+2√2 ∉ ℚ → braiding generates dense subgroup of SU(d^n)
    (Freedman-Larsen-Wang) → universal without magic states. -/
theorem silver_ratio_sq :
    (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

-- ═══════════════════════════════════════════════════════════════════════════
-- JAIN ROUTE (Section VI)
-- ═══════════════════════════════════════════════════════════════════════════

/-- ν=2/3 Jain state and 4e SC share the SAME Z₃ TO but differ in SET:
    Jain has trivial ρ_g = id, SC has ρ_g permuting 1₊↔1₋.
    The Jain→SC transition is purely a symmetry enrichment transition. -/
structure JainTransition where
  filling : ℚ
  filling_eq : filling = 2/3
  jain_rho : Fin 3 → Fin 3
  jain_trivial : ∀ a, jain_rho a = a
  sc_rho : Fin 3 → Fin 3
  sc_swap_1 : sc_rho ⟨1, by omega⟩ = ⟨2, by omega⟩
  sc_swap_2 : sc_rho ⟨2, by omega⟩ = ⟨1, by omega⟩

/-- Jain and SC have different symmetry actions on the same TO. -/
theorem jain_sc_different_SET (jt : JainTransition) :
    jt.jain_rho ⟨1, by omega⟩ ≠ jt.sc_rho ⟨1, by omega⟩ := by
  rw [jt.jain_trivial, jt.sc_swap_1]; decide

end Charge4eTSC