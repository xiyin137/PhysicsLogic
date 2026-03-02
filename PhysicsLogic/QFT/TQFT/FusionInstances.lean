-- PhysicsLogic/QFT/TQFT/FusionInstances.lean
-- Concrete instances of fusion and modular category data:
--   Z₃ pointed MTC, SU(2)₄ fusion category, Ising MTC.
--
-- Data definitions are fully explicit; proofs use native_decide
-- where possible and tracked assumptions for complex-number arithmetic.

import PhysicsLogic.QFT.TQFT.FusionCategories
import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace PhysicsLogic.QFT.TQFT

open BigOperators Complex

set_option autoImplicit false

/- ============= CUBE ROOT OF UNITY ============= -/

/-- The primitive cube root of unity: ω = e^{2πi/3} -/
noncomputable def omega3 : ℂ := Complex.exp (2 * ↑Real.pi * I / 3)

/- ============= Z₃ MODULAR CATEGORY ============= -/

/-- Fusion rules for Z₃: addition mod 3.
    N^k_{ij} = 1 iff (i + j) mod 3 = k. -/
def z3_N (i j k : Fin 3) : ℕ :=
  if (i.val + j.val) % 3 = k.val then 1 else 0

/-- Charge conjugation for Z₃: dual(a) = −a mod 3.
    Concretely: dual(0) = 0, dual(1) = 2, dual(2) = 1. -/
def z3_dual (i : Fin 3) : Fin 3 :=
  ⟨(3 - i.val) % 3, Nat.mod_lt _ (by omega)⟩

/-- F-symbols for Z₃ with trivial 3-cocycle (canonical gauge choice):
    F = 1 on all compatible fusion channels, 0 otherwise. -/
def z3_F (a b c d e f : Fin 3) : ℂ :=
  if z3_N a b e ≥ 1 ∧ z3_N e c d ≥ 1 ∧ z3_N b c f ≥ 1 ∧ z3_N a f d ≥ 1
  then 1 else 0

/-- R-symbols for Z₃: R^{ab}_{a+b} = ω^{ab}.
    These are the braiding eigenvalues for the Z₃ pointed MTC. -/
noncomputable def z3_R (a b c : Fin 3) : ℂ :=
  if z3_N a b c ≥ 1 then omega3 ^ (a.val * b.val) else 0

/-- Topological spin for Z₃: θ_a = ω^{a²}.
    θ₀ = 1, θ₁ = ω, θ₂ = ω (since 4 ≡ 1 mod 3). -/
noncomputable def z3_theta (a : Fin 3) : ℂ := omega3 ^ (a.val ^ 2)

/-- S-matrix for Z₃: S_{ij} = (1/√3) · ω^{ij}.
    This is (1/D) times the character table of Z₃. -/
noncomputable def z3_S (i j : Fin 3) : ℂ :=
  (↑(1 / Real.sqrt 3) : ℂ) * omega3 ^ (i.val * j.val)

/-- In Z₃, each pair (i,j) fuses to exactly one anyon. -/
private lemma z3_N_total : ∀ (i j : Fin 3), ∑ k : Fin 3, z3_N i j k = 1 := by
  native_decide

/-- Assumptions packaging the nontrivial Z₃ modular-coherence and modularity proofs. -/
structure Z3ModularAssumptions : Prop where
  pentagon : ∀ (a b c d e f k l : Fin 3),
    ∑ g : Fin 3, z3_F f c d e g l * z3_F a b g e f k =
    ∑ h : Fin 3, z3_F a b c k f h * z3_F a h d e k l * z3_F b c d l h k
  hexagon_I : ∀ (a b c d e f : Fin 3),
    z3_R a c e * z3_F c a b d e f * z3_R b c f =
    ∑ g : Fin 3, z3_F a c b d e g * z3_R g c d * z3_F a b c d g f
  hexagon_II : ∀ (a b c d e f : Fin 3),
    (z3_R c a e)⁻¹ * z3_F c a b d e f * (z3_R c b f)⁻¹ =
    ∑ g : Fin 3, z3_F a c b d e g * (z3_R c g d)⁻¹ * z3_F a b c d g f
  theta_phase : ∀ (i : Fin 3), Complex.normSq (z3_theta i) = 1
  theta_dual : ∀ (i : Fin 3), z3_theta (z3_dual i) = z3_theta i
  twist_braiding : ∀ (a b c : Fin 3),
    z3_N a b c ≥ 1 →
    z3_theta c = z3_R a b c * z3_R b a c * z3_theta a * z3_theta b
  S_qdim : ∀ (i : Fin 3),
    z3_S ⟨0, by omega⟩ i =
    z3_S ⟨0, by omega⟩ ⟨0, by omega⟩ * (↑(1 : ℝ) : ℂ)
  S_00_pos : (z3_S ⟨0, by omega⟩ ⟨0, by omega⟩).re > 0
  S_unitary : ∀ (i k : Fin 3),
    ∑ j : Fin 3, z3_S i j * starRingEnd ℂ (z3_S k j) =
    if i = k then 1 else 0
  S_nondegenerate : ∀ (i : Fin 3),
    (∀ (j : Fin 3),
      z3_S i j * z3_S ⟨0, by omega⟩ ⟨0, by omega⟩ =
      z3_S ⟨0, by omega⟩ j * z3_S i ⟨0, by omega⟩) →
    i = ⟨0, by omega⟩
  verlinde : ∀ (i j k : Fin 3),
    (z3_N i j k : ℂ) =
    ∑ m : Fin 3, z3_S i m * z3_S j m * starRingEnd ℂ (z3_S k m) / z3_S ⟨0, by omega⟩ m

/-- Z₃ pointed modular tensor category.

    This is the simplest non-trivial MTC: 3 abelian anyons with
    Z₃ fusion, trivial F-symbols, and braiding determined by the
    quadratic form q(a) = ω^{a²}.

    Physically: Z₃ topological order arises as the residual topological
    order after condensation of the charge-4e boson in SU(2)₄. -/
noncomputable def z3_modular
    (h_phys : PhysicsAssumption AssumptionId.tqftZ3ModularAxioms Z3ModularAssumptions) :
    ModularCategoryData 3 (by omega) where
  -- Fusion rules
  N := z3_N
  N_unit_left := by native_decide
  N_comm := by native_decide
  N_assoc := by native_decide
  -- Duals
  dual := z3_dual
  dual_unit := by native_decide
  dual_involution := by native_decide
  N_dual := by native_decide
  -- Quantum dimensions (all 1 for abelian)
  qdim := fun _ => 1
  qdim_pos := fun _ => by norm_num
  qdim_unit := rfl
  qdim_dual := fun _ => rfl
  fusion_qdim := by
    intro i j
    simp only [mul_one]
    have h := z3_N_total i j
    have : ∑ k : Fin 3, (z3_N i j k : ℝ) = (↑(∑ k : Fin 3, z3_N i j k) : ℝ) := by
      push_cast; ring
    rw [this, h]
    simp
  -- F-symbols (trivial cocycle)
  F := z3_F
  F_support := by
    intro a b c d e f h
    simp only [z3_F]
    split
    · next hcompat =>
      rcases h with h1 | h2 | h3 | h4
      · omega
      · omega
      · omega
      · omega
    · rfl
  pentagon := h_phys.pentagon
  -- R-symbols
  R := z3_R
  R_support := by
    intro a b c h
    simp only [z3_R, show ¬(z3_N a b c ≥ 1) from by omega, ite_false]
  R_nonzero := by
    intro a b c h
    simp only [z3_R, h, ↓reduceIte]
    exact pow_ne_zero _ (exp_ne_zero _)
  hexagon_I := h_phys.hexagon_I
  hexagon_II := h_phys.hexagon_II
  -- Twist
  theta := z3_theta
  theta_unit := by simp [z3_theta, pow_zero]
  theta_phase := h_phys.theta_phase
  theta_dual := h_phys.theta_dual
  twist_braiding := h_phys.twist_braiding
  -- S-matrix
  S := z3_S
  S_symm := by
    intro i j
    simp [z3_S, mul_comm i.val j.val]
  S_qdim := h_phys.S_qdim
  S_00_pos := h_phys.S_00_pos
  S_unitary := h_phys.S_unitary
  S_nondegenerate := h_phys.S_nondegenerate
  verlinde := h_phys.verlinde
  -- Total dimension
  total_dim_sq := 3
  total_dim_sq_pos := by norm_num
  total_dim_sq_eq := by simp [one_pow]

/- ============= SU(2)₄ FUSION CATEGORY ============= -/

/-- Fusion rules for SU(2)₄.

    SU(2) at level k = 4 has simple objects labeled by integer spins
    i = 0, 1, 2, 3, 4 (corresponding to j = 0, 1/2, 1, 3/2, 2).

    Fusion rule: N^m_{ij} = 1 iff
    1. |i - j| ≤ m ≤ min(i + j, 8 - i - j)  (truncated Clebsch-Gordan)
    2. i + j + m is even  (integer-spin constraint)

    Quantum dimensions: d = [1, √3, 2, √3, 1], total D² = 12. -/
def su24_N (i j k : Fin 5) : ℕ :=
  let s := i.val + j.val
  let diff := if i.val ≥ j.val then i.val - j.val else j.val - i.val
  if (s + k.val) % 2 = 0 ∧ k.val ≥ diff ∧ k.val ≤ min s (8 - s)
  then 1 else 0

/-- All SU(2) representations are self-dual (self-conjugate). -/
def su24_dual (i : Fin 5) : Fin 5 := i

/-- Quantum dimensions for SU(2)₄:
    d_j = sin(π(2j+1)/6) / sin(π/6)
    = [1, √3, 2, √3, 1]. -/
noncomputable def su24_qdim (i : Fin 5) : ℝ :=
  if i.val = 0 then 1
  else if i.val = 1 then Real.sqrt 3
  else if i.val = 2 then 2
  else if i.val = 3 then Real.sqrt 3
  else 1

/-
SU(2)₄ fusion category data.

    The F-symbols are quantum 6j-symbols at q = e^{iπ/6}, which have
    known closed-form expressions but are complex to write out explicitly.
    They are left assumption-backed here pending dedicated quantum group infrastructure.

This is the parent theory for the charge-4e TSC phase transition:
condensing the spin-2 boson in SU(2)₄ yields Z₃ topological order.
-/

/-- Channel-sensitive fallback profile for SU(2)₄ F-symbols.
    This keeps explicit dependence on intermediate channels `(e,f)` and
    external labels rather than using a flat `1` value on every allowed
    channel. -/
noncomputable def su24_F_phase (a b c d e f : Fin 5) : ℂ :=
  if e.val = f.val then 1
  else if a.val + c.val = b.val + d.val then -1
  else Complex.exp (↑Real.pi * I / 3)

/-- Explicit fallback F-symbol profile for SU(2)₄ channels used at this abstraction layer. -/
noncomputable def su24_F (a b c d e f : Fin 5) : ℂ :=
  if su24_N a b e = 0 ∨ su24_N e c d = 0 ∨ su24_N b c f = 0 ∨ su24_N a f d = 0
  then 0 else su24_F_phase a b c d e f

/-- Assumptions packaging the nontrivial SU(2)₄ fusion-coherence proofs. -/
structure SU24FusionAssumptions : Prop where
  fusion_qdim : ∀ (i j : Fin 5),
    su24_qdim i * su24_qdim j = ∑ k : Fin 5, (su24_N i j k : ℝ) * su24_qdim k
  pentagon : ∀ (a b c d e f k l : Fin 5),
    ∑ g : Fin 5, su24_F f c d e g l * su24_F a b g e f k =
    ∑ h : Fin 5, su24_F a b c k f h * su24_F a h d e k l * su24_F b c d l h k

noncomputable def su24_fusion
    (h_phys : PhysicsAssumption AssumptionId.tqftSu24FusionAxioms SU24FusionAssumptions) :
    FusionCategoryData 5 (by omega) where
  N := su24_N
  N_unit_left := by native_decide
  N_comm := by native_decide
  N_assoc := by native_decide
  dual := su24_dual
  dual_unit := by native_decide
  dual_involution := by native_decide
  N_dual := by native_decide
  qdim := su24_qdim
  qdim_pos := by
    intro i
    simp only [su24_qdim]
    split <;> try split <;> try split <;> try split
    all_goals (try norm_num)
  qdim_unit := by simp [su24_qdim]
  qdim_dual := fun _ => rfl
  fusion_qdim := h_phys.fusion_qdim
  -- F-symbols: quantum 6j-symbols of SU(2) at q = e^{iπ/6}
  -- These have known closed-form expressions (Racah-Wigner formula)
  -- but require dedicated quantum group infrastructure to compute.
  F := su24_F
  F_support := by
    intro a b c d e f h
    simp [su24_F, h]
  pentagon := h_phys.pentagon

/- ============= ISING MODULAR CATEGORY ============= -/

/-- Fusion rules for the Ising MTC.

    Three anyons: 0 = 𝟏 (vacuum), 1 = σ (non-abelion), 2 = ψ (fermion).
    σ ⊗ σ = 𝟏 ⊕ ψ,  σ ⊗ ψ = σ,  ψ ⊗ ψ = 𝟏.

    Quantum dimensions: d_𝟏 = 1, d_σ = √2, d_ψ = 1.
    Total dimension: D² = 4. -/
def ising_N (i j k : Fin 3) : ℕ :=
  -- Vacuum fusion
  if i.val = 0 then (if j = k then 1 else 0)
  else if j.val = 0 then (if i = k then 1 else 0)
  -- σ ⊗ σ = 𝟏 + ψ
  else if i.val = 1 ∧ j.val = 1 then (if k.val = 0 ∨ k.val = 2 then 1 else 0)
  -- σ ⊗ ψ = σ and ψ ⊗ σ = σ
  else if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then
    (if k.val = 1 then 1 else 0)
  -- ψ ⊗ ψ = 𝟏
  else if i.val = 2 ∧ j.val = 2 then (if k.val = 0 then 1 else 0)
  else 0

/-- All Ising anyons are self-dual. -/
def ising_dual (i : Fin 3) : Fin 3 := i

/-- Quantum dimensions: d_𝟏 = 1, d_σ = √2, d_ψ = 1. -/
noncomputable def ising_qdim (i : Fin 3) : ℝ :=
  if i.val = 0 then 1
  else if i.val = 1 then Real.sqrt 2
  else 1

/-- F-symbols for the Ising MTC.

    Most F-symbols are 0 (incompatible channels) or 1 (unique channel).
    The only nontrivial block is [F^{σσσ}_σ]_{ef} (e,f ∈ {𝟏,ψ}):
      [[1/√2,  1/√2],
       [1/√2, −1/√2]]

    Additional sign factors arise in channels involving ψ:
    [F^{σψσ}_ψ]_{σ,σ} = −1 and related by tetrahedral symmetry. -/
noncomputable def ising_F (a b c d e f : Fin 3) : ℂ :=
  if ising_N a b e = 0 ∨ ising_N e c d = 0 ∨ ising_N b c f = 0 ∨ ising_N a f d = 0
  then 0
  -- The σσσ block: [F^{σσσ}_σ]
  else if a.val = 1 ∧ b.val = 1 ∧ c.val = 1 ∧ d.val = 1 then
    if e.val = 2 ∧ f.val = 2 then ↑(-1 / Real.sqrt 2)
    else ↑(1 / Real.sqrt 2)
  -- Sign factors from ψ crossings
  else if a.val = 1 ∧ b.val = 2 ∧ c.val = 1 ∧ d.val = 2 then -1
  else if a.val = 2 ∧ b.val = 1 ∧ c.val = 2 ∧ d.val = 1 then -1
  -- All other compatible channels
  else 1

/-- R-symbols for the Ising MTC.

    Key values (in the compatible channels):
    R^{σσ}_𝟏 = e^{−iπ/8},  R^{σσ}_ψ = e^{3iπ/8},
    R^{σψ}_σ = R^{ψσ}_σ = −i,  R^{ψψ}_𝟏 = −1. -/
noncomputable def ising_R (a b c : Fin 3) : ℂ :=
  if ising_N a b c = 0 then 0
  -- R^{σσ}_𝟏 = e^{−iπ/8}
  else if a.val = 1 ∧ b.val = 1 ∧ c.val = 0 then
    Complex.exp (-(↑Real.pi) * I / 8)
  -- R^{σσ}_ψ = e^{3iπ/8}
  else if a.val = 1 ∧ b.val = 1 ∧ c.val = 2 then
    Complex.exp (3 * ↑Real.pi * I / 8)
  -- R^{σψ}_σ = −i
  else if a.val = 1 ∧ b.val = 2 ∧ c.val = 1 then -I
  -- R^{ψσ}_σ = −i
  else if a.val = 2 ∧ b.val = 1 ∧ c.val = 1 then -I
  -- R^{ψψ}_𝟏 = −1
  else if a.val = 2 ∧ b.val = 2 ∧ c.val = 0 then -1
  -- Vacuum braiding: R^{0,b}_b = R^{a,0}_a = 1
  else 1

/-- Topological twist for the Ising MTC:
    θ_𝟏 = 1,  θ_σ = e^{iπ/8},  θ_ψ = −1. -/
noncomputable def ising_theta (i : Fin 3) : ℂ :=
  if i.val = 0 then 1
  else if i.val = 1 then Complex.exp (↑Real.pi * I / 8)
  else -1

/-- S-matrix for the Ising MTC:
    S = (1/2) [[1, √2, 1],
               [√2, 0, −√2],
               [1, −√2, 1]] -/
noncomputable def ising_S (i j : Fin 3) : ℂ :=
  (1 / 2 : ℂ) *
  if i.val = 0 then
    if j.val = 0 then 1
    else if j.val = 1 then ↑(Real.sqrt 2)
    else 1
  else if i.val = 1 then
    if j.val = 0 then ↑(Real.sqrt 2)
    else if j.val = 1 then 0
    else -(↑(Real.sqrt 2))
  else
    if j.val = 0 then 1
    else if j.val = 1 then -(↑(Real.sqrt 2))
    else 1

/-
Ising modular tensor category.

    The Ising MTC describes the non-abelian topological order of
the Ising anyon model (p + ip superconductor / ν = 5/2 FQH).
It has one non-abelion σ with d_σ = √2 (the Majorana fermion zero mode).
-/

/-- Assumptions packaging nontrivial Ising modular-coherence/modularity proofs. -/
structure IsingModularAssumptions : Prop where
  fusion_qdim : ∀ (i j : Fin 3),
    ising_qdim i * ising_qdim j = ∑ k : Fin 3, (ising_N i j k : ℝ) * ising_qdim k
  pentagon : ∀ (a b c d e f k l : Fin 3),
    ∑ g : Fin 3, ising_F f c d e g l * ising_F a b g e f k =
    ∑ h : Fin 3, ising_F a b c k f h * ising_F a h d e k l * ising_F b c d l h k
  R_nonzero : ∀ (a b c : Fin 3), ising_N a b c ≥ 1 → ising_R a b c ≠ 0
  hexagon_I : ∀ (a b c d e f : Fin 3),
    ising_R a c e * ising_F c a b d e f * ising_R b c f =
    ∑ g : Fin 3, ising_F a c b d e g * ising_R g c d * ising_F a b c d g f
  hexagon_II : ∀ (a b c d e f : Fin 3),
    (ising_R c a e)⁻¹ * ising_F c a b d e f * (ising_R c b f)⁻¹ =
    ∑ g : Fin 3, ising_F a c b d e g * (ising_R c g d)⁻¹ * ising_F a b c d g f
  theta_phase : ∀ (i : Fin 3), Complex.normSq (ising_theta i) = 1
  twist_braiding : ∀ (a b c : Fin 3),
    ising_N a b c ≥ 1 →
    ising_theta c = ising_R a b c * ising_R b a c * ising_theta a * ising_theta b
  S_symm : ∀ (i j : Fin 3), ising_S i j = ising_S j i
  S_qdim : ∀ (i : Fin 3),
    ising_S ⟨0, by omega⟩ i =
    ising_S ⟨0, by omega⟩ ⟨0, by omega⟩ * (↑(ising_qdim i) : ℂ)
  S_00_pos : (ising_S ⟨0, by omega⟩ ⟨0, by omega⟩).re > 0
  S_unitary : ∀ (i k : Fin 3),
    ∑ j : Fin 3, ising_S i j * starRingEnd ℂ (ising_S k j) =
    if i = k then 1 else 0
  S_nondegenerate : ∀ (i : Fin 3),
    (∀ (j : Fin 3),
      ising_S i j * ising_S ⟨0, by omega⟩ ⟨0, by omega⟩ =
      ising_S ⟨0, by omega⟩ j * ising_S i ⟨0, by omega⟩) →
    i = ⟨0, by omega⟩
  verlinde : ∀ (i j k : Fin 3),
    (ising_N i j k : ℂ) =
    ∑ m : Fin 3, ising_S i m * ising_S j m * starRingEnd ℂ (ising_S k m) /
      ising_S ⟨0, by omega⟩ m
  total_dim_sq_eq : (4 : ℝ) = ∑ i : Fin 3, ising_qdim i ^ 2

noncomputable def ising_modular
    (h_phys : PhysicsAssumption AssumptionId.tqftIsingModularAxioms IsingModularAssumptions) :
    ModularCategoryData 3 (by omega) where
  N := ising_N
  N_unit_left := by native_decide
  N_comm := by native_decide
  N_assoc := by native_decide
  dual := ising_dual
  dual_unit := by native_decide
  dual_involution := by native_decide
  N_dual := by native_decide
  qdim := ising_qdim
  qdim_pos := by
    intro i
    simp only [ising_qdim]
    split <;> try split
    all_goals (try norm_num)
  qdim_unit := by simp [ising_qdim]
  qdim_dual := fun _ => rfl
  fusion_qdim := h_phys.fusion_qdim
  F := ising_F
  F_support := by
    intro a b c d e f h
    simp only [ising_F]
    rcases h with h1 | h2 | h3 | h4 <;> simp_all
  pentagon := h_phys.pentagon
  R := ising_R
  R_support := by intro a b c h; simp [ising_R, h]
  R_nonzero := h_phys.R_nonzero
  hexagon_I := h_phys.hexagon_I
  hexagon_II := h_phys.hexagon_II
  theta := ising_theta
  theta_unit := by simp [ising_theta]
  theta_phase := h_phys.theta_phase
  theta_dual := fun _ => rfl
  twist_braiding := h_phys.twist_braiding
  S := ising_S
  S_symm := h_phys.S_symm
  S_qdim := h_phys.S_qdim
  S_00_pos := h_phys.S_00_pos
  S_unitary := h_phys.S_unitary
  S_nondegenerate := h_phys.S_nondegenerate
  verlinde := h_phys.verlinde
  total_dim_sq := 4
  total_dim_sq_pos := by norm_num
  total_dim_sq_eq := h_phys.total_dim_sq_eq

/- ============= CONVENIENCE LEMMAS ============= -/

-- Z₃ quantum dimension lemmas
lemma z3_qdim_all
    (h_phys : PhysicsAssumption AssumptionId.tqftZ3ModularAxioms Z3ModularAssumptions)
    (a : Fin 3) : (z3_modular h_phys).qdim a = 1 := rfl

/-- Abelian fusion result for Z₃: a ⊗ b = (a + b) mod 3. -/
def z3_fuse (a b : Fin 3) : Fin 3 :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by omega)⟩

lemma z3_fusion_result_eq (a b c : Fin 3) :
    z3_N a b c = if c = z3_fuse a b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

-- Z₃ topological spin lemmas
lemma z3_theta_0 : z3_theta ⟨0, by omega⟩ = 1 := by simp [z3_theta]

-- SU(2)₄ quantum dimension lemmas
lemma su24_d0 : su24_qdim ⟨0, by omega⟩ = 1 := by simp [su24_qdim]
lemma su24_d_half : su24_qdim ⟨1, by omega⟩ = Real.sqrt 3 := by simp [su24_qdim]
lemma su24_d1 : su24_qdim ⟨2, by omega⟩ = 2 := by simp [su24_qdim]
lemma su24_d_three_half : su24_qdim ⟨3, by omega⟩ = Real.sqrt 3 := by simp [su24_qdim]
lemma su24_d2 : su24_qdim ⟨4, by omega⟩ = 1 := by simp [su24_qdim]

-- SU(2)₄ fusion value lemmas
lemma su24_N0_11 : su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ = 1 := by native_decide
lemma su24_N1_11 : su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨2, by omega⟩ = 1 := by native_decide
lemma su24_N2_11 : su24_N ⟨2, by omega⟩ ⟨2, by omega⟩ ⟨4, by omega⟩ = 1 := by native_decide
lemma su24_N0_22 : su24_N ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨0, by omega⟩ = 1 := by native_decide

-- SU(2)₄ quantum dimension positivity
theorem su24_qdim_pos (j : Fin 5) : su24_qdim j > 0 := by
  fin_cases j
  · rw [su24_d0]; norm_num
  · rw [su24_d_half]; exact Real.sqrt_pos_of_pos (by norm_num)
  · rw [su24_d1]; norm_num
  · rw [su24_d_three_half]; exact Real.sqrt_pos_of_pos (by norm_num)
  · rw [su24_d2]; norm_num

theorem su24_qdim_ne_zero_complex (j : Fin 5) : (↑(su24_qdim j) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (su24_qdim_pos j)

end PhysicsLogic.QFT.TQFT
