-- PhysicsLogic/QFT/TQFT/CondensationInstances.lean
-- Concrete instances of G-actions, G-crossed braided extensions,
-- anyon condensation, and gauging:
--   Z₂ action on Z₃, Z₂-crossed extension (parafermion/Tambara-Yamagami),
--   SU(2)₄ → Z₃ condensation.

import PhysicsLogic.QFT.TQFT.FusionInstances
import PhysicsLogic.QFT.TQFT.GCrossedCategories
import PhysicsLogic.Assumptions

namespace PhysicsLogic.QFT.TQFT

open BigOperators Complex

set_option autoImplicit false

/- ============= SU(2)₄ RIBBON CATEGORY ============= -/

/-- Topological twist for SU(2)₄:
    θ_j = e^{2πi·j(j+1)/(k+2)} where k = 4 and j = i/2 (integer label).
    θ₀ = 1, θ₁ = e^{iπ/4}, θ₂ = e^{2iπ/3}, θ₃ = e^{5iπ/4}, θ₄ = 1. -/
noncomputable def su24_theta (i : Fin 5) : ℂ :=
  if i.val = 0 then 1
  else if i.val = 1 then Complex.exp (↑Real.pi * I / 4)
  else if i.val = 2 then Complex.exp (2 * ↑Real.pi * I / 3)
  else if i.val = 3 then Complex.exp (5 * ↑Real.pi * I / 4)
  else 1  -- θ₄ = e^{2πi} = 1

/-
SU(2)₄ as a ribbon category.

Extends su24_fusion with braiding and explicit topological twists.
The key property for condensation is θ₄ = 1 (spin-2 is a boson).
-/
/-- Placeholder braiding profile for compatible SU(2)₄ fusion channels. -/
noncomputable def su24_R (a b c : Fin 5) : ℂ :=
  if su24_N a b c = 0 then 0 else 1

/-- Assumptions packaging nontrivial SU(2)₄ ribbon-coherence proofs. -/
structure SU24RibbonAssumptions : Prop where
  hexagon_I : ∀ (a b c d e f : Fin 5),
    su24_R a c e * su24_F c a b d e f * su24_R b c f =
    ∑ g : Fin 5, su24_F a c b d e g * su24_R g c d * su24_F a b c d g f
  hexagon_II : ∀ (a b c d e f : Fin 5),
    (su24_R c a e)⁻¹ * su24_F c a b d e f * (su24_R c b f)⁻¹ =
    ∑ g : Fin 5, su24_F a c b d e g * (su24_R c g d)⁻¹ * su24_F a b c d g f
  theta_phase : ∀ (i : Fin 5), Complex.normSq (su24_theta i) = 1
  twist_braiding : ∀ (a b c : Fin 5),
    su24_N a b c ≥ 1 →
    su24_theta c = su24_R a b c * su24_R b a c * su24_theta a * su24_theta b

noncomputable def su24_ribbon
    (h_fusion : PhysicsAssumption AssumptionId.tqftSu24FusionAxioms SU24FusionAssumptions)
    (h_phys : PhysicsAssumption AssumptionId.tqftSu24RibbonAxioms SU24RibbonAssumptions) :
    RibbonCategoryData 5 (by omega) where
  toFusionCategoryData := su24_fusion h_fusion
  -- R-symbols: assumption-backed placeholder profile at this abstraction layer.
  R := su24_R
  R_support := by
    intro a b c h
    change su24_N a b c = 0 at h
    simp [su24_R, h]
  R_nonzero := by
    intro a b c h
    change su24_N a b c ≥ 1 at h
    have hne : su24_N a b c ≠ 0 := by omega
    simp [su24_R, hne]
  hexagon_I := h_phys.hexagon_I
  hexagon_II := h_phys.hexagon_II
  -- Topological twist
  theta := su24_theta
  theta_unit := by simp [su24_theta]
  theta_phase := h_phys.theta_phase
  theta_dual := fun _ => rfl  -- dual = id for SU(2)
  twist_braiding := h_phys.twist_braiding

/- ============= Z₂ ACTION ON Z₃ ============= -/

/-- The Z₂ action on Z₃ by charge conjugation: ρ(1, a) = −a mod 3.

    This is the symmetry of the Z₃ topological order that exchanges
    charge 1 ↔ charge 2 while fixing the vacuum. -/
def z2_rho_on_z3 (g : Fin 2) (a : Fin 3) : Fin 3 :=
  if g.val = 0 then a else z3_dual a

/-- Z₂ acts on Z₃ by charge conjugation.

    The nontrivial element swaps anyons 1 ↔ 2, preserving fusion rules
    (since Z₃ fusion is symmetric under charge conjugation) and
    quantum dimensions (all equal to 1). -/
noncomputable def z2_action_on_z3
    (h_z3 : PhysicsAssumption AssumptionId.tqftZ3ModularAxioms Z3ModularAssumptions) :
    GActionOnCategory 3 (by omega) 2 (by omega) (z3_modular h_z3).toFusionCategoryData where
  rho := z2_rho_on_z3
  rho_id := by
    intro a; simp [z2_rho_on_z3]
  rho_comp := by
    intro g h a
    fin_cases g <;> fin_cases h <;> simp [z2_rho_on_z3]
    · fin_cases a <;> rfl  -- g=1, h=1: dual(dual(a)) = a
  rho_vacuum := by
    intro g; fin_cases g <;> simp [z2_rho_on_z3, z3_dual]
  rho_preserves_fusion := by
    intro g a b c
    fin_cases g
    · rfl
    · fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
  rho_preserves_qdim := fun _ _ => rfl

/- ============= Z₂-CROSSED EXTENSION OF Z₃ ============= -/

/-- Helper: z3_modular.qdim is identically 1. -/
private lemma z3_qdim_eq_one
    (h_z3 : PhysicsAssumption AssumptionId.tqftZ3ModularAxioms Z3ModularAssumptions)
    (i : Fin 3) : (z3_modular h_z3).qdim i = 1 := rfl

/-- Z₂-crossed braided extension of Z₃ (Tambara-Yamagami / parafermion).

    The defect sector C₁ (Z₂ nontrivial sector) contains a single
    non-abelian defect σ with quantum dimension d_σ = √3.

    Key properties:
    - σ ⊗ σ = 0 ⊕ 1 ⊕ 2 (fuses to all Z₃ anyons with multiplicity 1)
    - d_σ² = 3 = D²(Z₃) (equal total dimension in each sector)
    - Braiding a Z₃ anyon a around σ gives charge conjugate: a ↦ −a mod 3

    Gauging this Z₂ symmetry produces SU(2)₄ (or its time-reversal). -/
noncomputable def z2_gcrossed_z3
    (h_z3 : PhysicsAssumption AssumptionId.tqftZ3ModularAxioms Z3ModularAssumptions) :
    GCrossedBraidedData 3 (by omega) 2 (by omega)
      (z3_modular h_z3).toFusionCategoryData (z2_action_on_z3 h_z3) where
  defect_count := 1
  defect_count_pos := by omega
  defect_qdim := fun _ => Real.sqrt 3
  defect_qdim_pos := fun _ => Real.sqrt_pos_of_pos (by norm_num)
  D_sq_0 := 3
  D_sq_0_pos := by norm_num
  D_sq_0_eq := by
    simp only [z3_qdim_eq_one h_z3, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  D_sq_defect_eq := by
    simp only [Fin.sum_univ_one]
    rw [sq, Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  defect_self_fusion := fun _ _ _ => 1  -- σ ⊗ σ → all Z₃ anyons
  defect_fusion_qdim := by
    intro σ τ
    simp only [Fin.sum_univ_three, Nat.cast_one, one_mul, z3_qdim_eq_one h_z3]
    rw [Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
    norm_num
  gcrossed_braiding := fun a _ => z3_dual a
  gcrossed_braiding_eq := by
    intro a σ
    exact ⟨⟨1, by omega⟩, rfl⟩

/- ============= SU(2)₄ → Z₃ CONDENSATION ============= -/

/-- Monodromy signs for SU(2)₄ condensation.

    Monodromy of anyon i with the spin-2 boson (label 4):
    M_{i,4} = θ_{i⊗4} / (θ_i · θ_4)
    Labels 0, 2, 4 have M = +1 (deconfined).
    Labels 1, 3 have M = −1 (confined). -/
def su24_condensation_monodromy (a : Fin 5) : ℤ :=
  if a.val = 0 then 1
  else if a.val = 1 then -1
  else if a.val = 2 then 1
  else if a.val = 3 then -1
  else 1

/-- Deconfinement map for SU(2)₄ → Z₃ condensation.

    - Vacuum (0) → vacuum (0)
    - Spin-1/2 (1) → confined
    - Spin-1 (2) → charge 1 in Z₃  (d=2 splits into d=1+d=1)
    - Spin-3/2 (3) → confined
    - Spin-2 boson (4) → vacuum (0)  (identified with vacuum) -/
def su24_deconfine_map (a : Fin 5) : Option (Fin 3) :=
  if a.val = 0 then some ⟨0, by omega⟩
  else if a.val = 1 then none
  else if a.val = 2 then some ⟨1, by omega⟩
  else if a.val = 3 then none
  else some ⟨0, by omega⟩  -- spin-2 → vacuum

/-- Condensation of the spin-2 boson in SU(2)₄ produces Z₃ topological order.

    The spin-2 representation (label 4) is a bosonic simple current:
    - θ₄ = 1 (boson), d₄ = 1 (abelian), dual(4) = 4 (self-dual)
    - 4 ⊗ 4 = 0 (order-2 simple current, generates ℤ₂ ⊂ SU(2)₄)

    After condensation:
    - Confined: spins 1/2, 3/2 (labels 1, 3; monodromy = −1)
    - Deconfined: vacuum, spin-1, spin-2 (labels 0, 2, 4)
    - Identification: {0, 4} → vacuum of Z₃
    - Splitting: spin-1 (d=2) → two Z₃ anyons (d=1 each)
    - Dimension ratio: D²(SU(2)₄) = 12 = 2² · 3 = |ℤ₂|² · D²(Z₃) -/
noncomputable def su24_to_z3_condensation
    (h_fusion : PhysicsAssumption AssumptionId.tqftSu24FusionAxioms SU24FusionAssumptions)
    (h_ribbon : PhysicsAssumption AssumptionId.tqftSu24RibbonAxioms SU24RibbonAssumptions)
    (h_z3 : PhysicsAssumption AssumptionId.tqftZ3ModularAxioms Z3ModularAssumptions) :
    CondensableAlgebraData 5 (by omega) (su24_ribbon h_fusion h_ribbon) 3 (by omega)
      (z3_modular h_z3).toFusionCategoryData where
  condensing := ⟨4, by omega⟩
  condensing_is_boson := ⟨rfl, rfl, rfl⟩
  condensing_self_fuse := by
    -- N^0_{44} ≥ 1: unfold through su24_ribbon to su24_N
    change su24_N ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨0, by omega⟩ ≥ 1
    native_decide
  monodromy_sign := su24_condensation_monodromy
  mono_vacuum := rfl
  mono_self := rfl
  mono_values := by
    intro a
    simp only [su24_condensation_monodromy]
    split <;> try split <;> try split <;> try split
    all_goals (first | left; rfl | right; rfl)
  deconfine_map := su24_deconfine_map
  confined_removed := by
    intro a h
    fin_cases a <;> simp_all [su24_condensation_monodromy, su24_deconfine_map]
  deconfined_survives := by
    intro a h
    fin_cases a <;> simp_all [su24_condensation_monodromy, su24_deconfine_map]
  deconfine_vacuum := rfl
  condensation_order := 2
  condensation_order_pos := by omega
  dim_ratio := by
    show (su24_ribbon h_fusion h_ribbon).totalDimSq =
      (2 : ℝ) ^ 2 * (z3_modular h_z3).toFusionCategoryData.totalDimSq
    have h_parent : (su24_ribbon h_fusion h_ribbon).totalDimSq = 12 := by
      have hq : (su24_ribbon h_fusion h_ribbon).qdim = su24_qdim := rfl
      simp only [FusionCategoryData.totalDimSq, hq]
      rw [Fin.sum_univ_five]
      simp [su24_qdim]
      have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
      nlinarith
    have h_child : (z3_modular h_z3).toFusionCategoryData.totalDimSq = 3 := by
      show ∑ i : Fin 3, (z3_modular h_z3).qdim i ^ 2 = 3
      simp only [z3_qdim_all h_z3, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
      norm_num
    rw [h_parent, h_child]; norm_num

/- ============= CONVENIENCE LEMMAS ============= -/

-- Z₂ action on Z₃: nontrivial element (g = 1) convenience lemmas
@[simp] lemma z2_rho_0 : z2_rho_on_z3 ⟨1, by omega⟩ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  simp [z2_rho_on_z3, z3_dual]

@[simp] lemma z2_rho_swap : z2_rho_on_z3 ⟨1, by omega⟩ ⟨1, by omega⟩ = ⟨2, by omega⟩ := by
  simp [z2_rho_on_z3, z3_dual]

@[simp] lemma z2_rho_swap' : z2_rho_on_z3 ⟨1, by omega⟩ ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
  simp [z2_rho_on_z3, z3_dual]

-- SU(2)₄ topological twist convenience lemmas
lemma su24_theta_j0 : su24_theta ⟨0, by omega⟩ = 1 := by simp [su24_theta]
lemma su24_theta_j2 : su24_theta ⟨4, by omega⟩ = 1 := by simp [su24_theta]

end PhysicsLogic.QFT.TQFT
