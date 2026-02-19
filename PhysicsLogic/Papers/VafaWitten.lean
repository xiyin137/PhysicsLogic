import PhysicsLogic.QFT.PathIntegral
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PhysicsLogic.Paper.VafaWitten

open PhysicsLogic.QFT.PathIntegral

set_option autoImplicit false

/- ═══════════════════════════════════════════════════════════════════════════
   VAFA-WITTEN THEOREM (1984)

   Vector-like gauge theories cannot spontaneously break vector flavor symmetry.

   Reference: Vafa & Witten, Nucl. Phys. B 234 (1984) 173
   ═══════════════════════════════════════════════════════════════════════════ -/

abbrev FermionMass : Type := ℝ

/-- Flavor index a = 1, ..., N_f² - 1 labeling generators of SU(N_f) -/
def FlavorIndex (Nf : ℕ) : Type := Fin (Nf^2 - 1)

/-- Complex conjugation (synonym for star) -/
def conjComplex (z : ℂ) : ℂ := star z

/- ═══════════════════════════════════════════════════════════════════════════
   GAUGE THEORY SETUP

   All gauge theory data is bundled in VafaWittenSetup: field configurations,
   gauge transforms, Dirac operators, Euclidean reflection, path integral,
   and condensate observables.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Complete setup for the Vafa-Witten theorem.

    Bundles a vector-like gauge theory with:
    - Gauge field configuration space and gauge transformations
    - Dirac operators and fermion determinants (massless and massive)
    - Euclidean reflection with involution property
    - Path integral (expectation values) with reflection invariance and linearity
    - Reflection positivity of massive fermion determinant
    - Non-singlet condensate observables that are gauge-invariant and reflection-odd
    - Continuity of the massless limit m → 0 -/
structure VafaWittenSetup where
  -- Gauge theory data
  /-- Configuration space of gauge fields A_μ -/
  FieldConfig : Type
  /-- Gauge transformation group -/
  Transform : Type
  /-- Action of gauge transforms on gauge field configurations -/
  gaugeAction : Transform → FieldConfig → FieldConfig

  -- Dirac operator data
  /-- Dirac operator (massless) associated to a gauge configuration -/
  DiracOp : FieldConfig → Type
  /-- Massive Dirac operator D + m -/
  DiracOpMassive : FieldConfig → FermionMass → Type
  /-- Fermion determinant det(D) in the massless case -/
  determinant : (A : FieldConfig) → DiracOp A → ℂ
  /-- Fermion determinant det(D + m) in the massive case -/
  determinantMassive : (A : FieldConfig) → (m : FermionMass) → DiracOpMassive A m → ℂ

  -- Euclidean reflection
  /-- Type of Euclidean reflections (e.g., time reflection x₄ → -x₄) -/
  Reflection : Type
  /-- Action of Euclidean reflection on gauge field configurations -/
  reflectField : Reflection → FieldConfig → FieldConfig
  /-- Reflection is an involution: R² = id -/
  reflect_involution : ∀ (R : Reflection) (A : FieldConfig),
    reflectField R (reflectField R A) = A

  -- Path integral (expectation values)
  /-- Massive gauge expectation value: ⟨O⟩_m = ∫ DA O(A) |det(D+m)| e^{-S[A]} / Z_m -/
  expectMassive : (FieldConfig → ℝ) → FermionMass → ℝ
  /-- Massless gauge expectation value: ⟨O⟩ = lim_{m→0} ⟨O⟩_m -/
  expect : (FieldConfig → ℝ) → ℝ
  /-- Path integral measure is invariant under Euclidean reflection -/
  measure_reflection_inv : ∀ (R : Reflection) (O : FieldConfig → ℝ) (m : FermionMass),
    expectMassive O m = expectMassive (fun A => O (reflectField R A)) m
  /-- Linearity of expectation value: ⟨c·O⟩ = c·⟨O⟩ -/
  expect_linear : ∀ (O : FieldConfig → ℝ) (c : ℝ) (m : FermionMass),
    expectMassive (fun A => c * O A) m = c * expectMassive O m

  -- Reflection positivity of massive fermion determinant
  /-- For m > 0, det(D+m) satisfies:
      1. det(D_R + m) = det(D+m)* (conjugation under reflection)
      2. det(D+m) is real and positive
      This ensures the path integral measure is positive for m > 0. -/
  rp_massive : ∀ (A : FieldConfig) (m : FermionMass)
    (D_m : DiracOpMassive A m) (R : Reflection)
    (D_m_R : DiracOpMassive (reflectField R A) m),
    m > 0 →
    (determinantMassive (reflectField R A) m D_m_R =
     conjComplex (determinantMassive A m D_m)) ∧
    (∃ r : ℝ, r > 0 ∧ determinantMassive A m D_m = r)

  -- Flavor and condensate data
  /-- Number of quark flavors -/
  Nf : ℕ
  /-- Non-singlet condensate observable O_a(A) for each flavor index a.
      These are bilinears like ψ̄ λ_a ψ where λ_a are SU(N_f) generators. -/
  condensate : FlavorIndex Nf → FieldConfig → ℝ
  /-- Condensate is gauge invariant: O_a(A^g) = O_a(A) -/
  condensate_gauge_inv : ∀ (a : FlavorIndex Nf) (g : Transform) (A : FieldConfig),
    condensate a (gaugeAction g A) = condensate a A
  /-- Condensate is odd under Euclidean reflection: O_a(RA) = -O_a(A).
      This is the key property: non-singlet condensates are parity-odd. -/
  condensate_reflection_odd : ∀ (R : Reflection) (a : FlavorIndex Nf) (A : FieldConfig),
    condensate a (reflectField R A) = -(condensate a A)

  -- Massless limit
  /-- Continuity of the massless limit: if ⟨O_a⟩_m = 0 for all m > 0,
      then ⟨O_a⟩ = 0 in the massless theory. -/
  massless_limit : ∀ (a : FlavorIndex Nf),
    (∀ m : FermionMass, m > 0 → expectMassive (condensate a) m = 0) →
    expect (condensate a) = 0

/- ============= OBSERVABLES AND SYMMETRIES ============= -/

/-- A gauge-invariant order parameter -/
structure OrderParameter (setup : VafaWittenSetup) where
  observable : setup.FieldConfig → ℝ
  gauge_invariant : ∀ (g : setup.Transform) (A : setup.FieldConfig),
    observable (setup.gaugeAction g A) = observable A

/-- Non-singlet condensate as an order parameter -/
def condensateNonSinglet (setup : VafaWittenSetup) (a : FlavorIndex setup.Nf) :
    OrderParameter setup :=
  ⟨setup.condensate a, setup.condensate_gauge_inv a⟩

/-- Vector flavor symmetry: commutes with reflection, rotates condensates -/
structure VectorSymmetry (setup : VafaWittenSetup) where
  /-- Flavor transformation acting on gauge fields -/
  transformGauge : setup.FieldConfig → setup.FieldConfig
  /-- Vector symmetry commutes with Euclidean reflection -/
  commutes_with_reflection : ∀ (R : setup.Reflection) (A : setup.FieldConfig),
    setup.reflectField R (transformGauge A) =
    transformGauge (setup.reflectField R A)
  /-- Vector symmetry rotates non-singlet condensates among themselves -/
  rotates_nonsinglet : ∀ (A : setup.FieldConfig) (a : FlavorIndex setup.Nf),
    ∃ (b : FlavorIndex setup.Nf),
    setup.condensate a (transformGauge A) = setup.condensate b A

/- ============= SPONTANEOUS SYMMETRY BREAKING ============= -/

/-- SSB in the massless theory: ⟨O⟩ ≠ 0 -/
def hasSpontaneousSymmetryBreaking (setup : VafaWittenSetup)
  (O : OrderParameter setup) : Prop :=
  setup.expect O.observable ≠ 0

/-- SSB in the massive theory: ⟨O⟩_m ≠ 0 -/
def hasSpontaneousSymmetryBreakingMassive (setup : VafaWittenSetup)
  (O : OrderParameter setup)
  (m : FermionMass) : Prop :=
  setup.expectMassive O.observable m ≠ 0

/- ═══════════════════════════════════════════════════════════════════════════
   THE VAFA-WITTEN THEOREM
   ═══════════════════════════════════════════════════════════════════════════ -/

lemma eq_neg_self_iff_eq_zero {x : ℝ} (h : x = -x) : x = 0 := by linarith

/-- MAIN THEOREM (massive case): No vector SSB for non-singlet condensates.

    Proof: The condensate O_a is parity-odd (O_a(RA) = -O_a(A)),
    so by reflection invariance of the measure:
      ⟨O_a⟩ = ⟨O_a ∘ R⟩ = ⟨-O_a⟩ = -⟨O_a⟩
    Therefore ⟨O_a⟩ = 0 and there is no SSB. -/
theorem vafaWitten_no_vector_SSB_nonsinglet_massive (setup : VafaWittenSetup)
  (_V : VectorSymmetry setup)
  (a : FlavorIndex setup.Nf)
  (m : FermionMass)
  (_h_positive_mass : m > (0 : ℝ))
  (R : setup.Reflection) :
  ¬hasSpontaneousSymmetryBreakingMassive setup (condensateNonSinglet setup a) m := by
  unfold hasSpontaneousSymmetryBreakingMassive
  intro h_SSB

  let O := setup.condensate a
  let x := setup.expectMassive O m

  have h_reflection_inv := setup.measure_reflection_inv R O m
  have h_odd : ∀ A, O (setup.reflectField R A) = -O A :=
    setup.condensate_reflection_odd R a
  have h_linear := setup.expect_linear O (-1) m

  have h_self_neg : x = -x := by
    calc x = setup.expectMassive O m := rfl
         _ = setup.expectMassive (fun A => O (setup.reflectField R A)) m := h_reflection_inv
         _ = setup.expectMassive (fun A => -O A) m := by
             congr 1; funext A; exact h_odd A
         _ = setup.expectMassive (fun A => (-1) * O A) m := by
             congr 1; funext A; ring
         _ = (-1) * setup.expectMassive O m := h_linear
         _ = -x := by ring

  have h_zero : x = 0 := eq_neg_self_iff_eq_zero h_self_neg
  exact h_SSB h_zero

/-- CHIRAL LIMIT: No vector SSB at m = 0.

    Proof: The massive theorem shows ⟨O_a⟩_m = 0 for all m > 0.
    By continuity of the massless limit, ⟨O_a⟩ = lim_{m→0} ⟨O_a⟩_m = 0. -/
theorem vafaWitten_no_vector_SSB_nonsinglet_chiral_limit (setup : VafaWittenSetup)
  (V : VectorSymmetry setup)
  (a : FlavorIndex setup.Nf)
  (R : setup.Reflection) :
  ¬hasSpontaneousSymmetryBreaking setup (condensateNonSinglet setup a) := by
  unfold hasSpontaneousSymmetryBreaking condensateNonSinglet
  simp only
  -- Show: setup.expect (setup.condensate a) = 0
  -- Use massless_limit: if ⟨O_a⟩_m = 0 for all m > 0, then ⟨O_a⟩ = 0
  have h_massive_zero : ∀ m : FermionMass, m > 0 →
      setup.expectMassive (setup.condensate a) m = 0 := by
    intro m hm
    have h := vafaWitten_no_vector_SSB_nonsinglet_massive setup V a m hm R
    unfold hasSpontaneousSymmetryBreakingMassive condensateNonSinglet at h
    simp only at h
    push_neg at h
    exact h
  have h_zero := setup.massless_limit a h_massive_zero
  rw [h_zero]
  simp

end PhysicsLogic.Paper.VafaWitten
