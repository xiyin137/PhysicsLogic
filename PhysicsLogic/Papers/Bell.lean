import PhysicsLogic.Quantum
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Basic

/-!
# Bell's Theorem

This module formalizes Bell's theorem: no local hidden variable theory with a finite
hidden variable space can reproduce the quantum mechanical predictions for singlet state
correlations.

## Structure

1. **LHVT model**: Local hidden variable theories with finite Λ, deterministic ±1 outcomes,
   and locality (Alice's outcome depends only on her setting and λ, not Bob's setting).
2. **CHSH inequality** (fully proven): |S| ≤ 2 for any LHVT.
3. **Quantum prediction** (computed): The singlet correlation E(a,b) = -cos(a-b) gives S = 2√2.
4. **Bell's theorem** (fully proven): No finite LHVT reproduces -cos(a-b).
5. **Connection to QM** (axiomatized via `singlet_pauli_correlation`): The function -cos(a-b)
   is the quantum mechanical expectation value for spin measurements on the singlet state.

## Limitation

The hidden variable space Λ is required to be `Fintype`. The fully general Bell theorem
works for arbitrary probability spaces (σ-algebras with measures). Any stochastic local model
can be purified into a deterministic one by enlarging Λ, so the deterministic assumption
is without loss of generality within the finite setting.
-/

namespace Bell

open PhysicsLogic.Quantum
open BigOperators

set_option autoImplicit false

-- ========================================
-- MEASUREMENT FRAMEWORK
-- ========================================

/-- Measurement setting (detector angle) -/
abbrev Setting : Type := ℝ

/-- Measurement outcome: ±1 -/
inductive Outcome where
  | plus : Outcome
  | minus : Outcome
  deriving DecidableEq

def Outcome.toReal : Outcome → ℝ
  | Outcome.plus => 1
  | Outcome.minus => -1

/-- Correlation function: maps a pair of detector settings to a real number -/
abbrev Correlation := Setting → Setting → ℝ

-- ========================================
-- LOCAL HIDDEN VARIABLE THEORIES
-- ========================================

/-- Probability distribution over a finite hidden variable space -/
structure HiddenVariableDistribution (Λ : Type*) [Fintype Λ] where
  ρ : Λ → ℝ
  nonneg : ∀ (lam : Λ), ρ lam ≥ 0
  normalized : ∑ lam, ρ lam = 1

/-- Deterministic outcome function: maps a setting and hidden variable to an outcome -/
def OutcomeFunction (Λ : Type*) := Setting → Λ → Outcome

/-- Local outcome functions for a bipartite experiment.
    Locality is encoded structurally: Alice's function A depends only on her setting and λ,
    Bob's function B depends only on his setting and λ. Neither can access the other's setting. -/
structure LocalOutcomeFunctions (Λ : Type*) where
  A : OutcomeFunction Λ
  B : OutcomeFunction Λ

/-- Local hidden variable theory with finite hidden variable space.
    Combines a probability distribution over Λ with local deterministic outcomes. -/
structure LHVT where
  Λ : Type*
  fintype_inst : Fintype Λ
  dist : @HiddenVariableDistribution Λ fintype_inst
  outcomes : LocalOutcomeFunctions Λ

attribute [instance] LHVT.fintype_inst

/-- Correlation predicted by an LHVT: E(a,b) = ∑_λ ρ(λ) A(a,λ) B(b,λ) -/
def lhvt_correlation (theory : LHVT) (a b : Setting) : ℝ :=
  ∑ lam : theory.Λ, theory.dist.ρ lam *
    (theory.outcomes.A a lam).toReal *
    (theory.outcomes.B b lam).toReal

-- ========================================
-- CHSH INEQUALITY (FULLY PROVEN)
-- ========================================

/-- CHSH parameter: S = E(a,b) + E(a,b') + E(a',b) - E(a',b') -/
def chsh_parameter (E : Correlation) (a a' b b' : Setting) : ℝ :=
  E a b + E a b' + E a' b - E a' b'

/-- For any ±1 outcomes, the CHSH combination is bounded by 2.
    Key combinatorial fact: a(b + b') + a'(b - b') has one term 0 and the other ±2. -/
lemma outcome_chsh_bound
  (A_a A_a' B_b B_b' : Outcome) :
  |A_a.toReal * B_b.toReal +
   A_a.toReal * B_b'.toReal +
   A_a'.toReal * B_b.toReal -
   A_a'.toReal * B_b'.toReal| ≤ 2 := by
  cases A_a <;> cases A_a' <;> cases B_b <;> cases B_b'
  all_goals (unfold Outcome.toReal; simp only [abs_le]; constructor <;> linarith)

/-- **CHSH inequality**: For any LHVT, |S| ≤ 2.

    Proof sketch: Factor the CHSH parameter as ∑_λ ρ(λ) f(λ), apply the triangle inequality,
    use the per-λ bound |f(λ)| ≤ 2 with ρ(λ) ≥ 0, then normalize with ∑ρ = 1. -/
theorem chsh_inequality (theory : LHVT) (a a' b b' : Setting) :
  |chsh_parameter (lhvt_correlation theory) a a' b b'| ≤ 2 := by
  unfold chsh_parameter lhvt_correlation
  let f := fun (lam : theory.Λ) =>
    (theory.outcomes.A a lam).toReal * (theory.outcomes.B b lam).toReal +
    (theory.outcomes.A a lam).toReal * (theory.outcomes.B b' lam).toReal +
    (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b lam).toReal -
    (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b' lam).toReal
  have h_rewrite : (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a lam).toReal * (theory.outcomes.B b lam).toReal) +
                   (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a lam).toReal * (theory.outcomes.B b' lam).toReal) +
                   (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b lam).toReal) -
                   (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b' lam).toReal) =
                   ∑ lam, theory.dist.ρ lam * f lam := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    funext lam
    simp [f]
    ring
  rw [h_rewrite]
  calc |∑ lam : theory.Λ, theory.dist.ρ lam * f lam|
    ≤ ∑ lam : theory.Λ, |theory.dist.ρ lam * f lam| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ lam : theory.Λ, theory.dist.ρ lam * |f lam| := by
      congr 1
      funext lam
      rw [abs_mul, abs_of_nonneg (theory.dist.nonneg lam)]
    _ ≤ ∑ lam : theory.Λ, theory.dist.ρ lam * 2 := by
      apply Finset.sum_le_sum
      intro lam _
      apply mul_le_mul_of_nonneg_left _ (theory.dist.nonneg lam)
      exact outcome_chsh_bound _ _ _ _
    _ = 2 * ∑ lam : theory.Λ, theory.dist.ρ lam := by
      rw [← Finset.sum_mul]
      ring
    _ = 2 * 1 := by rw [theory.dist.normalized]
    _ = 2 := by norm_num

-- ========================================
-- QUANTUM PREDICTION: SINGLET CORRELATION
-- ========================================

/-- Quantum mechanical correlation for the singlet state with coplanar spin measurements.
    For detector angles a, b in a plane, E(a,b) = -cos(a - b). -/
noncomputable def quantum_correlation_singlet (a b : ℝ) : ℝ :=
  -Real.cos (a - b)

theorem quantum_correlation_bounded (a b : ℝ) :
  -1 ≤ quantum_correlation_singlet a b ∧
  quantum_correlation_singlet a b ≤ 1 := by
  constructor
  · simp [quantum_correlation_singlet]
    have h := Real.cos_le_one (a - b)
    linarith
  · simp [quantum_correlation_singlet]
    have h := Real.neg_one_le_cos (a - b)
    linarith

/-- The CHSH parameter for the singlet correlation with optimal settings equals 2√2.
    Settings: a = 0, a' = -π/2, b = 3π/4, b' = -3π/4. -/
theorem quantum_chsh_equals :
  chsh_parameter quantum_correlation_singlet (0:ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4) = 2 * Real.sqrt 2 := by
  have cos_3pi4 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_four]
  have cos_5pi4 : Real.cos (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : 5 * Real.pi / 4 = Real.pi / 4 + Real.pi := by ring
    rw [this, Real.cos_add_pi, Real.cos_pi_div_four]
  have E1 : quantum_correlation_singlet 0 (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    unfold quantum_correlation_singlet
    rw [show (0 : ℝ) - 3 * Real.pi / 4 = -(3 * Real.pi / 4) from by ring,
        Real.cos_neg, cos_3pi4]; ring
  have E2 : quantum_correlation_singlet 0 (-3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    unfold quantum_correlation_singlet
    rw [show (0 : ℝ) - -3 * Real.pi / 4 = 3 * Real.pi / 4 from by ring,
        cos_3pi4]; ring
  have E3 : quantum_correlation_singlet (-Real.pi / 2) (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    unfold quantum_correlation_singlet
    rw [show -Real.pi / 2 - 3 * Real.pi / 4 = -(5 * Real.pi / 4) from by ring,
        Real.cos_neg, cos_5pi4]; ring
  have E4 : quantum_correlation_singlet (-Real.pi / 2) (-3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    unfold quantum_correlation_singlet
    rw [show -Real.pi / 2 - -3 * Real.pi / 4 = Real.pi / 4 from by ring,
        Real.cos_pi_div_four]
  unfold chsh_parameter
  rw [E1, E2, E3, E4]
  ring

/-- The quantum CHSH parameter exceeds the classical bound: S_QM = 2√2 > 2. -/
theorem quantum_chsh_greater :
  chsh_parameter quantum_correlation_singlet (0:ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4) > 2 := by
  rw [quantum_chsh_equals]
  have : Real.sqrt 2 > 1 := by
    have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 1 := by norm_num
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h2 h1
  linarith

-- ========================================
-- BELL'S THEOREM (FULLY PROVEN)
-- ========================================

/-- **Bell's theorem**: No local hidden variable theory (with finite Λ) can reproduce
    the quantum mechanical singlet correlation E(a,b) = -cos(a-b) for all settings.

    Proof: If such a theory existed, the CHSH inequality would give |S| ≤ 2, but the
    quantum prediction gives S = 2√2 > 2. -/
theorem bell_theorem :
  ¬∃ (theory : LHVT),
    ∀ (a b : Setting),
      lhvt_correlation theory a b = quantum_correlation_singlet a b := by
  intro ⟨theory, h_match⟩
  -- CHSH bound: |S_LHVT| ≤ 2
  have h_bound := chsh_inequality theory (0:ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4)
  -- Matching QM forces lhvt_correlation = quantum_correlation_singlet
  have h_eq : lhvt_correlation theory = quantum_correlation_singlet :=
    funext fun a => funext fun b => h_match a b
  rw [h_eq] at h_bound
  -- Now h_bound : |S_QM| ≤ 2, but S_QM > 2
  linarith [quantum_chsh_greater,
    le_abs_self (chsh_parameter quantum_correlation_singlet
      (0:ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4))]

-- ========================================
-- CONNECTION TO QUANTUM MECHANICS
-- (Axiomatized via singlet_pauli_correlation)
-- ========================================

/-- The singlet state density operator -/
noncomputable def singlet_density (basis : QubitBasis) (bell : BellState basis qubitTensorProduct)
    (h_pure : PhysicsLogic.PhysicsAssumption PhysicsLogic.AssumptionId.quantumPureToDensityAxioms
      (PureToDensityAssumptions (singlet basis bell))) :
    DensityOperator QubitPair :=
  pureToDensity (singlet basis bell) h_pure

/-- The correlation function -cos(a-b) is the quantum mechanical prediction for
    spin measurements on the singlet state along directions (θ=π/2, φ=a) and (θ=π/2, φ=b).
    Depends on `singlet_pauli_correlation` in PhysicsLogic.Quantum.Measurement. -/
theorem quantum_correlation_is_physical (basis : QubitBasis) (bell : BellState basis qubitTensorProduct)
    (paulis : PauliOperators) (a b : ℝ)
    (h_pauli_a : PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.quantumPauliDirectionObservable
      (PauliDirectionAssumptions paulis (Real.pi / 2) a))
    (h_pauli_b : PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.quantumPauliDirectionObservable
      (PauliDirectionAssumptions paulis (Real.pi / 2) b))
    (tensorObs : TensorObservable qubitTensorProduct
      (pauli_direction paulis (Real.pi / 2) a h_pauli_a)
      (pauli_direction paulis (Real.pi / 2) b h_pauli_b))
    (h_phys : PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.quantumSingletPauliCorrelation
      (expectation_value (singlet basis bell) tensorObs.obs = -Real.cos (a - b))) :
  quantum_correlation_singlet a b =
  expectation_value (singlet basis bell) tensorObs.obs := by
  unfold quantum_correlation_singlet
  symm
  exact singlet_pauli_correlation basis bell paulis a b h_pauli_a h_pauli_b tensorObs h_phys

/-- **Quantum mechanics violates local realism**: No LHVT can reproduce the quantum mechanical
    expectation values for tensor product observables on the singlet state.

    This lifts `bell_theorem` from the specific function -cos(a-b) to the full quantum
    mechanical prediction via `quantum_correlation_is_physical`. -/
theorem quantum_mechanics_violates_local_realism (basis : QubitBasis)
    (bell : BellState basis qubitTensorProduct)
    (paulis : PauliOperators)
    (h_pauli : ∀ (x : ℝ),
      PhysicsLogic.PhysicsAssumption PhysicsLogic.AssumptionId.quantumPauliDirectionObservable
      (PauliDirectionAssumptions paulis (Real.pi / 2) x))
    (mkTensorObs : ∀ (a b : ℝ), TensorObservable qubitTensorProduct
      (pauli_direction paulis (Real.pi / 2) a (h_pauli a))
      (pauli_direction paulis (Real.pi / 2) b (h_pauli b)))
    (h_corr : ∀ (a b : ℝ),
      PhysicsLogic.PhysicsAssumption PhysicsLogic.AssumptionId.quantumSingletPauliCorrelation
      (expectation_value (singlet basis bell) (mkTensorObs a b).obs = -Real.cos (a - b))) :
  ¬∃ (theory : LHVT),
    ∀ (a b : Setting),
      lhvt_correlation theory a b =
      expectation_value (singlet basis bell) (mkTensorObs a b).obs := by
  intro ⟨theory, h_match⟩
  apply bell_theorem
  use theory
  intro a b
  rw [quantum_correlation_is_physical basis bell paulis a b
        (h_pauli a) (h_pauli b) (mkTensorObs a b) (h_corr a b)]
  exact h_match a b

end Bell
