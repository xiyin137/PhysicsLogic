import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Weinberg-Witten theorem (physics-logic abstraction)

This module encodes the logical core of the Weinberg-Witten no-go statements:

1. If a massless one-particle state carries a nonzero charge of a Lorentz-covariant
   conserved current, then its helicity magnitude is at most `1/2`.
2. If a massless one-particle state carries nonzero energy-momentum matrix element
   of a Lorentz-covariant conserved stress tensor, then its helicity magnitude is
   at most `1`.

The detailed QFT derivation is represented here as explicit `Prop` assumptions in the
setup structures, while consequences are proved in Lean.
-/

namespace WeinbergWitten

set_option autoImplicit false

/-- Abstract massless one-particle state.

`spin = |helicity|` is included as an explicit kinematic fact for massless states. -/
structure MasslessOneParticleState where
  spin : ℝ
  helicity : ℝ
  spin_nonneg : 0 ≤ spin
  spin_eq_abs_helicity : spin = |helicity|

/-- Setup for the charge-current branch of Weinberg-Witten. -/
structure CurrentTheoremSetup where
  state : MasslessOneParticleState
  /-- Existence of a Lorentz-covariant conserved current. -/
  hasLorentzCovariantConservedCurrent : Prop
  /-- The massless state carries a nonzero charge of that current. -/
  carriesNonzeroCurrentCharge : Prop
  /-- Weinberg-Witten current conclusion: `|h| ≤ 1/2`. -/
  helicity_bound :
    hasLorentzCovariantConservedCurrent →
    carriesNonzeroCurrentCharge →
    |state.helicity| ≤ (1 / 2 : ℝ)

/-- Setup for the stress-tensor branch of Weinberg-Witten. -/
structure StressTheoremSetup where
  state : MasslessOneParticleState
  /-- Existence of a Lorentz-covariant conserved stress tensor. -/
  hasLorentzCovariantConservedStress : Prop
  /-- The massless state has nonzero energy-momentum matrix element. -/
  hasNonzeroStressMatrixElement : Prop
  /-- Weinberg-Witten stress conclusion: `|h| ≤ 1`. -/
  helicity_bound :
    hasLorentzCovariantConservedStress →
    hasNonzeroStressMatrixElement →
    |state.helicity| ≤ (1 : ℝ)

/-! ## Current branch consequences -/

/-- Under the current-branch assumptions, spin is at most `1/2`. -/
theorem current_branch_spin_bound
    (setup : CurrentTheoremSetup)
    (h_cov : setup.hasLorentzCovariantConservedCurrent)
    (h_charge : setup.carriesNonzeroCurrentCharge) :
    setup.state.spin ≤ (1 / 2 : ℝ) := by
  calc
    setup.state.spin = |setup.state.helicity| := setup.state.spin_eq_abs_helicity
    _ ≤ (1 / 2 : ℝ) := setup.helicity_bound h_cov h_charge

/-- No-go form: a massless state with spin `> 1/2` cannot satisfy both
current-branch hypotheses simultaneously. -/
theorem no_current_charge_for_spin_gt_half
    (setup : CurrentTheoremSetup)
    (h_spin : setup.state.spin > (1 / 2 : ℝ))
    (h_cov : setup.hasLorentzCovariantConservedCurrent) :
    ¬ setup.carriesNonzeroCurrentCharge := by
  intro h_charge
  have h_bound : setup.state.spin ≤ (1 / 2 : ℝ) :=
    current_branch_spin_bound setup h_cov h_charge
  linarith

/-- Spin-1 corollary of the current branch. -/
theorem spin_one_no_current_charge
    (setup : CurrentTheoremSetup)
    (h_spin_one : setup.state.spin = (1 : ℝ))
    (h_cov : setup.hasLorentzCovariantConservedCurrent) :
    ¬ setup.carriesNonzeroCurrentCharge := by
  apply no_current_charge_for_spin_gt_half setup
  · linarith [h_spin_one]
  · exact h_cov

/-! ## Stress-tensor branch consequences -/

/-- Under the stress-branch assumptions, spin is at most `1`. -/
theorem stress_branch_spin_bound
    (setup : StressTheoremSetup)
    (h_cov : setup.hasLorentzCovariantConservedStress)
    (h_stress : setup.hasNonzeroStressMatrixElement) :
    setup.state.spin ≤ (1 : ℝ) := by
  calc
    setup.state.spin = |setup.state.helicity| := setup.state.spin_eq_abs_helicity
    _ ≤ (1 : ℝ) := setup.helicity_bound h_cov h_stress

/-- No-go form: a massless state with spin `> 1` cannot satisfy both
stress-branch hypotheses simultaneously. -/
theorem no_stress_matrix_element_for_spin_gt_one
    (setup : StressTheoremSetup)
    (h_spin : setup.state.spin > (1 : ℝ))
    (h_cov : setup.hasLorentzCovariantConservedStress) :
    ¬ setup.hasNonzeroStressMatrixElement := by
  intro h_stress
  have h_bound : setup.state.spin ≤ (1 : ℝ) :=
    stress_branch_spin_bound setup h_cov h_stress
  linarith

/-- Spin-2 corollary of the stress branch. -/
theorem spin_two_no_stress_matrix_element
    (setup : StressTheoremSetup)
    (h_spin_two : setup.state.spin = (2 : ℝ))
    (h_cov : setup.hasLorentzCovariantConservedStress) :
    ¬ setup.hasNonzeroStressMatrixElement := by
  apply no_stress_matrix_element_for_spin_gt_one setup
  · linarith [h_spin_two]
  · exact h_cov

end WeinbergWitten
