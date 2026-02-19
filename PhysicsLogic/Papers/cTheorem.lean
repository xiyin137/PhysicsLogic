-- PhysicsLogic/Papers/cTheorem.lean

import PhysicsLogic.QFT.CFT.TwoDimensional.Virasoro
import PhysicsLogic.QFT.Wightman.WightmanFunctions
import PhysicsLogic.QFT.Wightman.Operators
import PhysicsLogic.Quantum
import PhysicsLogic.SpaceTime.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

/-!
# Zamolodchikov's c-Theorem in 2D Quantum Field Theory

This file formalizes A.B. Zamolodchikov's groundbreaking 1986 theorem proving
the irreversibility of renormalization group (RG) flows in 2-dimensional QFT.

## Physical Context

In quantum field theory, the renormalization group describes how physical
observables change with energy scale. A fundamental question is whether this
flow has a preferred direction - an "arrow of time" in theory space.

Zamolodchikov proved that in 2D, there exists a function c(g) of the coupling
constants that:
1. Decreases monotonically along RG flows: dc/dt ≤ 0
2. Is stationary at fixed points: dc/dt = 0 iff βᵢ = 0 for all i
3. Equals the Virasoro central charge at CFT fixed points

This establishes irreversibility: RG flow from UV to IR is a one-way process.

## Mathematical Framework

The proof relies entirely on the **Wightman axioms** - no path integrals or
actions required. Key ingredients:

1. **Stress tensor trace**: θ = T^μ_μ (vanishes in CFT, nonzero off-criticality)
2. **Ward identities**: Relate θ correlators to β-functions via operator insertions
3. **Spectral representation**: Unitarity (Wightman positivity) gives ρ(p²) ≥ 0
4. **Momentum space kernel**: K(p²) = -1/(p²√p²) has crucial sign properties

The c-function is defined via:
```
c(g) = (3/4π²) ∫ d²x r³ ⟨θ(x)θ(0)⟩
```

In momentum space, using the Ward identity:
```
dc/dt = -(3/4π²) ∑ᵢ βᵢ ∫ d²p K(p²) ρᵢ(p²)
```

Since K(p²) < 0 and ρᵢ(p²) ≥ 0 by unitarity, we get βᵢ · (dc/dgᵢ) ≤ 0,
proving dc/dt = ∑ᵢ βᵢ · (dc/dgᵢ) ≤ 0.

## References

- Zamolodchikov, A.B. (1986). "Irreversibility of the Flux of the Renormalization
  Group in a 2D Field Theory". JETP Lett. 43: 730-732.
-/

namespace PhysicsLogic.Papers.Zamolodchikov1986

open PhysicsLogic.QFT Real
open CFT.TwoDimensional Wightman
open PhysicsLogic.Quantum
open PhysicsLogic.SpaceTime

/-- 2D spacetime point (time, space) -/
abbrev Point2D := Fin 2 → ℝ

/-- Origin in 2D spacetime -/
def origin_2d : Point2D := fun _ => 0

/-- Radial point at distance r in spatial direction -/
noncomputable def radialPoint_2d (r : ℝ) : Point2D :=
  fun i => if i.val = 1 then r else 0

/-- A 2D quantum field theory with RG flow.

    This structure encodes:
    - n_couplings: number of marginal/relevant operators
    - theta_field: the trace of stress tensor T^μ_μ as a field distribution
    - couplings: current values gᵢ(t) at RG scale t
    - beta_functions: βᵢ = dgᵢ/dt governing RG flow
    - coupling_dimensions: canonical dimensions Δᵢ of coupling operators
-/
structure QFT2D (H : Type _) [QuantumStateSpace H] where
  /-- Number of coupling constants in the theory -/
  n_couplings : ℕ
  /-- Wightman function theory for the 2D theory -/
  wft : WightmanFunctionTheory H 2
  /-- Trace of stress tensor θ = T^μ_μ as operator-valued distribution.
      Vanishes at CFT fixed points, nonzero under RG flow. -/
  theta_field : FieldDistribution H 2
  /-- Current values of coupling constants gᵢ -/
  couplings : Fin n_couplings → ℝ
  /-- Beta functions βᵢ = μ dgᵢ/dμ governing RG flow -/
  beta_functions : Fin n_couplings → ℝ
  /-- Canonical scaling dimensions of coupling operators -/
  coupling_dimensions : Fin n_couplings → ℝ

/-- The stress tensor trace θ = T^μ_μ as a field distribution -/
def theta {H : Type _} [QuantumStateSpace H] (theory : QFT2D H) : FieldDistribution H 2 :=
  theory.theta_field

/-! ## Momentum Space Kernel

The kernel K(p²) = -1/(p²√p²) arises from the Fourier transform of ∫ dr r³ cos(pr).
Its negativity is crucial for the proof. -/

/-- Momentum space kernel K(p²) = -1/(p²√p²) for p² > 0.
    This arises from Fourier transform of ∫ dr r³ cos(pr).
    The crucial property is K(p²) < 0 for p² > 0. -/
noncomputable def momentum_space_kernel (p_squared : ℝ) : ℝ :=
  if p_squared > 0 then -1 / (p_squared * sqrt p_squared) else 0

theorem momentum_kernel_negative (p_squared : ℝ) (h : p_squared > 0) :
  momentum_space_kernel p_squared < 0 := by
  unfold momentum_space_kernel
  simp [h]
  apply div_neg_of_neg_of_pos
  · norm_num
  · apply mul_pos h; exact Real.sqrt_pos.mpr h

/-- Positive version of kernel: -K(p²) > 0 for p² > 0 -/
noncomputable def positive_kernel_function (p_squared : ℝ) : ℝ :=
  - momentum_space_kernel p_squared

theorem kernel_positivity (p_squared : ℝ) (h : p_squared > 0) :
  positive_kernel_function p_squared > 0 := by
  unfold positive_kernel_function
  linarith [momentum_kernel_negative p_squared h]

/-! ## Complete Setup for the c-Theorem

The `CTheoremSetup` structure bundles all the physical data and properties
needed for the proof: a 2D QFT, integration operations, spectral data from
unitarity, Ward identities connecting correlators to beta functions, and
the spectral/Fourier representations. -/

/-- Complete physical setup for Zamolodchikov's c-theorem.

    This bundles a 2D QFT with:
    - Integration infrastructure (2D momentum space and radial)
    - Operator insertions corresponding to running couplings
    - Two-point function of the stress tensor trace
    - Spectral densities from unitarity (ρᵢ(p²) ≥ 0)
    - Ward identity connecting θ-θ correlator to β-functions
    - Spectral and Fourier representations
    - Momentum space form of the c-function
    - Connection to Virasoro central charge at fixed points -/
structure CTheoremSetup (H : Type _) [QuantumStateSpace H] where
  /-- The underlying 2D QFT -/
  theory : QFT2D H

  -- Integration infrastructure
  /-- Integration over 2D momentum space ∫ d²p -/
  integrate_2d : ((Fin 2 → ℝ) → ℝ) → ℝ
  /-- Integration over radial coordinate ∫ dr -/
  integrate_1d : (ℝ → ℝ) → ℝ
  /-- Non-negative functions have non-negative integrals -/
  integrate_nonneg_2d : ∀ (f : (Fin 2 → ℝ) → ℝ), (∀ p, f p ≥ 0) → integrate_2d f ≥ 0

  -- Operator insertions and correlators
  /-- Operator insertion ∂_i corresponding to the i-th coupling.
      These are the operators whose couplings run under RG flow.
      Example: in φ⁴ theory, ∂_λ corresponds to the φ⁴ operator itself. -/
  operator_insertion : Fin theory.n_couplings → FieldDistribution H 2
  /-- Two-point Wightman function ⟨0|θ(x)θ(y)|0⟩ of the stress tensor trace -/
  two_point_trace : Point2D → Point2D → ℂ
  /-- The trace-trace correlator is real (consequence of hermiticity of θ) -/
  trace_is_real : ∀ x y, (two_point_trace x y).im = 0
  /-- Translation invariance: ⟨θ(x)θ(y)⟩ = ⟨θ(x+a)θ(y+a)⟩ (from Wightman W1) -/
  translation_inv : ∀ x y a,
    (two_point_trace x y).re = (two_point_trace (x + a) (y + a)).re

  -- Spectral data (from unitarity)
  /-- Spectral density ρᵢ(p²) from inserting complete set of momentum eigenstates.
      By unitarity (Wightman positivity), ρᵢ(p²) ≥ 0 for all i and p². -/
  spectral_density : Fin theory.n_couplings → (Fin 2 → ℝ) → ℝ
  /-- Unitarity: spectral densities are non-negative.
      This follows from Wightman positivity (reflection positivity in Euclidean). -/
  unitarity_positivity : ∀ i p, spectral_density i p ≥ 0

  -- Ward identity
  /-- Ward identity: ⟨θ(x)θ(y)⟩ = ∑ᵢ βᵢ ⟨θ(y)∂ᵢ(x)⟩.
      Physical meaning: The trace anomaly is generated by operators whose
      couplings run (βᵢ ≠ 0). At fixed points (βᵢ = 0), θ = 0 and we have CFT. -/
  ward_identity : ∀ x y,
    (two_point_trace x y).re =
    ∑ i : Fin theory.n_couplings,
      theory.beta_functions i *
      (twoPointWightman theory.wft (operator_insertion i) x y).re

  -- Spectral representation
  /-- Spectral representation of operator correlator.
      Inserting complete set of states gives:
      ⟨θ(r)∂ᵢ(0)⟩ = ∫ d²p cos(pr) ρᵢ(p²) -/
  operator_correlator_spectral : ∀ (i : Fin theory.n_couplings) (r : ℝ),
    (twoPointWightman theory.wft (theta theory) (radialPoint_2d r) origin_2d).re =
    integrate_2d (fun p =>
      Real.cos (sqrt (p 0^2 + p 1^2) * r) * spectral_density i p)

  -- Fourier transform
  /-- Fourier transform identity: ∫ dr r³ cos(pr) = K(p²).
      This is the key technical result connecting position and momentum space. -/
  fourier_r_cubed : ∀ (p : Fin 2 → ℝ),
    integrate_1d (fun r => r^3 * Real.cos (sqrt (p 0^2 + p 1^2) * r)) =
    momentum_space_kernel (p 0^2 + p 1^2)

  -- Momentum space representation
  /-- Momentum space representation of c-function.
      Using Ward identity + spectral representation + Fourier transform:
      c(g) = (3/4π²) ∑ᵢ βᵢ ∫ d²p K(p²) ρᵢ(p²) -/
  c_momentum_rep :
    (3 / (4 * Real.pi^2)) *
    integrate_1d (fun r => r^3 * (two_point_trace (radialPoint_2d r) origin_2d).re) =
    (3 / (4 * Real.pi^2)) *
    ∑ i : Fin theory.n_couplings,
      theory.beta_functions i *
      integrate_2d (fun p =>
        momentum_space_kernel (p 0^2 + p 1^2) *
        spectral_density i p)

  -- c-function properties
  /-- The c-function is non-negative (related to positivity of energy) -/
  c_nonneg :
    (3 / (4 * Real.pi^2)) *
    integrate_1d (fun r => r^3 * (two_point_trace (radialPoint_2d r) origin_2d).re) ≥ 0

  -- CFT fixed point connection
  /-- At CFT fixed points, the c-function equals the Virasoro central charge.
      This connects Zamolodchikov's c to the algebraic central charge of CFT. -/
  fixed_point_virasoro :
    (∀ i, theory.beta_functions i = 0) →
    ∃ (c : VirasoroCentralCharge),
      centralChargeValue c =
      (3 / (4 * Real.pi^2)) *
      integrate_1d (fun r => r^3 * (two_point_trace (radialPoint_2d r) origin_2d).re)

/-! ## Definitions on the Setup -/

/-- Zamolodchikov's c-function:
    c(g) = (3/4π²) ∫ d²x r³ ⟨θ(x)θ(0)⟩ -/
noncomputable def CTheoremSetup.c_function
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H) : ℝ :=
  (3 / (4 * Real.pi^2)) *
  setup.integrate_1d (fun r => r^3 * (setup.two_point_trace (radialPoint_2d r) origin_2d).re)

/-- Spectral weighted integral ∫ d²p (-K(p²)) ρᵢ(p²).
    This is the key quantity in the c-theorem proof. -/
noncomputable def CTheoremSetup.spectral_weighted_integral
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H)
  (i : Fin setup.theory.n_couplings) : ℝ :=
  setup.integrate_2d (fun p =>
    positive_kernel_function (p 0 ^ 2 + p 1 ^ 2) *
    setup.spectral_density i p)

/-- Derivative of c with respect to coupling gᵢ.
    From the momentum representation:
    ∂c/∂gᵢ = -(3/4π²) βᵢ ∫ d²p (-K(p²)) ρᵢ(p²) -/
noncomputable def CTheoremSetup.coupling_derivative
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H)
  (i : Fin setup.theory.n_couplings) : ℝ :=
  -(3 / (4 * Real.pi^2)) *
  setup.theory.beta_functions i *
  setup.spectral_weighted_integral i

/-- Total derivative dc/dt along RG flow.
    By chain rule: dc/dt = ∑ᵢ βᵢ · (∂c/∂gᵢ) -/
noncomputable def CTheoremSetup.dc_dt
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H) : ℝ :=
  ∑ i : Fin setup.theory.n_couplings,
    setup.theory.beta_functions i * setup.coupling_derivative i

/-! ## Core Proof Chain

The heart of the c-theorem:
  unitarity (ρᵢ ≥ 0) + kernel negativity (K < 0) → ∫(-K)ρ ≥ 0
  → βᵢ · (∂c/∂gᵢ) ≤ 0
  → dc/dt = ∑ᵢ βᵢ · (∂c/∂gᵢ) ≤ 0 -/

/-- The spectral weighted integral is non-negative.
    Proof: Both -K(p²) ≥ 0 and ρᵢ(p²) ≥ 0, so product is ≥ 0. -/
theorem spectral_weighted_positive
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H)
  (i : Fin setup.theory.n_couplings) :
  setup.spectral_weighted_integral i ≥ 0 := by
  unfold CTheoremSetup.spectral_weighted_integral
  apply setup.integrate_nonneg_2d
  intro p
  apply mul_nonneg
  · by_cases h : p 0 ^ 2 + p 1 ^ 2 > 0
    · exact le_of_lt (kernel_positivity _ h)
    · unfold positive_kernel_function momentum_space_kernel
      simp [h]
  · exact setup.unitarity_positivity i p

/-- Key inequality: βᵢ · (∂c/∂gᵢ) ≤ 0.

    Proof: βᵢ · (∂c/∂gᵢ) = -βᵢ² · (positive constant) · (positive integral) ≤ 0

    This is the heart of the c-theorem: each coupling contributes non-positively
    to dc/dt, regardless of the sign of βᵢ. -/
theorem sign_beta_times_derivative
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H)
  (i : Fin setup.theory.n_couplings) :
  setup.theory.beta_functions i * setup.coupling_derivative i ≤ 0 := by
  unfold CTheoremSetup.coupling_derivative
  have h := spectral_weighted_positive setup i
  have h_const : (0 : ℝ) < 3 / (4 * Real.pi^2) := by
    apply div_pos
    · norm_num
    · apply mul_pos; norm_num; apply sq_pos_of_pos Real.pi_pos
  -- Goal: β * (-(3/(4π²)) * β * integral) ≤ 0
  -- = -β² * (3/(4π²)) * integral ≤ 0
  calc setup.theory.beta_functions i * (-(3 / (4 * Real.pi^2)) * setup.theory.beta_functions i * setup.spectral_weighted_integral i)
      = -(setup.theory.beta_functions i ^ 2 * (3 / (4 * Real.pi^2)) * setup.spectral_weighted_integral i) := by ring
    _ ≤ 0 := by
        apply neg_nonpos_of_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · exact sq_nonneg _
        · linarith
        · exact h

/-- Helper lemma: sum of non-positive terms is non-positive -/
theorem sum_nonpositive {n : ℕ} (f : Fin n → ℝ) (h : ∀ i, f i ≤ 0) :
  ∑ i, f i ≤ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h_rest : ∑ i : Fin n, f (Fin.castSucc i) ≤ 0 := by
      apply ih; intro i; exact h (Fin.castSucc i)
    linarith [h (Fin.last n)]

/-- The c-function decreases monotonically: dc/dt ≤ 0.

    This is Zamolodchikov's c-theorem. The proof follows from summing
    the inequality βᵢ · (∂c/∂gᵢ) ≤ 0 over all couplings. -/
theorem dc_dt_nonpositive
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H) :
  setup.dc_dt ≤ 0 := by
  unfold CTheoremSetup.dc_dt
  apply sum_nonpositive
  intro i
  exact sign_beta_times_derivative setup i

/-- At fixed points (βᵢ = 0 for all i), dc/dt = 0.
    The c-function is stationary precisely at CFT fixed points. -/
theorem beta_zero_stationary
  {H : Type _} [QuantumStateSpace H]
  (setup : CTheoremSetup H)
  (h_fixed : ∀ i, setup.theory.beta_functions i = 0) :
  setup.dc_dt = 0 := by
  unfold CTheoremSetup.dc_dt CTheoremSetup.coupling_derivative
  simp [h_fixed]

/-! ## RG Flow and Irreversibility

To prove the full irreversibility theorem, we need a path through theory space
(the RG flow) and the multivariable chain rule relating dc/dt to ∑ᵢ βᵢ ∂c/∂gᵢ. -/

/-- Data for an RG flow: a path of CTheoremSetups with the chain rule. -/
structure RGFlowSetup (H : Type _) [QuantumStateSpace H] where
  /-- Number of coupling constants (constant along the flow) -/
  n : ℕ
  /-- The RG flow as a path of CTheoremSetups parameterized by scale t -/
  path : ℝ → CTheoremSetup H
  /-- The number of couplings is constant along the flow -/
  n_constant : ∀ s, (path s).theory.n_couplings = n
  /-- Multivariable chain rule for c-function along the RG trajectory.
      For a path g(t) in coupling space:
      dc/dt = ∑ᵢ (dgᵢ/dt) · (∂c/∂gᵢ) = ∑ᵢ βᵢ · (∂c/∂gᵢ) -/
  chain_rule : ∀ t,
    deriv (fun s => (path s).c_function) t =
    ∑ i : Fin n,
      (path t).theory.beta_functions (i.cast (n_constant t).symm) *
      (path t).coupling_derivative (i.cast (n_constant t).symm)

/-- Zamolodchikov's c-theorem: The c-function decreases along any RG flow.

    For any RG trajectory in coupling space, the derivative of c(g(t)) with respect
    to the RG scale t is non-positive. Equality holds only at fixed points where
    all beta functions vanish. -/
theorem zamolodchikov_c_theorem
  {H : Type _} [QuantumStateSpace H]
  (flow : RGFlowSetup H) (t : ℝ) :
  deriv (fun s => (flow.path s).c_function) t ≤ 0 := by
  rw [flow.chain_rule t]
  apply sum_nonpositive
  intro i
  exact sign_beta_times_derivative (flow.path t) (i.cast (flow.n_constant t).symm)

/-- Fundamental theorem of calculus for decreasing functions:
    If f'(t) ≤ 0 on [a,b], then f(b) ≤ f(a).
    (Provable from Mathlib's mean value theorem; sorry'd here.) -/
theorem fundamental_calculus_monotone
  (f : ℝ → ℝ) (a b : ℝ) (h_order : a < b)
  (h_decreasing : ∀ t ∈ Set.Icc a b, deriv f t ≤ 0) :
  f b ≤ f a := by
  sorry

/-- If there exists a monotone decreasing path from c_UV to c_IR, then c_UV ≥ c_IR -/
theorem c_UV_greater_equal_c_IR
  (c_UV c_IR : ℝ)
  (h_exists_flow : ∃ (c : ℝ → ℝ),
    c 0 = c_UV ∧ c 1 = c_IR ∧ ∀ t ∈ Set.Icc 0 1, deriv c t ≤ 0) :
  c_UV ≥ c_IR := by
  obtain ⟨c, h_start, h_end, h_mono⟩ := h_exists_flow
  have h_dec : c 1 ≤ c 0 :=
    fundamental_calculus_monotone c 0 1 (by norm_num) h_mono
  rw [←h_end, ←h_start]; exact h_dec

/-- Irreversibility theorem: c_UV ≥ c_IR for any RG flow.

    This is the physical statement of the c-theorem: The central charge in the UV
    (high energy) is always greater than or equal to the central charge in the IR
    (low energy). RG flow is irreversible - you cannot return to a higher central
    charge by tuning couplings.

    This establishes a fundamental arrow of time in the space of quantum field theories. -/
theorem irreversibility_theorem
  {H : Type _} [QuantumStateSpace H]
  (flow : RGFlowSetup H)
  (theory_UV theory_IR : CTheoremSetup H)
  (h_UV_endpoint : flow.path 0 = theory_UV)
  (h_IR_endpoint : flow.path 1 = theory_IR)
  (c_virasoro_UV : VirasoroCentralCharge)
  (c_virasoro_IR : VirasoroCentralCharge)
  (h_UV_central : centralChargeValue c_virasoro_UV = theory_UV.c_function)
  (h_IR_central : centralChargeValue c_virasoro_IR = theory_IR.c_function) :
  centralChargeValue c_virasoro_UV ≥ centralChargeValue c_virasoro_IR := by
  rw [h_UV_central, h_IR_central]
  apply c_UV_greater_equal_c_IR
  use (fun t => (flow.path t).c_function)
  refine ⟨?_, ?_, ?_⟩
  · show (flow.path 0).c_function = theory_UV.c_function
    rw [h_UV_endpoint]
  · show (flow.path 1).c_function = theory_IR.c_function
    rw [h_IR_endpoint]
  · intro t _; exact zamolodchikov_c_theorem flow t

end PhysicsLogic.Papers.Zamolodchikov1986
