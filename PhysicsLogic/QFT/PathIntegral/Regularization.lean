-- ModularPhysics/Core/QFT/PathIntegral/Regularization.lean
-- Regularization and renormalization of path integrals
--
-- The path integral ∫ Dφ e^{iS[φ]} is typically divergent.
-- Regularization introduces a UV cutoff to make it finite:
--   Z(Λ) = ∫_{|k|<Λ} Dφ e^{iS[φ]}
--
-- Renormalization tunes the bare parameters as Λ → ∞ to obtain
-- finite physical predictions (when possible).
import PhysicsLogic.QFT.PathIntegral.PathIntegrals
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= REGULARIZATION SCHEMES ============= -/

/-- UV cutoff: a scale Λ above which modes are suppressed. -/
structure UVCutoff where
  /-- The cutoff scale -/
  scale : ℝ
  /-- Cutoff is positive -/
  positive : scale > 0

/-- Regularization scheme: a procedure for making the path integral finite.
    Different schemes exist, each with advantages:
    - Lattice: manifestly gauge-invariant, preserves unitarity
    - Dimensional: preserves gauge symmetry, good for perturbation theory
    - Pauli-Villars: respects gauge invariance for abelian theories
    - Zeta function: elegant, good for curved spacetime -/
structure RegularizationScheme (F : Type*) where
  /-- The regularized path integral as a function of the cutoff -/
  regularized_integral : UVCutoff → FieldMeasure F
  /-- The regularized action -/
  regularized_action : UVCutoff → ActionFunctional F

/-- Lattice regularization: replace spacetime continuum by a discrete lattice.
    Field configurations become functions on lattice sites.
    Path integral becomes a finite-dimensional integral. -/
structure LatticeRegularization where
  /-- Lattice spacing a > 0 -/
  spacing : ℝ
  /-- Spacing is positive -/
  spacing_positive : spacing > 0

/-- Lattice path integral: the regularized path integral on a lattice.
    This is a well-defined finite-dimensional integral over lattice field values. -/
structure LatticePathIntegralData (F : Type*) where
  /-- The lattice -/
  lattice : LatticeRegularization
  /-- The lattice action (sum over lattice sites/links) -/
  lattice_action : ActionFunctional F
  /-- The lattice measure (product of on-site measures) -/
  lattice_measure : FieldMeasure F

/-- Continuum limit: take lattice spacing a → 0.
    This requires tuning bare couplings g(a) to approach a critical point
    (second-order phase transition in statistical mechanics language).

    The bare couplings must flow along an RG trajectory to a UV fixed point.
    When no such fixed point exists, the theory is said to be trivial
    (e.g., φ⁴ theory in d > 4 dimensions). -/
structure ContinuumLimitData (F : Type*) where
  /-- Lattice theories parameterized by lattice spacing -/
  lattice_theories : LatticeRegularization → LatticePathIntegralData F
  /-- Bare couplings as function of lattice spacing -/
  bare_couplings : LatticeRegularization → List ℝ
  /-- A fixed point of the couplings (limit as a → 0) -/
  fixed_point_couplings : List ℝ
  /-- The couplings converge to the fixed point as lattice spacing → 0:
      for each coupling component i, |g_i(a) - g_i*| → 0 as a → 0 -/
  approaches_fixed_point : ∀ (i : ℕ) (hi : i < fixed_point_couplings.length) (ε : ℝ),
    ε > 0 → ∃ a₀ > 0,
    ∀ (a : LatticeRegularization), a.spacing < a₀ →
    i < (bare_couplings a).length ∧
    |(bare_couplings a)[i]! - fixed_point_couplings[i]!| < ε

/-- Dimensional regularization: analytically continue spacetime dimension d → d - ε.
    Poles in 1/ε capture UV divergences.
    This preserves gauge symmetry and is the standard for perturbative calculations. -/
structure DimensionalRegularizationData (F : Type*) where
  /-- The regularized amplitude as a function of ε = 4 - d -/
  regulated_amplitude : ℝ → ℂ
  /-- The renormalization scale μ -/
  renormalization_scale : ℝ
  /-- Scale is positive -/
  scale_positive : renormalization_scale > 0

/-- Pauli-Villars regularization: add heavy auxiliary fields that cancel
    divergences at high momenta. -/
structure PauliVillarsRegularization where
  /-- Regulator masses (heavy auxiliary fields) -/
  regulator_masses : List ℝ
  /-- Signs of the regulator fields (alternating to cancel divergences) -/
  signs : List ℤ
  /-- Signs are ±1 -/
  sign_constraint : ∀ i : Fin signs.length, signs[i] = 1 ∨ signs[i] = -1

/- ============= RENORMALIZATION ============= -/

/-- Counterterm structure: to cancel divergences, add counterterms to the action.
    S_renormalized = S_bare + δS where δS cancels UV divergences.

    The key insight of renormalizability: only finitely many counterterms
    (corresponding to relevant and marginal operators) are needed. -/
structure CountertermData (F : Type*) where
  /-- The bare action -/
  bare_action : ActionFunctional F
  /-- Counterterms (divergent parts to be subtracted) -/
  counterterms : UVCutoff → ActionFunctional F
  /-- The renormalized action -/
  renormalized_action : ActionFunctional F
  /-- Renormalized = bare + counterterms -/
  renormalization_relation : ∀ (φ : F) (Λ : UVCutoff),
    renormalized_action.eval φ = bare_action.eval φ + (counterterms Λ).eval φ

/- ============= MEASURE THEORY FOR PATH INTEGRALS ============= -/

-- NOTE: The proper Osterwalder-Schrader axioms with full mathematical content
-- are defined in QFT/Euclidean/OsterwalderSchrader.lean as the OSAxioms structure.
-- The OS reconstruction theorem is stated in QFT/Euclidean/WickRotation.lean.

end PhysicsLogic.QFT.PathIntegral
