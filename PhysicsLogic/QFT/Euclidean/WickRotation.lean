import PhysicsLogic.QFT.Euclidean.OsterwalderSchrader
import PhysicsLogic.QFT.Wightman.WightmanFunctions
import PhysicsLogic.Assumptions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.QFT.Euclidean

open SpaceTime Wightman PhysicsLogic.QFT.Euclidean Real

/-- A vector η ∈ ℝᵈ lies in the open forward light cone if η₀ > 0 and
    η² < 0 (in mostly-plus signature: -η₀² + |η⃗|² < 0, i.e., η₀ > |η⃗|). -/
def inForwardCone {d : ℕ} [NeZero d] (η : Fin d → ℝ) : Prop :=
  η 0 > 0 ∧ (η 0)^2 > ∑ i : Fin d, if i = 0 then 0 else (η i)^2

/-- The forward tube T_n in complexified spacetime.

    T_n = {(z₁,...,zₙ) ∈ ℂⁿᵈ : Im(ζₖ) ∈ V₊ for all k}

    where ζₖ = zₖ - zₖ₋₁ are successive differences and V₊ is the open forward
    light cone. This is the domain to which Wightman functions analytically continue. -/
def inForwardTube {d : ℕ} [NeZero d] (n : ℕ) (z : Fin n → (Fin d → ℂ)) : Prop :=
  ∀ k : Fin n,
    let prev : Fin d → ℂ := if k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin d → ℝ := fun μ => (z k μ - prev μ).im
    inForwardCone η

/-- Appendix-D analytic-continuation domain interface:
the continuation domain for `n`-point functions is identified with the forward tube. -/
def WightmanEuclideanAnalyticContinuationDomain {d : ℕ} [NeZero d]
    (n : ℕ)
    (domain : (Fin n → (Fin d → ℂ)) → Prop) : Prop :=
  domain = inForwardTube n

/-- Assumed Appendix-D forward-tube domain identification for Wightman-to-Euclidean
analytic continuation. -/
theorem wightman_euclidean_analytic_continuation_domain {d : ℕ} [NeZero d]
    (n : ℕ)
    (domain : (Fin n → (Fin d → ℂ)) → Prop)
    (h_phys : PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.wightmanEuclideanAnalyticContinuationDomain
      (WightmanEuclideanAnalyticContinuationDomain n domain)) :
    WightmanEuclideanAnalyticContinuationDomain n domain := by
  exact h_phys

/-- A Wightman function with analytic continuation to the forward tube.

    The Wightman n-point function W_n, initially defined as a tempered distribution
    on real spacetime, extends to a holomorphic function W_analytic on the forward
    tube T_n. The boundary values of W_analytic recover the original distribution. -/
structure AnalyticWightmanFunction (d : ℕ) [NeZero d] (n : ℕ) where
  /-- The Wightman function on real spacetime points (boundary value) -/
  W : (Fin n → (Fin d → ℝ)) → ℂ
  /-- The analytic continuation to complexified spacetime -/
  W_analytic : (Fin n → (Fin d → ℂ)) → ℂ
  /-- The analytic continuation agrees with W on real points -/
  boundary_value : ∀ (x : Fin n → (Fin d → ℝ)),
    W x = W_analytic (fun i μ => (x i μ : ℂ))

/- ============= WICK ROTATION ============= -/

/-- Wick rotation data: analytic continuation t → -iτ from Minkowski to Euclidean.
    Only well-defined when the Wightman function satisfies analyticity conditions.

    The Wick rotation relates:
    - Minkowski correlators W_n(x₁,...,xₙ) (oscillatory, distributional)
    - Euclidean correlators S_n(x₁,...,xₙ) (exponentially damped, regular functions)

    via analytic continuation through the forward tube domain. -/
structure WickRotationData (d : ℕ) [NeZero d] where
  /-- Wick rotation map: given an analytic Wightman function, produce Schwinger functions -/
  wickRotation : ∀ (n : ℕ) (_W_analytic : AnalyticWightmanFunction d n),
    (Fin n → EuclideanPoint d) → ℂ

/-- Ordering-compatible Euclidean insertion data:
the Euclidean time coordinates are weakly increasing with insertion label. -/
def EuclideanTimeOrdered {d : ℕ} [NeZero d]
    (n : ℕ) (points : Fin n → EuclideanPoint d) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → points i 0 ≤ points j 0

/-- Appendix-D interface for analytic continuation from Lorentzian Wightman
data to Euclidean correlators, with ordering/analytic-domain dependence
implicit in the chosen `AnalyticWightmanFunction`. -/
def WightmanToEuclideanContinuation {d : ℕ} [NeZero d]
    (n : ℕ)
    (W : AnalyticWightmanFunction d n)
    (wick : WickRotationData d)
    (euclideanCorrelator : (Fin n → EuclideanPoint d) → ℂ) : Prop :=
  ∀ points : Fin n → EuclideanPoint d,
    EuclideanTimeOrdered n points →
    euclideanCorrelator points = wick.wickRotation n W points

/-- Osterwalder-Schrader reconstruction theorem (corrected version):
    A Euclidean QFT with E1 covariance (already in `QFT`) and OS axioms E2-E5
    can be analytically continued to a relativistic Wightman QFT.

    CRITICAL: This version includes the growth bound axiom E5 that was missing in
    the original 1973 paper and added in the 1975 follow-up. Without E5, the
    reconstruction fails due to non-convergence of the GNS construction.

    The theorem guarantees existence of analytic Wightman functions that,
    when Wick rotated, reproduce the Schwinger functions. -/
theorem os_reconstruction_theorem {d : ℕ} [NeZero d]
  (theory : QFT d)
  (_os : OSAxioms theory)
  (wick : WickRotationData d)
  (h_phys :
    PhysicsLogic.PhysicsAssumption
      PhysicsLogic.AssumptionId.osReconstruction
      (∀ (n : ℕ), ∃ (W : AnalyticWightmanFunction d n),
        ∀ euclidean_points : Fin n → EuclideanPoint d,
          (theory.schwinger n euclidean_points : ℂ) = wick.wickRotation n W euclidean_points)) :
  -- Conclusion: All n-point Schwinger functions are analytic continuations
  ∀ (n : ℕ), ∃ (W : AnalyticWightmanFunction d n),
    ∀ euclidean_points : Fin n → EuclideanPoint d,
      (theory.schwinger n euclidean_points : ℂ) = wick.wickRotation n W euclidean_points := by
  exact h_phys

end PhysicsLogic.QFT.Euclidean
