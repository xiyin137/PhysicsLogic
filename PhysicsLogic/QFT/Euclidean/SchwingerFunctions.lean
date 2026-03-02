import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PhysicsLogic.Units

namespace PhysicsLogic.QFT.Euclidean

open Real

/-- Euclidean spacetime point in d dimensions -/
abbrev EuclideanPoint (d : ℕ) := Fin d → ℝ

/-- The origin (zero point) in d-dimensional Euclidean space -/
def euclideanOrigin (d : ℕ) : EuclideanPoint d := fun _ => 0

/-- Euclidean distance (positive definite metric) -/
noncomputable def euclideanDistance {d : ℕ} (x y : EuclideanPoint d) : LengthScale :=
  (sqrt (∑ μ, (x μ - y μ)^2) : ℝ)

/-- Orthogonal matrix in `d` Euclidean dimensions. -/
def IsOrthogonal {d : ℕ} (R : Fin d → Fin d → ℝ) : Prop :=
  ∀ μ ν, ∑ ρ, R μ ρ * R ν ρ = if μ = ν then 1 else 0

/-- Radial distance from origin -/
noncomputable def radialDistance {d : ℕ} (x : EuclideanPoint d) : LengthScale :=
  euclideanDistance x (euclideanOrigin d)

/-- A quantum field theory in d dimensions, characterized by its Schwinger functions.

    The Schwinger functions S_n(x₁,...,xₙ) = ⟨φ(x₁)...φ(xₙ)⟩_E are the Euclidean
    correlation functions that define the theory. All physical observables can be
    extracted from these functions.

    Euclidean covariance is encoded directly via translation and rotation invariance below.
    The remaining Osterwalder-Schrader axioms (reflection positivity, cluster property,
    growth bound) are formulated in `OsterwalderSchrader.lean` as `OSAxioms`. -/
structure QFT (d : ℕ) where
  /-- The n-point Schwinger functions ⟨φ(x₁)...φ(xₙ)⟩_E -/
  schwinger : (n : ℕ) → (Fin n → EuclideanPoint d) → ℝ
  /-- Translation invariance: correlations depend only on differences -/
  translation_invariant : ∀ n (points : Fin n → EuclideanPoint d) (a : EuclideanPoint d),
    schwinger n points = schwinger n (fun i μ => points i μ + a μ)
  /-- Rotational invariance under Euclidean orthogonal transformations. -/
  rotation_invariant : ∀ n (points : Fin n → EuclideanPoint d)
    (rotation : Fin d → Fin d → ℝ),
    IsOrthogonal rotation →
    schwinger n points = schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν)
  /-- Permutation symmetry (bosonic fields) -/
  permutation_symmetric : ∀ n (points : Fin n → EuclideanPoint d) (σ : Equiv.Perm (Fin n)),
    schwinger n points = schwinger n (points ∘ σ)

/-- Complex-valued Euclidean QFT interface.
    This is the physically general case (charged fields/spin structures can
    produce complex Schwinger functions), while `QFT` above keeps a lightweight
    real-valued interface for minimal modules. -/
structure ComplexQFT (d : ℕ) where
  /-- Complex Schwinger functions ⟨φ(x₁)...φ(xₙ)⟩_E. -/
  schwinger : (n : ℕ) → (Fin n → EuclideanPoint d) → ComplexAmplitude
  /-- Translation invariance. -/
  translation_invariant : ∀ n (points : Fin n → EuclideanPoint d) (a : EuclideanPoint d),
    schwinger n points = schwinger n (fun i μ => points i μ + a μ)
  /-- Rotational invariance under O(d). -/
  rotation_invariant : ∀ n (points : Fin n → EuclideanPoint d)
    (rotation : Fin d → Fin d → ℝ),
    IsOrthogonal rotation →
    schwinger n points = schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν)
  /-- Bosonic permutation symmetry. -/
  permutation_symmetric : ∀ n (points : Fin n → EuclideanPoint d) (σ : Equiv.Perm (Fin n)),
    schwinger n points = schwinger n (points ∘ σ)

/-- Combined Euclidean covariance from translation and rotational invariance. -/
theorem QFT.euclidean_covariance {d : ℕ} (theory : QFT d)
    (n : ℕ)
    (rotation : Fin d → Fin d → ℝ)
    (h_orthogonal : IsOrthogonal rotation)
    (translation : EuclideanPoint d)
    (points : Fin n → EuclideanPoint d) :
    theory.schwinger n points =
    theory.schwinger n (fun i μ => translation μ + ∑ ν, rotation μ ν * points i ν) := by
  have h_rot :
      theory.schwinger n points =
      theory.schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν) :=
    theory.rotation_invariant n points rotation h_orthogonal
  have h_trans :
      theory.schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν) =
      theory.schwinger n (fun i μ => (∑ ν, rotation μ ν * points i ν) + translation μ) :=
    theory.translation_invariant n (fun i μ => ∑ ν, rotation μ ν * points i ν) translation
  calc
    theory.schwinger n points =
        theory.schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν) := h_rot
    _ =
        theory.schwinger n (fun i μ => (∑ ν, rotation μ ν * points i ν) + translation μ) :=
          h_trans
    _ =
        theory.schwinger n (fun i μ => translation μ + ∑ ν, rotation μ ν * points i ν) := by
          congr
          funext i μ
          simp [add_comm]

/-- Combined Euclidean covariance for the complex-valued interface. -/
theorem ComplexQFT.euclidean_covariance {d : ℕ} (theory : ComplexQFT d)
    (n : ℕ)
    (rotation : Fin d → Fin d → ℝ)
    (h_orthogonal : IsOrthogonal rotation)
    (translation : EuclideanPoint d)
    (points : Fin n → EuclideanPoint d) :
    theory.schwinger n points =
    theory.schwinger n (fun i μ => translation μ + ∑ ν, rotation μ ν * points i ν) := by
  have h_rot :
      theory.schwinger n points =
      theory.schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν) :=
    theory.rotation_invariant n points rotation h_orthogonal
  have h_trans :
      theory.schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν) =
      theory.schwinger n (fun i μ => (∑ ν, rotation μ ν * points i ν) + translation μ) :=
    theory.translation_invariant n (fun i μ => ∑ ν, rotation μ ν * points i ν) translation
  calc
    theory.schwinger n points =
        theory.schwinger n (fun i μ => ∑ ν, rotation μ ν * points i ν) := h_rot
    _ =
        theory.schwinger n (fun i μ => (∑ ν, rotation μ ν * points i ν) + translation μ) :=
          h_trans
    _ =
        theory.schwinger n (fun i μ => translation μ + ∑ ν, rotation μ ν * points i ν) := by
          congr
          funext i μ
          simp [add_comm]

/-- Embed a real-valued Euclidean QFT as a complex-valued one. -/
def QFT.toComplex {d : ℕ} (theory : QFT d) : ComplexQFT d where
  schwinger := fun n points => (theory.schwinger n points : ℂ)
  translation_invariant := by
    intro n points a
    exact congrArg (fun r : ℝ => (r : ℂ)) (theory.translation_invariant n points a)
  rotation_invariant := by
    intro n points rotation h_orthogonal
    exact congrArg (fun r : ℝ => (r : ℂ))
      (theory.rotation_invariant n points rotation h_orthogonal)
  permutation_symmetric := by
    intro n points σ
    exact congrArg (fun r : ℝ => (r : ℂ)) (theory.permutation_symmetric n points σ)

/-- Vacuum expectation value ⟨φ⟩: the 1-point function at the origin -/
def vev {d : ℕ} (theory : QFT d) : ℝ :=
  theory.schwinger 1 (fun _ => euclideanOrigin d)

/-- 2-point correlation function for a specific theory -/
noncomputable def correlationFunction {d : ℕ} (theory : QFT d) (x y : EuclideanPoint d) : ℝ :=
  theory.schwinger 2 (fun i => if i = 0 then x else y)

/-- Correlation length ξ ~ 1/m -/
noncomputable def correlationLength (m : MassScale) : LengthScale := 1 / m

/-- A theory has a mass gap m > 0 if correlations decay exponentially
    with rate m. NOT all theories have a mass gap (e.g., massless theories). -/
structure HasMassGap {d : ℕ} (theory : QFT d) (m : MassScale) where
  m_pos : m > 0
  /-- Correlations decay exponentially: |⟨φ(x)φ(y)⟩| ≤ C e^{-m|x-y|} -/
  decay_bound : ∃ C > 0, ∀ x y : EuclideanPoint d,
    |correlationFunction theory x y| ≤ C * exp (-(m * euclideanDistance x y).value)

/-- Exponential decay of correlations (mass gap).
    For a theory WITH mass gap m > 0, correlations decay exponentially.
    NOTE: This is a property of specific theories, not a universal law. -/
theorem exponential_decay {d : ℕ} (theory : QFT d) (m : MassScale) (h : HasMassGap theory m)
  (x y : EuclideanPoint d) :
  ∃ C > 0, |correlationFunction theory x y| ≤
    C * exp (-(m * euclideanDistance x y).value) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := h.decay_bound
  exact ⟨C, hC_pos, hC_bound x y⟩

/- ============= MASSIVE KERNEL (EUCLIDEAN PROPAGATOR) ============= -/

/-- The massive Euclidean propagator data: K_d(m, r) in d dimensions.
    This is the Fourier transform of 1/(k² + m²), the free scalar propagator.

    In Core we specify it abstractly through its defining properties
    (exponential decay, logarithmic behavior in 2D massless limit).
    Rigorous construction via Bessel functions belongs in RigorousQFT. -/
structure MassiveKernelData where
  /-- The massive Euclidean propagator K_d(m, r) in d dimensions -/
  kernel : (d : ℕ) → (m : MassScale) → (r : LengthScale) → ℝ
  /-- For any mass m > 0, the massive kernel decays exponentially in d dimensions -/
  kernel_decay : ∀ {d : ℕ} (m : MassScale) (_hm : m > 0),
    ∃ C > 0, ∀ r : LengthScale, r ≥ 0 → |kernel d m r| ≤ C * exp (-(m * r).value)
  /-- In 2D, the massless kernel K(0,r) has logarithmic behavior for large r -/
  massless_2d_logarithmic :
    ∀ (r : LengthScale), r > 1 → ∃ ε_r : ℝ,
      kernel 2 0 r = -log r.value + ε_r ∧
      |ε_r| ≤ 1

/-- Spectral density ρ(m²) in the Källén-Lehmann representation. -/
structure SpectralDensity (d : ℕ) where
  /-- The spectral weight function ρ(m²) ≥ 0 -/
  ρ : MassSquaredScale → ℝ
  /-- Positivity: spectral density is non-negative -/
  nonneg : ∀ mSq, mSq ≥ 0 → ρ mSq ≥ 0
  /-- Support: spectral density vanishes for negative mass² -/
  support : ∀ mSq, mSq < 0 → ρ mSq = 0

/-- A QFT admits a spectral (Källén-Lehmann) representation if its 2-point
    function can be decomposed into a sum over mass eigenstates.

    By translation invariance, we work with ⟨φ(x)φ(0)⟩.
    The spectral representation is:
    ⟨φ(x)φ(0)⟩ = ∫₀^∞ dm² ρ(m²) K_d(√m², |x|)
    where the integral includes both:
    - Isolated poles (single-particle states): δ(m² - m₀²)
    - Continuum (multi-particle states): smooth ρ(m²) -/
structure HasSpectralRepresentation {d : ℕ} (theory : QFT d) where
  spectral : SpectralDensity d
  /-- Spectral integral prediction for the two-point function. -/
  spectralTwoPoint : EuclideanPoint d → ℝ
  /-- The 2-point function admits the spectral decomposition -/
  decomposition : ∀ x : EuclideanPoint d,
    correlationFunction theory x (euclideanOrigin d) = spectralTwoPoint x
    -- In a full formalization, this would be the actual integral
    -- ∫₀^∞ dm² spectral.ρ(m²) · K.kernel d (√m²) (radialDistance x)

/-- Isolated mass: a delta function contribution δ(m² - m₀²) to the spectral density,
    representing a stable single-particle state of mass m₀. -/
structure IsolatedMass {d : ℕ} (K : MassiveKernelData) (spec : SpectralDensity d)
    (m₀ : MassScale) where
  /-- The residue Z > 0 (field strength renormalization) -/
  residue : ℝ
  residue_pos : residue > 0
  /-- Pole contribution profile from the isolated mass shell m₀. -/
  poleContribution : EuclideanPoint d → ℝ
  /-- Pole contribution equals residue times the massive kernel. -/
  pole_contribution_formula : ∀ (x : EuclideanPoint d),
    poleContribution x = residue * K.kernel d m₀ (radialDistance x)

/-- Spectral decomposition: correlation function splits into isolated poles + continuum.
    For a theory with isolated masses, the 2-point function is:
    ⟨φ(x)φ(0)⟩ = Σᵢ Zᵢ·K(mᵢ, |x|) + ∫_continuum ρ(m²)·K(m, |x|) dm²

    The continuum contribution comes from multi-particle states. For massless theories,
    the two-particle threshold starts at m=0, so the continuum can contribute additional
    logarithmic terms in 2D. We only know: ρ(m²) ≥ 0 (positivity). -/
structure SpectralDecomposition {d : ℕ} (theory : QFT d)
    (spec : HasSpectralRepresentation theory) where
  /-- Contribution from continuum (multi-particle states and higher-mass single particles) -/
  continuum_part : EuclideanPoint d → ℝ
  /-- If the continuum has a mass gap m_gap > 0 (i.e., ρ(m²) = 0 for 0 < m² < m_gap²),
      then it decays exponentially. This holds when all isolated poles are at discrete masses. -/
  has_mass_gap : Option MassScale
  /-- If has_mass_gap = some(m_gap) with m_gap > 0, then continuum decays exponentially -/
  continuum_decay_with_gap : ∀ m_gap : MassScale, has_mass_gap = some m_gap → m_gap > 0 →
    ∃ C > 0, ∀ x : EuclideanPoint d,
    |continuum_part x| ≤ C * exp (-(m_gap * radialDistance x).value)

end PhysicsLogic.QFT.Euclidean
