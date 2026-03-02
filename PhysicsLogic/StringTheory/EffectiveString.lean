import PhysicsLogic.Assumptions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PhysicsLogic.StringTheory

set_option autoImplicit false

/-- Abstract worldsheet point with one chosen local coordinate chart.
    Physical content is encoded through reparameterization-invariant structures below. -/
structure WorldsheetPoint where
  τ : ℝ
  σ : ℝ

/-- Reparameterization data (diffeomorphism-level abstraction): map with two-sided inverse. -/
structure Reparametrization where
  map : WorldsheetPoint → WorldsheetPoint
  inv : WorldsheetPoint → WorldsheetPoint
  left_inv : ∀ p : WorldsheetPoint, inv (map p) = p
  right_inv : ∀ p : WorldsheetPoint, map (inv p) = p

abbrev Embedding (D : ℕ) := WorldsheetPoint → Fin D → ℝ
abbrev WorldsheetMetric := WorldsheetPoint → WorldsheetPoint → ℝ

/-- Reparameterized embedding `X ∘ ρ`. -/
def Embedding.reparametrize {D : ℕ} (X : Embedding D) (ρ : Reparametrization) : Embedding D :=
  fun p => X (ρ.map p)

/-- Pullback metric under a reparameterization map. -/
def WorldsheetMetric.pullback (h : WorldsheetMetric) (ρ : Reparametrization) : WorldsheetMetric :=
  fun p q => h (ρ.map p) (ρ.map q)

/-- Minimal Nambu-Goto data package. -/
structure NambuGotoData (D : ℕ) where
  tension : TensionScale
  action : Embedding D → ComplexActionValue
  reparam_invariant :
    ∀ (ρ : Reparametrization) (X : Embedding D),
      action (Embedding.reparametrize X ρ) = action X

/-- Minimal Polyakov data package. -/
structure PolyakovData (D : ℕ) where
  inverseStringTension : StringSlope
  action : WorldsheetMetric → Embedding D → ComplexActionValue
  reparam_invariant :
    ∀ (ρ : Reparametrization) (h : WorldsheetMetric) (X : Embedding D),
      action (WorldsheetMetric.pullback h ρ) (Embedding.reparametrize X ρ) = action h X

/-- On-shell equivalence relation between NG and Polyakov actions.
    For each embedding `X`, there exists a worldsheet metric `h` (an on-shell
    representative for that embedding) such that the two actions agree. -/
def NambuGotoPolyakovEquivalent {D : ℕ}
    (ng : NambuGotoData D) (poly : PolyakovData D) : Prop :=
  ∃ onShellMetric : WorldsheetMetric → Embedding D → Prop,
    ∀ (embedding : Embedding D),
      ∃ metric : WorldsheetMetric,
        onShellMetric metric embedding ∧
          ng.action embedding = poly.action metric embedding

/-- Section-02 canonical interface name for Nambu-Goto worldsheet data. -/
abbrev NambuGotoModel (D : ℕ) := NambuGotoData D

/-- Section-02 canonical interface name for Polyakov worldsheet data. -/
abbrev PolyakovModel (D : ℕ) := PolyakovData D

/-- Regge trajectory relation for rotating closed strings. -/
def ReggeTrajectory (tension : TensionScale) (energy : Energy) (spin : ScalingDimension) : Prop :=
  energy.value ^ (2 : ℕ) = 4 * Real.pi * tension.value * spin

/-- Section-02 canonical interface name for the rotating-string Regge law. -/
def ReggeTrajectoryLaw (tension : TensionScale) (energy : Energy) (spin : ScalingDimension) : Prop :=
  ReggeTrajectory tension energy spin

/-- Effective-string assumption: NG and Polyakov classical actions are equivalent. -/
theorem nambu_goto_polyakov_equivalence {D : ℕ}
    (ng : NambuGotoData D)
    (poly : PolyakovData D)
    (h_phys : PhysicsAssumption
      AssumptionId.stringEffectiveNgPolyakovEquivalence
      (NambuGotoPolyakovEquivalent ng poly)) :
    NambuGotoPolyakovEquivalent ng poly := by
  exact h_phys

/-- Effective-string assumption: classical Regge trajectory relation. -/
theorem regge_trajectory
    (tension : TensionScale) (energy : Energy) (spin : ScalingDimension)
    (h_phys : PhysicsAssumption
      AssumptionId.stringEffectiveReggeTrajectory
      (ReggeTrajectory tension energy spin)) :
    ReggeTrajectory tension energy spin := by
  exact h_phys

/-- Data-level Weyl-anomaly cancellation condition in bosonic string quantization. -/
structure BosonicWeylCriticalityData (D : ℕ) where
  matterCentralCharge : ℤ
  ghostCentralCharge : ℤ
  matter_charge : matterCentralCharge = (D : ℤ)
  ghost_charge : ghostCentralCharge = -26
  total_charge_cancel : matterCentralCharge + ghostCentralCharge = 0

/-- In bosonic quantization, central-charge cancellation with the `bc` ghost sector
forces the matter central charge to 26, hence `D = 26` for free bosons. -/
theorem BosonicWeylCriticalityData.dimension_eq_26
    {D : ℕ} (data : BosonicWeylCriticalityData D) : (D : ℤ) = 26 := by
  have h_matter :
      data.matterCentralCharge = -data.ghostCentralCharge :=
    eq_neg_of_add_eq_zero_left data.total_charge_cancel
  rw [data.ghost_charge] at h_matter
  have h_matter26 : data.matterCentralCharge = 26 := by
    simpa using h_matter
  calc
    (D : ℤ) = data.matterCentralCharge := by simp [data.matter_charge]
    _ = 26 := h_matter26

/-- Weyl-anomaly cancellation package for bosonic string quantization.
This is modeled as consistency data, not as a hard-coded numeric definition. -/
def BosonicWeylAnomalyCancellation (D : ℕ) : Prop :=
  Nonempty (BosonicWeylCriticalityData D)

/-- Section-02 canonical criticality interface: bosonic Weyl-anomaly cancellation
as a consistency package (not a hard-coded dimension value). -/
def CriticalBosonicCondition (D : ℕ) : Prop :=
  BosonicWeylAnomalyCancellation D

/-- Weyl-anomaly cancellation in the bosonic theory implies `D = 26`
as a theorem, not as a definitional abbreviation. -/
theorem bosonic_weyl_anomaly_cancellation_implies_dimension_eq_26
    {D : ℕ} (h : BosonicWeylAnomalyCancellation D) : (D : ℤ) = 26 := by
  rcases h with ⟨data⟩
  exact data.dimension_eq_26

/-- Nat-valued form of bosonic criticality consequence: `D = 26`. -/
theorem bosonic_weyl_anomaly_cancellation_implies_dimension_26
    {D : ℕ} (h : BosonicWeylAnomalyCancellation D) : D = 26 := by
  exact Int.ofNat.inj (bosonic_weyl_anomaly_cancellation_implies_dimension_eq_26 h)

/-- Criticality assumption: bosonic-string Weyl-anomaly cancellation package. -/
theorem bosonic_weyl_anomaly_cancellation
    (D : ℕ)
    (h_phys : PhysicsAssumption
      AssumptionId.stringBosonicCriticalDimension
    (BosonicWeylAnomalyCancellation D)) :
    BosonicWeylAnomalyCancellation D := by
  exact h_phys

/-- Section-02 canonical criticality theorem wrapper. -/
theorem critical_bosonic_condition
    (D : ℕ)
    (h_phys : PhysicsAssumption
      AssumptionId.stringBosonicCriticalDimension
      (CriticalBosonicCondition D)) :
    CriticalBosonicCondition D := by
  exact h_phys

end PhysicsLogic.StringTheory
