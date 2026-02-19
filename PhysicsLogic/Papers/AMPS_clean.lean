import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace AMPS_clean

set_option autoImplicit false

structure BlackHole where
  is_old : Prop

structure AMPSSetup (bh : BlackHole) where
  S_E : ℝ
  S_L : ℝ
  S_A : ℝ
  S_EL : ℝ
  S_LA : ℝ
  S_total : ℝ
  schmidt_L_A : S_LA = 0 → S_L = S_A
  product_from_purity : S_total = 0 → S_LA = 0 → S_EL = S_E + S_L
  unitarity : S_total = 0
  eft : S_LA = 0
  page_theorem : bh.is_old → S_EL < S_E + S_L

theorem amps_firewall_paradox {bh : BlackHole} (setup : AMPSSetup bh)
    (h_old : bh.is_old) : False := by
  have h_product := setup.product_from_purity setup.unitarity setup.eft
  linarith [setup.page_theorem h_old]

noncomputable def mutual_info_EL {bh : BlackHole} (s : AMPSSetup bh) : ℝ :=
  s.S_E + s.S_L - s.S_EL

noncomputable def mutual_info_LA {bh : BlackHole} (s : AMPSSetup bh) : ℝ :=
  s.S_L + s.S_A - s.S_LA

theorem eft_maximal_LA_entanglement {bh : BlackHole} (setup : AMPSSetup bh) :
    mutual_info_LA setup = 2 * setup.S_L := by
  unfold mutual_info_LA
  linarith [setup.schmidt_L_A setup.eft, setup.eft]

theorem eft_no_EL_correlation {bh : BlackHole} (setup : AMPSSetup bh) :
    mutual_info_EL setup = 0 := by
  unfold mutual_info_EL
  linarith [setup.product_from_purity setup.unitarity setup.eft]

theorem amps_mutual_info_contradiction {bh : BlackHole} (setup : AMPSSetup bh)
    (h_old : bh.is_old) :
    mutual_info_EL setup = 0 ∧ mutual_info_EL setup > 0 := by
  exact ⟨eft_no_EL_correlation setup,
    by unfold mutual_info_EL; linarith [setup.page_theorem h_old]⟩

def equivalence_principle {bh : BlackHole} (setup : AMPSSetup bh) : Prop :=
  mutual_info_LA setup > 0

theorem eft_implies_equivalence {bh : BlackHole} (setup : AMPSSetup bh)
    (h_nontrivial : setup.S_L > 0) :
    equivalence_principle setup := by
  unfold equivalence_principle
  linarith [eft_maximal_LA_entanglement setup]

def resolution_information_loss (S_total : ℝ) : Prop := S_total > 0

def resolution_firewall (S_LA : ℝ) : Prop := S_LA > 0

noncomputable def conditional_entropy_L_given_E {bh : BlackHole} (s : AMPSSetup bh) : ℝ :=
  s.S_EL - s.S_E

theorem conditional_entropy_equals_S_L {bh : BlackHole} (setup : AMPSSetup bh) :
    conditional_entropy_L_given_E setup = setup.S_L := by
  unfold conditional_entropy_L_given_E
  linarith [setup.product_from_purity setup.unitarity setup.eft]

end AMPS_clean
