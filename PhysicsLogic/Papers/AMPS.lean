import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The AMPS Firewall Paradox (Almheiri-Marolf-Polchinski-Sully 2012)

This module formalizes the AMPS firewall paradox, which shows that three
postulates about black holes are mutually inconsistent:

1. **Unitarity**: Black hole evaporation preserves quantum information
2. **EFT / No drama**: The Hawking pair is produced in the Unruh vacuum
3. **Page's theorem**: For an old black hole, each new Hawking mode is
   entangled with the early radiation

## The System

The system is four-partite: E ⊗ L ⊗ Ã ⊗ B' where:
- E = early Hawking radiation (already collected by a distant observer)
- L = a late Hawking mode (outgoing, recently emitted)
- Ã = interior partner mode of L (one mode behind the horizon)
- B' = rest of the black hole interior (excluding Ã)

## The Argument

1. Unitarity: the global state is pure, S(ELÃB') = 0
2. EFT: the Hawking pair is in the Unruh vacuum, S(LÃ) = 0
3. Pure subsystem factorization: since both the global state and the LÃ
   subsystem are pure, the global state factors as |α⟩_{EB'} ⊗ |ψ⟩_{LÃ},
   making E and L uncorrelated: I(E:L) = 0
4. Page's theorem: for an old black hole, L is entangled with E: I(E:L) > 0
5. Contradiction

## Monogamy of Entanglement

The AMPS argument is often described as using "monogamy of entanglement":
L cannot be maximally entangled with both E and Ã simultaneously. The precise
mechanism is that EFT forces LÃ into a pure state, which factorizes it from
the rest of the system, killing all correlations between L and E.

Monogamy applies to *quantum entanglement measures* (concurrence, entanglement
of formation), NOT to mutual information. Mutual information is NOT monogamous:
the GHZ state |000⟩ + |111⟩ satisfies I(A:B) = I(A:C) = S(A) simultaneously.
The AMPS argument uses the stronger property that a pure bipartite subsystem
is in a product state with everything else.
-/

namespace AMPS

set_option autoImplicit false

-- ========================================
-- BLACK HOLE
-- ========================================

/-- An evaporating black hole. The AMPS argument only needs the predicate
    `is_old`: whether the black hole has evaporated past the Page time
    (when more than half its initial Bekenstein-Hawking entropy has been
    radiated). -/
structure BlackHole where
  is_old : Prop

-- ========================================
-- AMPS SETUP: FOUR-PARTITE SYSTEM E ⊗ L ⊗ Ã ⊗ B'
-- ========================================

/-- AMPS setup: entropy data for a four-partite system E ⊗ L ⊗ Ã ⊗ B'
    around an evaporating black hole `bh`.

    E = early Hawking radiation (collected by distant observer)
    L = late Hawking mode (recently emitted)
    Ã = interior partner mode of L (one mode behind the horizon)
    B' = rest of the black hole interior (excluding Ã)

    Unlike a tripartite simplification where Ã would be the entire interior,
    here Ã is one mode inside a much larger black hole. The contradiction
    requires Page's theorem to establish that L should be entangled with E. -/
structure AMPSSetup (bh : BlackHole) where
  /-- S(E): von Neumann entropy of early radiation -/
  S_E : ℝ
  /-- S(L): von Neumann entropy of late Hawking mode -/
  S_L : ℝ
  /-- S(Ã): von Neumann entropy of interior partner -/
  S_A : ℝ
  /-- S(EL): von Neumann entropy of early radiation + late mode -/
  S_EL : ℝ
  /-- S(LÃ): von Neumann entropy of Hawking pair -/
  S_LA : ℝ
  /-- S(ELÃB'): von Neumann entropy of total system -/
  S_total : ℝ
  /-- Schmidt decomposition within the pure Hawking pair: S(L) = S(Ã).
      For a pure bipartite state, the reduced entropies of the two parts
      are equal. -/
  schmidt_L_A : S_LA = 0 → S_L = S_A
  /-- Pure subsystem factorization: if the global state is pure and the
      Hawking pair LÃ is pure, the global state factors as
      |α⟩_{EB'} ⊗ |ψ⟩_{LÃ}. This makes E and L a product state:
      S(EL) = S(E) + S(L), equivalently I(E:L) = 0. -/
  product_from_purity : S_total = 0 → S_LA = 0 → S_EL = S_E + S_L
  /-- **Postulate 1 (Unitarity)**: The global state ELÃB' is pure. -/
  unitarity : S_total = 0
  /-- **Postulate 2 (EFT / No Drama)**: The Hawking pair (L,Ã) is in the
      Unruh vacuum — a pure entangled state. -/
  eft : S_LA = 0
  /-- **Postulate 3 (Page's theorem)**: For an old black hole, each new
      Hawking mode L is entangled with the early radiation E: I(E:L) > 0.
      This follows from unitarity + Bekenstein-Hawking entropy counting
      microstates, via Page's theorem for random states. -/
  page_theorem : bh.is_old → S_EL < S_E + S_L

-- ========================================
-- THE AMPS FIREWALL PARADOX
-- ========================================

/-- **The AMPS Firewall Paradox**: For an old black hole, unitarity + EFT +
    Page's theorem are mutually inconsistent.

    EFT + unitarity force I(E:L) = 0 (via pure subsystem factorization),
    but Page's theorem demands I(E:L) > 0. -/
theorem amps_firewall_paradox {bh : BlackHole} (setup : AMPSSetup bh)
    (h_old : bh.is_old) : False := by
  have h_product := setup.product_from_purity setup.unitarity setup.eft
  linarith [setup.page_theorem h_old]

-- ========================================
-- MUTUAL INFORMATION ANALYSIS
-- ========================================

noncomputable def mutual_info_EL {bh : BlackHole} (s : AMPSSetup bh) : ℝ :=
  s.S_E + s.S_L - s.S_EL

noncomputable def mutual_info_LA {bh : BlackHole} (s : AMPSSetup bh) : ℝ :=
  s.S_L + s.S_A - s.S_LA

/-- EFT implies L and Ã are maximally entangled: I(L:Ã) = 2S(L). -/
theorem eft_maximal_LA_entanglement {bh : BlackHole} (setup : AMPSSetup bh) :
    mutual_info_LA setup = 2 * setup.S_L := by
  unfold mutual_info_LA
  linarith [setup.schmidt_L_A setup.eft, setup.eft]

/-- EFT + unitarity force L to be uncorrelated with E: I(E:L) = 0. -/
theorem eft_no_EL_correlation {bh : BlackHole} (setup : AMPSSetup bh) :
    mutual_info_EL setup = 0 := by
  unfold mutual_info_EL
  linarith [setup.product_from_purity setup.unitarity setup.eft]

/-- The AMPS paradox in mutual information form:
    I(E:L) = 0 from EFT + unitarity, but I(E:L) > 0 from Page's theorem. -/
theorem amps_mutual_info_contradiction {bh : BlackHole} (setup : AMPSSetup bh)
    (h_old : bh.is_old) :
    mutual_info_EL setup = 0 ∧ mutual_info_EL setup > 0 := by
  exact ⟨eft_no_EL_correlation setup,
    by unfold mutual_info_EL; linarith [setup.page_theorem h_old]⟩

-- ========================================
-- EQUIVALENCE PRINCIPLE
-- ========================================

/-- **Equivalence Principle / No Drama**: A freely falling observer sees
    nothing unusual at the horizon. This requires I(L:Ã) > 0.
    Implied by EFT when S(L) > 0 (the Hawking mode is nontrivial). -/
def equivalence_principle {bh : BlackHole} (setup : AMPSSetup bh) : Prop :=
  mutual_info_LA setup > 0

theorem eft_implies_equivalence {bh : BlackHole} (setup : AMPSSetup bh)
    (h_nontrivial : setup.S_L > 0) :
    equivalence_principle setup := by
  unfold equivalence_principle
  linarith [eft_maximal_LA_entanglement setup]

-- ========================================
-- ALTERNATIVE RESOLUTIONS
-- ========================================

/-- **Resolution 1: Information Loss** (Hawking 1975)
    Give up unitarity: S(ELÃB') > 0. The global state is mixed, so pure
    subsystem factorization does not apply and I(E:L) = 0 is not forced. -/
def resolution_information_loss (S_total : ℝ) : Prop := S_total > 0

/-- **Resolution 2: Firewall** (AMPS 2012)
    Give up EFT: S(LÃ) > 0. The Hawking pair is not in a pure state,
    so the state does not factorize and L can be entangled with E. -/
def resolution_firewall (S_LA : ℝ) : Prop := S_LA > 0

-- **Resolution 3: ER=EPR** (Maldacena-Susskind 2013)
--
-- The tensor product decomposition E ⊗ L ⊗ Ã ⊗ B' is invalid:
-- the early radiation and interior are connected by an Einstein-Rosen
-- bridge (wormhole). The geometric connection means product_from_purity
-- does not apply — the subsystems are not independent.
--
-- This cannot be expressed as a condition on entropy values within
-- the four-partite model, since it questions the model itself.

-- ========================================
-- CONDITIONAL ENTROPY
-- ========================================

/-- Conditional entropy S(L|E) = S(EL) - S(E).
    Quantum conditional entropy can be negative (unlike classical),
    indicating entanglement. -/
noncomputable def conditional_entropy_L_given_E {bh : BlackHole} (s : AMPSSetup bh) : ℝ :=
  s.S_EL - s.S_E

/-- EFT + unitarity imply S(L|E) = S(L): L and E are uncorrelated. -/
theorem conditional_entropy_equals_S_L {bh : BlackHole} (setup : AMPSSetup bh) :
    conditional_entropy_L_given_E setup = setup.S_L := by
  unfold conditional_entropy_L_given_E
  linarith [setup.product_from_purity setup.unitarity setup.eft]

end AMPS
