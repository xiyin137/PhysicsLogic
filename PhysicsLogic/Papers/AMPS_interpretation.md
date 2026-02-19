# The AMPS Firewall Paradox in Lean 4

This document is a faithful interpretation of the content formalized in `AMPS_clean.lean`.

## Setup

A `BlackHole` carries a single predicate `is_old`, representing whether the black hole has evaporated past the Page time (when more than half its initial Bekenstein-Hawking entropy has been radiated).

An `AMPSSetup bh` models the four-partite quantum system E ⊗ L ⊗ Ã ⊗ B' associated with an evaporating black hole `bh`, where:

- E = early Hawking radiation (already collected by a distant observer)
- L = a late Hawking mode (outgoing, recently emitted)
- Ã = interior partner mode of L (one mode behind the horizon)
- B' = rest of the black hole interior (excluding Ã)

The setup bundles six real-valued von Neumann entropies S_E, S_L, S_A, S_EL, S_LA, S_total for the subsystems E, L, Ã, EL, LÃ, ELÃB' respectively, together with two quantum information properties and three physical postulates.

### Quantum information properties

1. **Schmidt decomposition** (`schmidt_L_A`): If the Hawking pair LÃ is in a pure state (S(LÃ) = 0), then the reduced entropies are equal: S(L) = S(Ã). This is the Schmidt decomposition theorem applied to the bipartition L | Ã.

2. **Pure subsystem factorization** (`product_from_purity`): If the global state ELÃB' is pure (S_total = 0) and the Hawking pair LÃ is pure (S(LÃ) = 0), then S(EL) = S(E) + S(L). Physically: a pure subsystem of a pure global state factors out, so the global state is |α⟩_{EB'} ⊗ |ψ⟩_{LÃ}, making E and L a product state with additive entropy.

### Physical postulates

1. **Unitarity** (`unitarity`): The global state ELÃB' is pure: S_total = 0. Black hole evaporation preserves quantum information.

2. **EFT / No Drama** (`eft`): The Hawking pair (L, Ã) is in the Unruh vacuum, a pure entangled state: S(LÃ) = 0. Quantum field theory in curved spacetime is valid at the horizon, and a freely falling observer encounters nothing unusual.

3. **Page's theorem** (`page_theorem`): If the black hole is old (past the Page time), then the late Hawking mode L is entangled with the early radiation E: S(EL) < S(E) + S(L), equivalently I(E:L) > 0. This follows from unitarity combined with the Bekenstein-Hawking entropy formula counting black hole microstates, via Page's theorem for the entanglement structure of random states.

## The AMPS firewall paradox (proven)

For an old black hole, the three postulates are mutually inconsistent.

    amps_firewall_paradox : AMPSSetup bh → bh.is_old → False

Proof: `product_from_purity` applied to `unitarity` and `eft` gives S(EL) = S(E) + S(L), i.e., I(E:L) = 0. But `page_theorem` applied to `is_old` gives S(EL) < S(E) + S(L), i.e., I(E:L) > 0. These are contradictory.

## Mutual information analysis (proven)

Mutual information is defined as I(E:L) = S(E) + S(L) − S(EL) and I(L:Ã) = S(L) + S(Ã) − S(LÃ).

1. **EFT implies maximal L-Ã entanglement** (`eft_maximal_LA_entanglement`): I(L:Ã) = 2S(L). From `eft`, S(LÃ) = 0; from `schmidt_L_A`, S(L) = S(Ã); so I(L:Ã) = S(L) + S(L) − 0 = 2S(L). This is the maximum possible mutual information for a bipartite system, saturated by pure entangled states.

2. **EFT + unitarity kill E-L correlations** (`eft_no_EL_correlation`): I(E:L) = 0. Direct consequence of `product_from_purity`: S(EL) = S(E) + S(L) gives I(E:L) = 0.

3. **The paradox in mutual information form** (`amps_mutual_info_contradiction`): For an old black hole, I(E:L) = 0 ∧ I(E:L) > 0. All of L's correlations go to its interior partner Ã (I(L:Ã) = 2S(L)), leaving none for E (I(E:L) = 0). But Page's theorem requires L to be correlated with E (I(E:L) > 0).

## Equivalence principle (proven)

The equivalence principle (`equivalence_principle`) is defined as I(L:Ã) > 0: the Hawking pair is entangled, representing a smooth horizon.

    eft_implies_equivalence : S(L) > 0 → equivalence_principle

From `eft_maximal_LA_entanglement`, I(L:Ã) = 2S(L). If S(L) > 0 (the Hawking mode is nontrivial), then I(L:Ã) > 0. The equivalence principle is therefore not an independent postulate but a consequence of EFT.

## Alternative resolutions (defined)

Three resolutions are identified, corresponding to giving up each postulate:

1. **Information loss** (`resolution_information_loss`): S_total > 0. Give up unitarity — the global state is mixed. Pure subsystem factorization no longer applies, so I(E:L) = 0 is not forced. Problem: violates quantum mechanics.

2. **Firewall** (`resolution_firewall`): S(LÃ) > 0. Give up EFT — the Hawking pair is not pure. The state does not factorize, so L can be entangled with E. Problem: violates the equivalence principle; the horizon becomes a singular surface.

3. **ER=EPR** (comment only, not formalized): The tensor product decomposition E ⊗ L ⊗ Ã ⊗ B' is invalid. The early radiation and interior are connected by an Einstein-Rosen bridge, so `product_from_purity` does not apply. This cannot be expressed as a condition on entropy values within the four-partite model, since it questions the model itself.

## Conditional entropy (proven)

The conditional entropy S(L|E) = S(EL) − S(E) measures how much uncertainty remains about L given knowledge of E. Unlike classical conditional entropy, the quantum version can be negative, indicating entanglement.

    conditional_entropy_equals_S_L : S(L|E) = S(L)

From `product_from_purity`, S(EL) = S(E) + S(L), so S(L|E) = S(L). Conditioning on E does not reduce uncertainty about L, confirming that L and E are uncorrelated under unitarity + EFT.

## What is and isn't proven

Everything in the file is fully machine-checked with no `sorry` and no axioms beyond Lean's type theory and Mathlib.

The physical content is encoded in the structure fields of `AMPSSetup`: six entropy values, two quantum information properties (Schmidt decomposition and pure subsystem factorization), and three physical postulates (unitarity, EFT, Page's theorem). The main theorem shows these are jointly inconsistent for an old black hole, and all secondary results are derived consequences.

The formalization captures the logical structure of the AMPS argument faithfully: the contradiction arises because EFT forces L into a product state with E (via pure subsystem factorization), while Page's theorem demands L be entangled with E. The four-partite system E ⊗ L ⊗ Ã ⊗ B' correctly models the original AMPS setup where Ã is one mode inside a much larger black hole, requiring Page's theorem (rather than a simpler Schmidt argument) to establish the contradiction.
