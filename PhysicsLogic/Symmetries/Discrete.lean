import PhysicsLogic.SpaceTime.Basic
import Mathlib.Data.Complex.Basic

namespace PhysicsLogic.Symmetries

open SpaceTime

/-- Structure for charge conjugation C (particle ↔ antiparticle)
    Abstract operator - acts on quantum states, fields, etc. -/
structure ChargeConjugation (H : Type*) where
  /-- Charge conjugation operator -/
  op : H → H
  /-- C is involutive: C² = 1 -/
  involutive : ∀ (ψ : H), op (op ψ) = ψ

/-- Parity P: spatial inversion on spacetime together with its action on states. -/
structure Parity (H : Type*) where
  /-- Parity action on Hilbert-space states. -/
  op_state : H → H
  /-- Parity is involutive on states: P² = 1. -/
  involutive_state : ∀ (ψ : H), op_state (op_state ψ) = ψ
  /-- Parity action on spacetime points. -/
  op_spacetime : SpaceTimePoint → SpaceTimePoint
  /-- Spacetime parity is involutive. -/
  involutive_spacetime : ∀ (x : SpaceTimePoint), op_spacetime (op_spacetime x) = x
  /-- Parity preserves time coordinate. -/
  preserves_time : ∀ (x : SpaceTimePoint), (op_spacetime x) 0 = x 0
  /-- Parity flips spatial coordinates. -/
  inverts_space : ∀ (x : SpaceTimePoint) (i : Fin 3), (op_spacetime x) i.succ = -(x i.succ)

/-- Structure for time reversal T (t → -t, antiunitary) -/
structure TimeReversal (H : Type*) [SMul ℂ H] where
  /-- Time reversal operator on Hilbert space -/
  op : H → H
  /-- Wigner phase in T² = η_T (typically ±1 on irreducible sectors). -/
  t_square_phase : ℂ
  /-- η_T is a two-torsion phase. -/
  t_square_phase_square : t_square_phase * t_square_phase = 1
  /-- Time reversal squares to a phase on states. -/
  square_action : ∀ (ψ : H), op (op ψ) = t_square_phase • ψ
  /-- Time reversal on spacetime -/
  op_spacetime : SpaceTimePoint → SpaceTimePoint
  /-- T reverses time: t → -t -/
  reverses_time : ∀ (x : SpaceTimePoint), (op_spacetime x) 0 = -(x 0)
  /-- T preserves space: x → x -/
  preserves_space : ∀ (x : SpaceTimePoint) (i : Fin 3), (op_spacetime x) i.succ = x i.succ

/-- Combined CPT symmetry -/
structure CPTSymmetry (H : Type*) [SMul ℂ H] where
  C : ChargeConjugation H
  P : Parity H
  T : TimeReversal H

/-- Combined CPT action on states: Θ = C ∘ P ∘ T. -/
def CPTSymmetry.combined {H : Type*} [SMul ℂ H] (cpt : CPTSymmetry H) : H → H :=
  fun ψ => cpt.C.op (cpt.P.op_state (cpt.T.op ψ))

/-- CPT theorem data: a Lorentz-invariant local QFT admits a CPT symmetry
    such that the combined CPT operation Θ = CPT is antiunitary and involutive.

    The full PCT theorem for Wightman QFT (with proper Wightman function
    transformation law) is stated in QFT/Wightman/Theorems.lean. -/
structure CPTTheorem (H : Type*) [SMul ℂ H] where
  /-- CPT symmetry instance -/
  cpt : CPTSymmetry H
  /-- Combined CPT is involutive: (CPT)² = id -/
  cpt_involutive : ∀ (ψ : H), cpt.combined (cpt.combined ψ) = ψ

end PhysicsLogic.Symmetries
