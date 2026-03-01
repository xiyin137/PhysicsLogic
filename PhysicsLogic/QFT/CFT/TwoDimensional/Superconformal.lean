import PhysicsLogic.Assumptions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Algebra.Basic

namespace PhysicsLogic.QFT.CFT.TwoDimensional

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Neveu-Schwarz / Ramond choice for supercurrent mode indexing. -/
inductive NSRSector where
  | NS
  | R
deriving DecidableEq, Repr

/-- Endomorphisms of a complex state space. -/
abbrev Endomorphism (H : Type*) [AddCommGroup H] [Module ℂ H] := Module.End ℂ H

/-- Kronecker delta used in mode-algebra central terms. -/
def kroneckerDelta (a b : ℚ) : ℂ :=
  if a = b then 1 else 0

/-- Integer mode predicate (`r ∈ ℤ`). -/
def isIntegerMode (r : ℚ) : Prop :=
  ∃ n : ℤ, r = n

/-- Half-integer mode predicate (`r ∈ ℤ + 1/2`). -/
def isHalfIntegerMode (r : ℚ) : Prop :=
  ∃ n : ℤ, r = n + (1 / 2 : ℚ)

/-- Half-integer lattice predicate (`r ∈ (1/2)ℤ`). -/
def isHalfIntegerLattice (r : ℚ) : Prop :=
  ∃ n : ℤ, r = (n : ℚ) / 2

/-- Sector-compatible mode condition for ${\cal N}=1,2$ generators. -/
def sectorCompatible (sector : NSRSector) (r : ℚ) : Prop :=
  match sector with
  | NSRSector.NS => isHalfIntegerMode r
  | NSRSector.R => isIntegerMode r

/-- Operator commutator. -/
def opComm {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : Endomorphism H) : Endomorphism H :=
  A * B - B * A

/-- Operator anticommutator. -/
def opAntiComm {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : Endomorphism H) : Endomorphism H :=
  A * B + B * A

/-- Graded anticommutator-zero condition on superspace endomorphisms. -/
def superAntiCommute {S : Type*} [AddGroup S] (A B : S → S) : Prop :=
  ∀ Φ : S, A (B Φ) = - B (A Φ)

/-- Basic `(1,1)` superspace derivative/supercharge package. -/
structure Superspace11Operators (S : Type*) where
  dZ : S → S
  dZBar : S → S
  Dθ : S → S
  DθBar : S → S
  Qθ : S → S
  QθBar : S → S

/-- `(1,1)` superspace algebra:
`D_θ² = ∂_z`, `D_{\bar θ}² = ∂_{\bar z}`, and supercharge anticommutation with derivatives. -/
def Superspace11DerivativeAlgebra {S : Type*} [AddGroup S]
    (ops : Superspace11Operators S) : Prop :=
  (∀ Φ : S, ops.Dθ (ops.Dθ Φ) = ops.dZ Φ) ∧
  (∀ Φ : S, ops.DθBar (ops.DθBar Φ) = ops.dZBar Φ) ∧
  superAntiCommute ops.Dθ ops.DθBar ∧
  superAntiCommute ops.Qθ ops.Dθ ∧
  superAntiCommute ops.Qθ ops.DθBar ∧
  superAntiCommute ops.QθBar ops.Dθ ∧
  superAntiCommute ops.QθBar ops.DθBar

/-- Assumed `(1,1)` superspace derivative/supercharge algebra from Appendix J. -/
theorem superspace11_derivative_algebra {S : Type*} [AddGroup S]
    (ops : Superspace11Operators S)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dSuperspace11DerivativeAlgebra
      (Superspace11DerivativeAlgebra ops)) :
    Superspace11DerivativeAlgebra ops := by
  exact h_phys

/-- Holomorphic ${\cal N}=1$ superconformal mode data. -/
structure N1SuperconformalData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  L : ℚ → Endomorphism H
  G : ℚ → Endomorphism H
  centralCharge : ℂ
  sector : NSRSector

/-- ${\cal N}=1$ SCA mode relations:
`[L_n,G_r] = (n/2-r) G_{n+r}` and
`{G_r,G_s} = 2L_{r+s} + (c/12)(4r^2-1)δ_{r,-s}`. -/
def N1SuperconformalModeAlgebra {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N1SuperconformalData H) : Prop :=
  (∀ n : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.L n) (data.G r) =
      (((n : ℂ) / 2) - (r : ℂ)) • data.G (n + r)) ∧
  (∀ r s : ℚ, sectorCompatible data.sector r → sectorCompatible data.sector s →
    opAntiComm (data.G r) (data.G s) =
      (2 : ℂ) • data.L (r + s) +
        ((data.centralCharge / 12) * (4 * (r : ℂ) ^ (2 : ℕ) - 1) * kroneckerDelta r (-s))
          • (1 : Endomorphism H))

/-- Ramond zero-mode cylinder relation `L_0 - c/24 = G_0^2` in anticommutator form. -/
def N1RamondCylinderRelation {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N1SuperconformalData H) : Prop :=
  data.sector = NSRSector.R →
    opAntiComm (data.G 0) (data.G 0) =
      (2 : ℂ) • (data.L 0 - (data.centralCharge / 24) • (1 : Endomorphism H))

/-- Combined ${\cal N}=1$ superconformal package used in this abstraction layer. -/
def N1SuperconformalAlgebraPackage {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N1SuperconformalData H) : Prop :=
  N1SuperconformalModeAlgebra data ∧ N1RamondCylinderRelation data

/-- Assumed Appendix-J ${\cal N}=1$ superconformal algebra package. -/
theorem n1_superconformal_algebra_package {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N1SuperconformalData H)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dN1SuperconformalAlgebra
      (N1SuperconformalAlgebraPackage data)) :
    N1SuperconformalAlgebraPackage data := by
  exact h_phys

/-- `(2,2)` superspace derivative package. -/
structure Superspace22Operators (S : Type*) where
  DPlus : S → S
  DMinus : S → S
  DBarPlus : S → S
  DBarMinus : S → S

/-- Chiral-superfield constraint in `(2,2)` superspace. -/
def ChiralSuperfield {S : Type*} [Zero S] (ops : Superspace22Operators S) (Z : S) : Prop :=
  ops.DBarPlus Z = 0 ∧ ops.DBarMinus Z = 0

/-- Anti-chiral-superfield constraint in `(2,2)` superspace. -/
def AntiChiralSuperfield {S : Type*} [Zero S] (ops : Superspace22Operators S) (Z : S) : Prop :=
  ops.DPlus Z = 0 ∧ ops.DMinus Z = 0

/-- Data describing reduction of `(2,2)` chiral superspace expressions to `(1,1)` form. -/
structure Superspace22ReductionData (S22 S11 : Type*) where
  ops22 : Superspace22Operators S22
  to11 : S22 → S11
  DTheta11 : S11 → S11
  DThetaBar11 : S11 → S11
  pullbackDMinus : S22 → S11
  pullbackDBarPlus : S22 → S11

/-- Reduction interface: chiral `(2,2)` data maps to `(1,1)` superderivative data. -/
def Superspace22To11Reduction {S22 S11 : Type*} [Zero S22]
    (data : Superspace22ReductionData S22 S11) : Prop :=
  ∀ Z : S22, ChiralSuperfield data.ops22 Z →
    data.DThetaBar11 (data.to11 Z) = data.pullbackDMinus Z ∧
      data.DTheta11 (data.to11 Z) = data.pullbackDBarPlus Z

/-- Assumed `(2,2)` chiral-constraint and `(1,1)` reduction interface from Appendix J. -/
theorem superspace22_to11_reduction {S22 S11 : Type*} [Zero S22]
    (data : Superspace22ReductionData S22 S11)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dSuperspace22ChiralReduction
      (Superspace22To11Reduction data)) :
    Superspace22To11Reduction data := by
  exact h_phys

/-- Holomorphic ${\cal N}=2$ superconformal mode data. -/
structure N2SuperconformalData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  L : ℚ → Endomorphism H
  Gplus : ℚ → Endomorphism H
  Gminus : ℚ → Endomorphism H
  J : ℚ → Endomorphism H
  centralCharge : ℂ
  sector : NSRSector

/-- ${\cal N}=2$ SCA mode relations in operator form. -/
def N2SuperconformalModeAlgebra {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N2SuperconformalData H) : Prop :=
  (∀ n : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.L n) (data.Gplus r) =
      (((n : ℂ) / 2) - (r : ℂ)) • data.Gplus (n + r)) ∧
  (∀ n : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.L n) (data.Gminus r) =
      (((n : ℂ) / 2) - (r : ℂ)) • data.Gminus (n + r)) ∧
  (∀ m n : ℤ,
    opComm (data.L m) (data.J n) = (-(n : ℂ)) • data.J (m + n)) ∧
  (∀ r s : ℚ, sectorCompatible data.sector r → sectorCompatible data.sector s →
    opAntiComm (data.Gplus r) (data.Gminus s) =
      (2 : ℂ) • data.L (r + s) +
        ((r : ℂ) - (s : ℂ)) • data.J (r + s) +
        ((data.centralCharge / 3) * ((r : ℂ) ^ (2 : ℕ) - (1 / 4 : ℂ)) * kroneckerDelta r (-s))
          • (1 : Endomorphism H)) ∧
  (∀ r s : ℚ, sectorCompatible data.sector r → sectorCompatible data.sector s →
    opAntiComm (data.Gplus r) (data.Gplus s) = 0) ∧
  (∀ r s : ℚ, sectorCompatible data.sector r → sectorCompatible data.sector s →
    opAntiComm (data.Gminus r) (data.Gminus s) = 0) ∧
  (∀ n : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.J n) (data.Gplus r) = data.Gplus (n + r)) ∧
  (∀ n : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.J n) (data.Gminus r) = -data.Gminus (n + r)) ∧
  (∀ m n : ℤ,
    opComm (data.J m) (data.J n) =
      ((data.centralCharge / 3) * (m : ℂ) * kroneckerDelta m (-n))
        • (1 : Endomorphism H))

/-- Assumed Appendix-J ${\cal N}=2$ superconformal mode algebra. -/
theorem n2_superconformal_mode_algebra {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N2SuperconformalData H)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dN2SuperconformalAlgebra
      (N2SuperconformalModeAlgebra data)) :
    N2SuperconformalModeAlgebra data := by
  exact h_phys

/-- Data for ${\cal N}=2$ spectral-flow automorphism. -/
structure N2SpectralFlowData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  base : N2SuperconformalData H
  eta : ℚ
  Lflow : ℚ → Endomorphism H
  GplusFlow : ℚ → Endomorphism H
  GminusFlow : ℚ → Endomorphism H
  Jflow : ℚ → Endomorphism H

/-- ${\cal N}=2$ spectral-flow transformation rules. -/
def N2SpectralFlowAutomorphism {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N2SpectralFlowData H) : Prop :=
  (isIntegerMode data.eta ∨ isHalfIntegerMode data.eta) ∧
  (∀ n : ℤ,
    data.Lflow n = data.base.L n +
      (data.eta : ℂ) • data.base.J n +
        (((data.eta : ℂ) ^ (2 : ℕ)) * data.base.centralCharge / 6 * kroneckerDelta n 0)
          • (1 : Endomorphism H)) ∧
  (∀ r : ℚ, data.GplusFlow r = data.base.Gplus (r + data.eta)) ∧
  (∀ r : ℚ, data.GminusFlow r = data.base.Gminus (r - data.eta)) ∧
  (∀ n : ℤ,
    data.Jflow n = data.base.J n +
      (((data.eta : ℂ) * data.base.centralCharge / 3) * kroneckerDelta n 0)
        • (1 : Endomorphism H))

/-- Assumed Appendix-J ${\cal N}=2$ spectral-flow automorphism. -/
theorem n2_spectral_flow_automorphism {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : N2SpectralFlowData H)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dN2SpectralFlowAutomorphism
      (N2SpectralFlowAutomorphism data)) :
    N2SpectralFlowAutomorphism data := by
  exact h_phys

/-- Small ${\cal N}=4$ SCA mode package used in this abstraction layer. -/
structure SmallN4SuperconformalData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  level : ℕ
  L : ℚ → Endomorphism H
  J3 : ℚ → Endomorphism H
  Jplus : ℚ → Endomorphism H
  Jminus : ℚ → Endomorphism H
  Gplus : ℚ → Endomorphism H
  Gminus : ℚ → Endomorphism H
  centralCharge : ℂ
  sector : NSRSector

/-- Selected small ${\cal N}=4$ SCA mode relations and level/central-charge relation. -/
def SmallN4ModeAlgebra {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : SmallN4SuperconformalData H) : Prop :=
  data.centralCharge = (6 : ℂ) * data.level ∧
  (∀ m n : ℤ,
    opComm (data.J3 m) (data.J3 n) =
      (((data.level : ℂ) / 2) * (m : ℂ) * kroneckerDelta m (-n))
        • (1 : Endomorphism H)) ∧
  (∀ m n : ℤ,
    opComm (data.J3 m) (data.Jplus n) = data.Jplus (m + n)) ∧
  (∀ m n : ℤ,
    opComm (data.J3 m) (data.Jminus n) = -data.Jminus (m + n)) ∧
  (∀ m n : ℤ,
    opComm (data.Jplus m) (data.Jminus n) =
      (2 : ℂ) • data.J3 (m + n) +
        (((data.level : ℂ) * (m : ℂ)) * kroneckerDelta m (-n))
          • (1 : Endomorphism H)) ∧
  (∀ m : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.J3 m) (data.Gplus r) = (1 / 2 : ℂ) • data.Gplus (m + r)) ∧
  (∀ m : ℤ, ∀ r : ℚ, sectorCompatible data.sector r →
    opComm (data.J3 m) (data.Gminus r) = (-(1 / 2 : ℂ)) • data.Gminus (m + r))

/-- Assumed Appendix-J small ${\cal N}=4$ SCA mode relations. -/
theorem small_n4_mode_algebra {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : SmallN4SuperconformalData H)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dN4SmallSuperconformalAlgebra
      (SmallN4ModeAlgebra data)) :
    SmallN4ModeAlgebra data := by
  exact h_phys

/-- Data for small ${\cal N}=4$ spectral-flow inner automorphism. -/
structure SmallN4SpectralFlowData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  base : SmallN4SuperconformalData H
  eta : ℚ
  J3flow : ℚ → Endomorphism H
  JplusFlow : ℚ → Endomorphism H
  JminusFlow : ℚ → Endomorphism H
  Lflow : ℚ → Endomorphism H
  GplusFlow : ℚ → Endomorphism H
  GminusFlow : ℚ → Endomorphism H

/-- Small ${\cal N}=4$ spectral-flow rules (`η ∈ 1/2 ℤ`). -/
def SmallN4SpectralFlow {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : SmallN4SpectralFlowData H) : Prop :=
  isHalfIntegerLattice data.eta ∧
  (∀ n : ℤ,
    data.J3flow n = data.base.J3 n +
      (((data.eta : ℂ) * (data.base.level : ℂ)) * kroneckerDelta n 0)
        • (1 : Endomorphism H)) ∧
  (∀ n : ℚ, data.JplusFlow n = data.base.Jplus (n + 2 * data.eta)) ∧
  (∀ n : ℚ, data.JminusFlow n = data.base.Jminus (n - 2 * data.eta)) ∧
  (∀ n : ℤ,
    data.Lflow n = data.base.L n +
      (2 * (data.eta : ℂ)) • data.base.J3 n +
      (((data.eta : ℂ) ^ (2 : ℕ) * (data.base.level : ℂ)) * kroneckerDelta n 0)
        • (1 : Endomorphism H)) ∧
  (∀ r : ℚ, data.GplusFlow r = data.base.Gplus (r + data.eta)) ∧
  (∀ r : ℚ, data.GminusFlow r = data.base.Gminus (r - data.eta))

/-- Assumed Appendix-J small ${\cal N}=4$ spectral-flow inner automorphism. -/
theorem small_n4_spectral_flow {H : Type*} [AddCommGroup H] [Module ℂ H]
    (data : SmallN4SpectralFlowData H)
    (h_phys : PhysicsAssumption
      AssumptionId.cft2dN4SpectralFlowInnerAutomorphism
      (SmallN4SpectralFlow data)) :
    SmallN4SpectralFlow data := by
  exact h_phys

end PhysicsLogic.QFT.CFT.TwoDimensional
