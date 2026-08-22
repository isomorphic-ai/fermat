/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The basepoint-independent W1 lambda obstruction

The affine W2 criterion may be written without attaching mathematical
meaning to a chosen normalized W3 point.  Any two such points differ by an
element of the full `827` orbit kernel, so their lambda localizations define
one common coset modulo the restricted lambda range.

The literal cokernel class of the missing W1 lambda localization is therefore
independent of the normalized W3 basepoint.  Its vanishing is equivalent to
nonemptiness of the concrete W1+W3 fiber; no vanishing or lift is asserted.
-/
import Fermat.Exponents.FiftyNine.Conservation.LambdaOrbitAffineKernelCriterion827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827

open Fermat.Conservation
open ArbitraryUnitRawTameCarrierBridge827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LambdaOrbitAffineKernelCriterion827
open LambdaOrbitLocalizationFiber827
open NormalizedFullOrbitGlobalRealization827
open PointedTateIncidence
open SplitPrimeFourier827
open TwistedLambdaCupReceipt59
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)

/-- The difference of two normalized W3 points is an actual reflected
q-relaxed adjustment invisible at every place of the full `827` orbit. -/
noncomputable def normalizedW3Difference827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    FullOrbitValuationKernel827 (K := K) omega chi := by
  refine ⟨y₀.1 - y₁.1, ?_⟩
  change
    fullOrbitValuationLocalization827 (K := K) omega chi
        (y₀.1 - y₁.1) = 0
  rw [map_sub]
  have hy₀ :
      fullOrbitValuationLocalization827 (K := K) omega chi y₀.1 =
        normalizedFullOrbitEigenprofileCoordinates827 omega chi := by
    funext tau
    exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
      omega chi y₀ tau
  have hy₁ :
      fullOrbitValuationLocalization827 (K := K) omega chi y₁.1 =
        normalizedFullOrbitEigenprofileCoordinates827 omega chi := by
    funext tau
    exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
      omega chi y₁ tau
  rw [hy₀, hy₁, sub_self]

@[simp]
theorem normalizedW3Difference827_value
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    (normalizedW3Difference827 (K := K) omega chi y₀ y₁).1 =
      y₀.1 - y₁.1 :=
  rfl

/-- The cokernel of lambda localization restricted to adjustments which
preserve the entire normalized W3 orbit profile. -/
abbrev W1LambdaCokernel827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :=
  LambdaRootsContinuousH1 K ⧸
    LinearMap.range (lambdaOnFullOrbitKernel827 (K := K) omega chi)

/-- The canonical projection to the literal W2 cokernel. -/
def w1LambdaCokernelProjection827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    LambdaRootsContinuousH1 K →ₗ[ZMod 59]
      W1LambdaCokernel827 (K := K) omega chi :=
  (LinearMap.range
    (lambdaOnFullOrbitKernel827 (K := K) omega chi)).mkQ

/-- The common quotient coset occupied by the lambda localization of a
normalized W3 point. -/
def normalizedW3LambdaCoset827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    W1LambdaCokernel827 (K := K) omega chi :=
  w1LambdaCokernelProjection827 (K := K) omega chi
    (lambdaReflectedLocalization827 (K := K) omega chi y₀.1)

/-- W1's prescribed reflected lambda class, retained in the same cokernel. -/
def prescribedW1LambdaCoset827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    W1LambdaCokernel827 (K := K) omega chi :=
  w1LambdaCokernelProjection827 (K := K) omega chi
    (twistedLambdaCupReceipt59 K).reflected

/-- The exact W2 obstruction class.  It is initially written relative to a
normalized W3 point, and proved independent of that point below. -/
def w1LambdaObstructionClass827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    W1LambdaCokernel827 (K := K) omega chi :=
  w1LambdaCokernelProjection827 (K := K) omega chi
    (w1LambdaCorrection827 (K := K) omega chi y₀)

/-- The obstruction is the difference between W1's prescribed quotient
class and W3's realized quotient coset. -/
theorem w1LambdaObstructionClass827_eq_prescribed_sub_normalized
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    w1LambdaObstructionClass827 (K := K) omega chi y₀ =
      prescribedW1LambdaCoset827 (K := K) omega chi -
        normalizedW3LambdaCoset827 (K := K) omega chi y₀ := by
  simp [w1LambdaObstructionClass827, prescribedW1LambdaCoset827,
    normalizedW3LambdaCoset827, w1LambdaCorrection827,
    w1LambdaCokernelProjection827]

/-- Any two normalized W3 lambda localizations differ by the restricted
lambda image of their actual full-orbit-kernel difference. -/
theorem normalizedW3LambdaDifference_mem_restrictedRange827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    lambdaReflectedLocalization827 (K := K) omega chi y₀.1 -
        lambdaReflectedLocalization827 (K := K) omega chi y₁.1 ∈
      LinearMap.range
        (lambdaOnFullOrbitKernel827 (K := K) omega chi) := by
  refine ⟨normalizedW3Difference827 (K := K) omega chi y₀ y₁, ?_⟩
  change
    lambdaReflectedLocalization827 (K := K) omega chi
        (y₀.1 - y₁.1) =
      lambdaReflectedLocalization827 (K := K) omega chi y₀.1 -
        lambdaReflectedLocalization827 (K := K) omega chi y₁.1
  exact map_sub _ _ _

/-- The normalized W3 quotient coset is independent of its basepoint. -/
theorem normalizedW3LambdaCoset827_eq
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    normalizedW3LambdaCoset827 (K := K) omega chi y₀ =
      normalizedW3LambdaCoset827 (K := K) omega chi y₁ := by
  change
    Submodule.Quotient.mk
        (lambdaReflectedLocalization827 (K := K) omega chi y₀.1) =
      Submodule.Quotient.mk
        (lambdaReflectedLocalization827 (K := K) omega chi y₁.1)
  apply (Submodule.Quotient.eq
    (LinearMap.range
      (lambdaOnFullOrbitKernel827 (K := K) omega chi))).mpr
  exact normalizedW3LambdaDifference_mem_restrictedRange827
    omega chi y₀ y₁

/-- Consequently, the literal W2 obstruction class is independent of the
chosen normalized W3 basepoint. -/
theorem w1LambdaObstructionClass827_eq
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    w1LambdaObstructionClass827 (K := K) omega chi y₀ =
      w1LambdaObstructionClass827 (K := K) omega chi y₁ := by
  rw [w1LambdaObstructionClass827_eq_prescribed_sub_normalized,
    w1LambdaObstructionClass827_eq_prescribed_sub_normalized,
    normalizedW3LambdaCoset827_eq omega chi y₀ y₁]

/-- The cokernel obstruction vanishes exactly when the affine correction
lies in the restricted lambda range. -/
theorem w1LambdaObstructionClass827_eq_zero_iff_mem_range
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    w1LambdaObstructionClass827 (K := K) omega chi y₀ = 0 ↔
      w1LambdaCorrection827 (K := K) omega chi y₀ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K) omega chi) := by
  change
    (Submodule.Quotient.mk
      (w1LambdaCorrection827 (K := K) omega chi y₀) :
        W1LambdaCokernel827 (K := K) omega chi) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

/-- The correction-range condition itself is independent of the normalized
W3 basepoint, without assuming that it holds. -/
theorem w1LambdaCorrection827_mem_range_iff_basepoint
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    w1LambdaCorrection827 (K := K) omega chi y₀ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K) omega chi) ↔
      w1LambdaCorrection827 (K := K) omega chi y₁ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K) omega chi) := by
  rw [← w1LambdaObstructionClass827_eq_zero_iff_mem_range,
    ← w1LambdaObstructionClass827_eq_zero_iff_mem_range,
    w1LambdaObstructionClass827_eq omega chi y₀ y₁]

/-- Exact quotient formulation: W1's prescribed lambda class and W3's
normalized lambda image occupy the same coset precisely when the obstruction
vanishes. -/
theorem prescribedW1LambdaCoset827_eq_normalized_iff_obstruction_eq_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    prescribedW1LambdaCoset827 (K := K) omega chi =
        normalizedW3LambdaCoset827 (K := K) omega chi y₀ ↔
      w1LambdaObstructionClass827 (K := K) omega chi y₀ = 0 := by
  rw [w1LambdaObstructionClass827_eq_prescribed_sub_normalized]
  exact sub_eq_zero.symm

/-- The exact cokernel obstruction theorem.  This identifies the remaining
W2 lift problem but does not solve it. -/
theorem w1w3CompatibleFiber827_nonempty_iff_obstruction_eq_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      w1LambdaObstructionClass827 (K := K) omega chi y₀ = 0 := by
  rw [w1w3CompatibleFiber827_nonempty_iff_correction_mem_range]
  exact
    (w1LambdaObstructionClass827_eq_zero_iff_mem_range
      omega chi y₀).symm

/-- Equivalently, the W1+W3 fiber is inhabited exactly when the prescribed
W1 class equals the basepoint-independent normalized W3 coset. -/
theorem w1w3CompatibleFiber827_nonempty_iff_prescribed_eq_normalizedCoset
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      prescribedW1LambdaCoset827 (K := K) omega chi =
        normalizedW3LambdaCoset827 (K := K) omega chi y₀ := by
  rw [w1w3CompatibleFiber827_nonempty_iff_obstruction_eq_zero]
  exact
    (prescribedW1LambdaCoset827_eq_normalized_iff_obstruction_eq_zero
      omega chi y₀).symm

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827.normalizedW3LambdaCoset827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizedW3LambdaCoset827_eq

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827.w1LambdaObstructionClass827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms w1LambdaObstructionClass827_eq

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827.w1w3CompatibleFiber827_nonempty_iff_obstruction_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms w1w3CompatibleFiber827_nonempty_iff_obstruction_eq_zero

end Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827
