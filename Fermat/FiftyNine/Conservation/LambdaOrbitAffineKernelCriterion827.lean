/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The affine kernel criterion for the W1+W3 localization fiber

Fixing any point of W3's normalized full-orbit fiber turns the remaining W2
lifting problem into an exact linear equation.  A compatible W1+W3 point
exists precisely when the missing lambda-local class lies in the image of
lambda localization restricted to adjustments whose complete `827` orbit
valuation is zero.

This is pure linear algebra on the actual reflected q-relaxed Selmer carrier.
It neither supplies a Poitou--Tate lift nor asserts that the relevant range
contains the required correction.
-/
import Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.LambdaOrbitAffineKernelCriterion827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open ArbitraryUnitRawTameCarrierBridge827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LambdaOrbitLocalizationFiber827
open NormalizedFullOrbitGlobalRealization827
open PointedTateIncidence
open SplitPrimeFourier827
open TwistedLambdaCupReceipt59
open UlamReadout827
open WildOrbitBoundaryComparison827

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

/-- Lambda localization alone, viewed as a `ZMod 59` linear map on the
actual reflected q-relaxed Selmer carrier. -/
noncomputable def lambdaReflectedLocalizationLinear827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →ₗ[ZMod 59]
      LambdaRootsContinuousH1 K :=
  (lambdaReflectedLocalization827 (K := K) omega chi).toZModLinearMap 59

@[simp]
theorem lambdaReflectedLocalizationLinear827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    lambdaReflectedLocalizationLinear827 (K := K) omega chi y =
      lambdaReflectedLocalization827 (K := K) omega chi y :=
  rfl

/-- The complete `827` orbit valuation, viewed as a linear map. -/
noncomputable def fullOrbitValuationLocalizationLinear827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →ₗ[ZMod 59]
      (GaloisIndex59 → ZMod 59) :=
  (fullOrbitValuationLocalization827 (K := K) omega chi).toZModLinearMap 59

@[simp]
theorem fullOrbitValuationLocalizationLinear827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    fullOrbitValuationLocalizationLinear827 (K := K) omega chi y =
      fullOrbitValuationLocalization827 (K := K) omega chi y :=
  rfl

/-- Adjustments invisible at every one of the 58 supported places above
`827`. -/
abbrev FullOrbitValuationKernel827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :=
  LinearMap.ker
    (fullOrbitValuationLocalizationLinear827 (K := K) omega chi)

/-- Lambda localization restricted to adjustments that leave W3's complete
normalized orbit profile unchanged. -/
noncomputable def lambdaOnFullOrbitKernel827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    FullOrbitValuationKernel827 (K := K) omega chi →ₗ[ZMod 59]
      LambdaRootsContinuousH1 K :=
  (lambdaReflectedLocalizationLinear827 (K := K) omega chi).comp
    (FullOrbitValuationKernel827 (K := K) omega chi).subtype

@[simp]
theorem lambdaOnFullOrbitKernel827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (z : FullOrbitValuationKernel827 (K := K) omega chi) :
    lambdaOnFullOrbitKernel827 (K := K) omega chi z =
      lambdaReflectedLocalization827 (K := K) omega chi z.1 :=
  rfl

/-- Relative to a fixed W3 point, this is exactly the lambda-local class
which an orbit-invisible adjustment must contribute. -/
noncomputable def w1LambdaCorrection827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    LambdaRootsContinuousH1 K :=
  (twistedLambdaCupReceipt59 K).reflected -
    lambdaReflectedLocalization827 (K := K) omega chi y₀.1

/-- A zero complete-orbit localization is literally the vanishing of all
58 genuine orbit coordinates. -/
theorem fullOrbitValuationLocalization827_eq_zero_iff
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (z : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    fullOrbitValuationLocalization827 (K := K) omega chi z = 0 ↔
      ∀ tau : GaloisIndex59, relaxedOrbitValuation827 K tau z.1 = 0 := by
  constructor
  · intro h tau
    exact congrFun h tau
  · intro h
    funext tau
    exact h tau

/-- Subtracting a fixed normalized W3 point from a compatible point gives
an orbit-invisible correction with exactly the missing lambda localization;
adding any such correction reconstructs a compatible point. -/
theorem w1w3CompatibleFiber827_nonempty_iff_exists_orbitKernelCorrection
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      ∃ z : QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi,
        fullOrbitValuationLocalization827 (K := K) omega chi z = 0 ∧
        lambdaReflectedLocalization827 (K := K) omega chi z =
          w1LambdaCorrection827 (K := K) omega chi y₀ := by
  constructor
  · rintro ⟨y⟩
    refine ⟨y.1 - y₀.1, ?_, ?_⟩
    · rw [map_sub]
      have hy :
          fullOrbitValuationLocalization827 (K := K) omega chi y.1 =
            normalizedFullOrbitEigenprofileCoordinates827 omega chi :=
        w1w3CompatibleFiber827_fullOrbit omega chi y
      have hy₀ :
          fullOrbitValuationLocalization827 (K := K) omega chi y₀.1 =
            normalizedFullOrbitEigenprofileCoordinates827 omega chi := by
        funext tau
        exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
          omega chi y₀ tau
      rw [hy, hy₀, sub_self]
    · rw [map_sub]
      change
        lambdaReflectedLocalization827 (K := K) omega chi y.1 -
            lambdaReflectedLocalization827 (K := K) omega chi y₀.1 =
          w1LambdaCorrection827 (K := K) omega chi y₀
      rw [lambdaReflectedLocalization827_apply,
        w1w3CompatibleFiber827_lambda omega chi y]
      rfl
  · rintro ⟨z, horbit, hlambda⟩
    refine ⟨⟨y₀.1 + z, ?_⟩⟩
    apply Prod.ext
    · change
        lambdaReflectedLocalization827 (K := K) omega chi (y₀.1 + z) =
          (twistedLambdaCupReceipt59 K).reflected
      rw [map_add, hlambda]
      simp [w1LambdaCorrection827]
    · change
        fullOrbitValuationLocalization827 (K := K) omega chi (y₀.1 + z) =
          normalizedFullOrbitEigenprofileCoordinates827 omega chi
      rw [map_add, horbit, add_zero]
      funext tau
      exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
        omega chi y₀ tau

/-- The same affine criterion with the kernel condition exposed coordinate
by coordinate. -/
theorem w1w3CompatibleFiber827_nonempty_iff_exists_zeroOrbitCorrection
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      ∃ z : QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi,
        (∀ tau : GaloisIndex59,
          relaxedOrbitValuation827 K tau z.1 = 0) ∧
        lambdaReflectedLocalization827 (K := K) omega chi z =
          w1LambdaCorrection827 (K := K) omega chi y₀ := by
  rw [w1w3CompatibleFiber827_nonempty_iff_exists_orbitKernelCorrection]
  constructor
  · rintro ⟨z, horbit, hlambda⟩
    exact ⟨z,
      (fullOrbitValuationLocalization827_eq_zero_iff omega chi z).mp horbit,
      hlambda⟩
  · rintro ⟨z, horbit, hlambda⟩
    exact ⟨z,
      (fullOrbitValuationLocalization827_eq_zero_iff omega chi z).mpr horbit,
      hlambda⟩

/-- Membership in the restricted lambda range is the explicit existence of
an actual orbit-invisible reflected q-relaxed adjustment. -/
theorem w1LambdaCorrection827_mem_range_iff_exists_orbitKernelCorrection
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    w1LambdaCorrection827 (K := K) omega chi y₀ ∈
        LinearMap.range (lambdaOnFullOrbitKernel827 (K := K) omega chi) ↔
      ∃ z : QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi,
        fullOrbitValuationLocalization827 (K := K) omega chi z = 0 ∧
        lambdaReflectedLocalization827 (K := K) omega chi z =
          w1LambdaCorrection827 (K := K) omega chi y₀ := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.1, ?_, ?_⟩
    · exact z.2
    · exact hz
  · rintro ⟨z, horbit, hlambda⟩
    refine ⟨⟨z, ?_⟩, ?_⟩
    · exact horbit
    · exact hlambda

/-- The sharp affine range criterion: after choosing any existing W3 point,
the W1+W3 fiber is inhabited exactly when the missing W1 lambda class lies
in the range of lambda localization restricted to the full orbit kernel. -/
theorem w1w3CompatibleFiber827_nonempty_iff_correction_mem_range
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      w1LambdaCorrection827 (K := K) omega chi y₀ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K) omega chi) := by
  rw [w1w3CompatibleFiber827_nonempty_iff_exists_orbitKernelCorrection]
  exact
    (w1LambdaCorrection827_mem_range_iff_exists_orbitKernelCorrection
      omega chi y₀).symm

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitAffineKernelCriterion827.w1w3CompatibleFiber827_nonempty_iff_exists_orbitKernelCorrection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  w1w3CompatibleFiber827_nonempty_iff_exists_orbitKernelCorrection

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitAffineKernelCriterion827.w1w3CompatibleFiber827_nonempty_iff_correction_mem_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  w1w3CompatibleFiber827_nonempty_iff_correction_mem_range

end Fermat.FiftyNine.Conservation.LambdaOrbitAffineKernelCriterion827
