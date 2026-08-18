/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The concrete lambda-plus-827 localization fiber

This module puts the reflected lambda-local Kummer class and every genuine
supported valuation above `827` into one literal product carrier.  The
source is the actual reflected-character eigenspace inside Mathlib's
`827`-relaxed Selmer group; neither coordinate is supplied data.

The W1+W3 compatible fiber is the inverse image of the pair consisting of
W1's retained reflected `H^1` class and W3's normalized 58-row orbit
profile.  No inhabitant, Poitou--Tate theorem, reciprocity law, or
nonvanishing statement is asserted here.  Consequently, nonemptiness of
this fiber is the exact remaining global lifting question rather than a
certificate hidden in the definition.
-/
import Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.SelmerEigenspace
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalFullOrbitLocalPairing827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open NormalizedFullOrbitEigenprofile827
open NormalizedFullOrbitGlobalRealization827
open PointedTateIncidence
open SplitPrimeFourier827
open StrictTameOrbitClassFactorization827
open TwistedLambdaCupReceipt59
open UlamReadout827
open VostokovLocalization59
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

/-- The explicit local target: one roots-valued lambda `H¹` class together
with all 58 actual `827` supported-valuation coordinates. -/
abbrev LambdaOrbitLocalizationTarget827 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] :=
  LambdaRootsContinuousH1 K × (GaloisIndex59 → ZMod 59)

/-- Lambda localization of an actual reflected q-relaxed Selmer class,
retaining the roots-valued right Kummer seat required by W1. -/
noncomputable def lambdaReflectedLocalization827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →+
      LambdaRootsContinuousH1 K :=
  (rightKummerMap 59 (LambdaLocalField59 K)).comp
    ((LocalKummerTransport.map 59 (lambdaLocalization59 K)).comp
      toKummerClassAt)

@[simp]
theorem lambdaReflectedLocalization827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    lambdaReflectedLocalization827 (K := K) omega chi y =
      lambdaReflectedFactorOfGlobalKummer59 (K := K)
        (toKummerClassAt y) :=
  rfl

/-- All genuine `827` supported valuations, retained as one additive map.
The function coordinate is indexed by the actual 58-element Galois orbit. -/
def fullOrbitValuationLocalization827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →+
      (GaloisIndex59 → ZMod 59) where
  toFun y tau := relaxedOrbitValuation827 K tau y.1
  map_zero' := by
    funext tau
    exact (relaxedOrbitValuation827 K tau).map_zero
  map_add' y z := by
    funext tau
    exact (relaxedOrbitValuation827 K tau).map_add y.1 z.1

@[simp]
theorem fullOrbitValuationLocalization827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (tau : GaloisIndex59) :
    fullOrbitValuationLocalization827 (K := K) omega chi y tau =
      relaxedOrbitValuation827 K tau y.1 :=
  rfl

/-- The actual lambda-plus-827 localization map.  It is additive before
any fiber or target value is mentioned. -/
noncomputable def lambdaOrbitLocalization827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →+
      LambdaOrbitLocalizationTarget827 K :=
  (lambdaReflectedLocalization827 (K := K) omega chi).prod
    (fullOrbitValuationLocalization827 (K := K) omega chi)

@[simp]
theorem lambdaOrbitLocalization827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    lambdaOrbitLocalization827 (K := K) omega chi y =
      (lambdaReflectedFactorOfGlobalKummer59 (K := K) (toKummerClassAt y),
        fun tau ↦ relaxedOrbitValuation827 K tau y.1) :=
  rfl

/-- The same localization as a genuine `ZMod 59` linear map. -/
noncomputable def lambdaOrbitLocalizationLinear827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi →ₗ[ZMod 59]
      LambdaOrbitLocalizationTarget827 K :=
  (lambdaOrbitLocalization827 (K := K) omega chi).toZModLinearMap 59

@[simp]
theorem lambdaOrbitLocalizationLinear827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    lambdaOrbitLocalizationLinear827 (K := K) omega chi y =
      (lambdaReflectedFactorOfGlobalKummer59 (K := K) (toKummerClassAt y),
        fun tau ↦ relaxedOrbitValuation827 K tau y.1) :=
  rfl

/-- The exact prescribed W1+W3 local state. -/
noncomputable def w1w3LocalizationTarget827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    LambdaOrbitLocalizationTarget827 K :=
  ((twistedLambdaCupReceipt59 K).reflected,
    normalizedFullOrbitEigenprofileCoordinates827 omega chi)

/-- The actual reflected q-relaxed classes whose lambda localization is
W1's retained factor and whose complete `827` valuation vector is W3's
normalized profile.  This is a fiber, not an existence assertion. -/
def W1W3CompatibleFiber827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :=
  {y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi //
    lambdaOrbitLocalizationLinear827 (K := K) omega chi y =
      w1w3LocalizationTarget827 (K := K) omega chi}

/-- Every point of the combined fiber has exactly W1's reflected lambda
factor. -/
theorem w1w3CompatibleFiber827_lambda
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : W1W3CompatibleFiber827 (K := K) omega chi) :
    lambdaReflectedFactorOfGlobalKummer59 (K := K)
        (toKummerClassAt y.1) =
      (twistedLambdaCupReceipt59 K).reflected := by
  have h := congrArg Prod.fst y.2
  simpa [w1w3LocalizationTarget827] using h

/-- Every point of the combined fiber has exactly W3's complete normalized
58-row supported-valuation profile. -/
theorem w1w3CompatibleFiber827_fullOrbit
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : W1W3CompatibleFiber827 (K := K) omega chi) :
    (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y.1.1) =
      normalizedFullOrbitEigenprofileCoordinates827 omega chi := by
  have h := congrArg Prod.snd y.2
  simpa [w1w3LocalizationTarget827] using h

theorem w1w3CompatibleFiber827_orbitCoordinate
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : W1W3CompatibleFiber827 (K := K) omega chi)
    (tau : GaloisIndex59) :
    relaxedOrbitValuation827 K tau y.1.1 =
      normalizedFullOrbitEigenprofileCoordinates827 omega chi tau := by
  exact congrFun
    (w1w3CompatibleFiber827_fullOrbit omega chi y) tau

/-- Forgetting the lambda requirement sends the combined fiber into W3's
existing normalized reflected fiber.  The base coordinate is obtained from
the actual orbit coordinate at `1`, not from an extra normalization field. -/
noncomputable def w1w3CompatibleFiber827_toNormalizedReflectedFiber827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : W1W3CompatibleFiber827 (K := K) omega chi) :
    NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K)) := by
  refine ⟨y.1, ?_⟩
  rw [reflectedBoundaryFunctional827_apply]
  change supportValuationAt (tameOrbitBasePlace827 (K := K)) y.1.1 = 1
  have hplace :
      orbitSupportPlace827 K (1 : GaloisIndex59) =
        tameOrbitBasePlace827 (K := K) := by
    apply Subtype.ext
    exact tameOrbitPlace827_one K
  rw [← hplace]
  change relaxedOrbitValuation827 K (1 : GaloisIndex59) y.1.1 = 1
  rw [w1w3CompatibleFiber827_orbitCoordinate omega chi y]
  simp [normalizedFullOrbitEigenprofileCoordinates827,
    inverseReflectedResidueCharacter827]

/-- Conversely, a point of W3's retained normalized fiber whose actual
lambda localization is W1's retained class is a point of the combined
fiber.  W3's existing orbit theorem supplies every one of the 58 rows. -/
noncomputable def w1w3CompatibleFiber827_of_normalizedReflectedFiber827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K)))
    (hlambda :
      lambdaReflectedFactorOfGlobalKummer59 (K := K)
          (toKummerClassAt y.1) =
        (twistedLambdaCupReceipt59 K).reflected) :
    W1W3CompatibleFiber827 (K := K) omega chi := by
  refine ⟨y.1, ?_⟩
  apply Prod.ext
  · change lambdaReflectedFactorOfGlobalKummer59 (K := K)
        (toKummerClassAt y.1) =
      (twistedLambdaCupReceipt59 K).reflected
    exact hlambda
  · change (fun tau : GaloisIndex59 ↦
        relaxedOrbitValuation827 K tau y.1.1) =
      normalizedFullOrbitEigenprofileCoordinates827 omega chi
    funext tau
    exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
      omega chi y tau

/-- A combined-fiber point feeds the wild side of the common Hom-space as
the literal W1 cup functional, on every actual seated primal Selmer test. -/
theorem w1w3CompatibleFiber827_wildBoundary_eq_receiptCup
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : W1W3CompatibleFiber827 (K := K) omega chi)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    seatedWildBoundaryFunctional59 (K := K) omega chi y.1 x =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x))
          (twistedLambdaCupReceipt59 K).reflected) := by
  exact seatedWildBoundaryFunctional59_eq_receipt_cup_of_localizes
    omega chi y.1 (w1w3CompatibleFiber827_lambda omega chi y) x

/-- The same combined-fiber point feeds the orbit side of the common
Hom-space as the genuine strict-Selmer full-orbit functional. -/
theorem w1w3CompatibleFiber827_orbitBoundary_eq_strict
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : W1W3CompatibleFiber827 (K := K) omega chi)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    seatedOrbitBoundaryFunctional827 (K := K) omega chi y.1 x =
      strictTameOrbitFunctional827 K y.1.1 x.1 :=
  seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827
    omega chi y.1 x

/-- Nonemptiness of the concrete fiber is exactly simultaneous existence
of one actual reflected q-relaxed class with the prescribed W1 lambda
factor and every prescribed W3 orbit coordinate. -/
theorem w1w3CompatibleFiber827_nonempty_iff
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      ∃ y : QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi,
        lambdaReflectedFactorOfGlobalKummer59 (K := K)
            (toKummerClassAt y) =
          (twistedLambdaCupReceipt59 K).reflected ∧
        ∀ tau : GaloisIndex59,
          relaxedOrbitValuation827 K tau y.1 =
            normalizedFullOrbitEigenprofileCoordinates827 omega chi tau := by
  constructor
  · rintro ⟨y⟩
    exact ⟨y.1, w1w3CompatibleFiber827_lambda omega chi y,
      w1w3CompatibleFiber827_orbitCoordinate omega chi y⟩
  · rintro ⟨y, hlambda, horbit⟩
    refine ⟨⟨y, ?_⟩⟩
    apply Prod.ext
    · simpa [w1w3LocalizationTarget827] using hlambda
    · funext tau
      simpa [w1w3LocalizationTarget827] using horbit tau

/-- Using W3's already-proved orbit propagation, the remaining existence
question is even more sharply the intersection of its retained normalized
fiber with one literal lambda-localization fiber. -/
theorem w1w3CompatibleFiber827_nonempty_iff_exists_normalized_lambda
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    Nonempty (W1W3CompatibleFiber827 (K := K) omega chi) ↔
      ∃ y : NormalizedReflectedFiber827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          (tameOrbitBasePlace827 (K := K)),
        lambdaReflectedFactorOfGlobalKummer59 (K := K)
            (toKummerClassAt y.1) =
          (twistedLambdaCupReceipt59 K).reflected := by
  constructor
  · rintro ⟨y⟩
    exact
      ⟨w1w3CompatibleFiber827_toNormalizedReflectedFiber827 omega chi y,
        w1w3CompatibleFiber827_lambda omega chi y⟩
  · rintro ⟨y, hlambda⟩
    exact ⟨w1w3CompatibleFiber827_of_normalizedReflectedFiber827
      omega chi y hlambda⟩

end Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827
