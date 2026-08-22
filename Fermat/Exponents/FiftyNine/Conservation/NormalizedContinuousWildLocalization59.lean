/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The normalized continuous wild localization at 59

This module composes the unconditional normalized continuous Kummer pairing
with its canonical restriction to the old seated carrier.  The resulting
object fills all three fields of `ReflectedWildKummerCoreAt59`: the total
pairing is the genuine continuous-cup pairing, the 827 landing is obtained
from the common cyclotomic action, and calibration is proved against the
interface obtained by restricting that same pairing.

The construction therefore reaches the complete q-relaxed localization
consumer with no arithmetic premise.  It does not identify this canonical
old-shaped interface with an independently supplied historical wild
interface; `oldWildInterfaceOfPairing_eq_iff_calibration` remains the exact
comparison theorem for that separate claim.
-/
import Fermat.Exponents.FiftyNine.Conservation.ContinuousOldWildAdapter59
import Fermat.Exponents.FiftyNine.Conservation.NormalizedContinuousKummerPairing59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.WildKummerPairing
open ContinuousKummerTateLocalization59
open ContinuousOldWildAdapter59
open CyclotomicSelmerAction59
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open SplitPrimeFourier827
open UlamReadout827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The canonical old-shaped wild interface obtained by restricting the
unconditionally normalized total Kummer pairing. -/
noncomputable def normalizedOldWildInterface59
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    OldWildInterface59 (cyclotomicStrictSelmerRepresentation59 K)
      omega chi (lambdaPlace59 K) :=
  continuousOldWildInterface59 (K := K)
    (normalizedInflationReadout59 K) omega chi

@[simp]
theorem normalizedOldWildInterface59_reading
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : OldReflectedDual59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi) :
    (normalizedOldWildInterface59 K omega chi).reading x y =
      normalizedLambdaGlobalPairing59 K
        (toKummerClass x) (toKummerClass y) :=
  rfl

/-- All three fields of the reflected wild Kummer core, instantiated by the
unconditional normalized continuous pairing. -/
noncomputable def normalizedReflectedWildKummerCore59
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K)
      (normalizedOldWildInterface59 K omega chi) :=
  continuousReflectedWildKummerCoreAt59 (K := K)
    (normalizedInflationReadout59 K) omega chi

@[simp]
theorem normalizedReflectedWildKummerCore59_pairing
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    (normalizedReflectedWildKummerCore59 K omega chi).pairing =
      normalizedLambdaGlobalPairing59 K :=
  rfl

/-- The core calibration is an exposed theorem on the literal old carriers.
The total pairing is not defined from the old reading. -/
theorem normalizedReflectedWildKummerCore59_calibration
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : OldReflectedDual59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi) :
    (normalizedReflectedWildKummerCore59 K omega chi).pairing
        (toKummerClass x) (toKummerClass y) =
      (normalizedOldWildInterface59 K omega chi).reading x y :=
  rfl

/-- The retained pairing in the core still has the proved unit-60
normalization; passing through the carrier adapter loses no arithmetic
information. -/
theorem normalizedReflectedWildKummerCore59_unit60_primitive
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    (normalizedReflectedWildKummerCore59 K omega chi).pairing
        (classOfUnit 59 K
          (Additive.ofMul (globalUnit60RadicandUnit59 K)))
        (classOfUnit 59 K
          (Additive.ofMul (Fermat.Conservation.KummerOrientation.primitiveUnit
            59 K (globalPrimitiveRoot59 K)
            (globalPrimitiveRoot59_isPrimitive K)))) = 1 := by
  exact normalizedLambdaGlobalPairing59_unit60_primitive K

/-- The completed q-relaxed localization obtained by firing the Vostokov
core constructor on the normalized continuous core. -/
noncomputable def normalizedReflectedWildLocalization59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    UlamReadout827.ReflectedWildLocalizationAt59
      (Place := IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))
      (SelmerChi := OldPrimal59
        (cyclotomicStrictSelmerRepresentation59 K) chi)
      (DOmegaSelmerChiStar := OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K)
      (normalizedOldWildInterface59 K omega chi) :=
  continuousReflectedWildLocalizationAt59 (K := K)
    (normalizedInflationReadout59 K) omega chi

/-- Readback of the q-relaxed pairing on the canonical strict inclusion.
This is the completed localization's calibration theorem, not a postulated
comparison value. -/
theorem normalizedReflectedWildLocalization59_agrees_with_old
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : OldReflectedDual59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi) :
    (normalizedReflectedWildLocalization59 K omega chi).readingAt59 x
        ((normalizedReflectedWildLocalization59 K omega chi).oldToQRelaxed y) =
      (normalizedOldWildInterface59 K omega chi).reading x y :=
  (normalizedReflectedWildLocalization59 K omega chi).agrees_with_old x y

end Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59
