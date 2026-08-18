/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The Fermat-state bridge to the 60-twisted lambda class at 59

For a primitive second-case state, the raw plus factor is exactly the
normalized plus factor times `zeta - 1`.  This file records that identity in
the global Kummer quotient and transports it to the actual lambda-adic
completion.  At the canonical root, the fixed denominator becomes the bare
lambda class.  Consequently

`localized normalized factor = [60]`

is equivalent to

`localized raw factor = [60 * lambda]`.

The final section also gives the literal localization readback for an old
primal state.  Its last theorem deliberately takes the remaining historical
identification with the normalized factor as an equality hypothesis.  Thus
the module locates that arithmetic seam without inventing it and without
importing the currently broken historical `Fermat.Cases` route.
-/
import Fermat.Conservation.LocalKummerTransport
import Fermat.FiftyNine.Conservation.ArtinHasseInventory
import Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59
import Fermat.FiftyNine.Conservation.VostokovShapeAudit59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59

open Fermat.Conservation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.ArtinHasseInventory
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.VostokovLocalization59
open Fermat.FiftyNine.Conservation.VostokovShapeAudit59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable {K : Type} [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]
variable {zeta : K}

/-! ## The global factor identity -/

/-- The raw plus factor, viewed as a nonzero element of the cyclotomic
field. -/
def rawPlusFieldUnit59
    (hZeta : IsPrimitiveRoot zeta 59)
    (S : PrimitiveSecondCaseSolution) : Kˣ :=
  Units.mk0
    (algebraMap (NumberField.RingOfIntegers K) K
      (Fermat.Conservation.KummerDrain.factorNode
        (S.x : NumberField.RingOfIntegers K)
        (S.y : NumberField.RingOfIntegers K) (plusNode hZeta)))
    ((FaithfulSMul.algebraMap_injective
      (NumberField.RingOfIntegers K) K).ne
        (stateFactor_ne_zero S (plusNode hZeta)))

/-- The normalized plus factor, viewed as a nonzero element of the
cyclotomic field. -/
def normalizedPlusFieldUnit59
    (hZeta : IsPrimitiveRoot zeta 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) : Kˣ :=
  Units.mk0
    (algebraMap (NumberField.RingOfIntegers K) K
      (normalizedPlusFactor hZeta S hz))
    ((FaithfulSMul.algebraMap_injective
      (NumberField.RingOfIntegers K) K).ne
        (normalizedPlusFactor_ne_zero hZeta S hz))

/-- The fixed denominator `zeta - 1`, viewed as a nonzero element of the
cyclotomic field. -/
def denominatorFieldUnit59
    (hZeta : IsPrimitiveRoot zeta 59) : Kˣ :=
  Units.mk0
    (algebraMap (NumberField.RingOfIntegers K) K
      (fixedDenominator hZeta))
    ((FaithfulSMul.algebraMap_injective
      (NumberField.RingOfIntegers K) K).ne
        (fixedDenominator_ne_zero hZeta))

/-- The global Kummer class of the raw plus factor. -/
def rawPlusKummerClass59
    (hZeta : IsPrimitiveRoot zeta 59)
    (S : PrimitiveSecondCaseSolution) : KummerClass 59 K :=
  fieldKummerClass (rawPlusFieldUnit59 hZeta S)

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
private theorem fieldKummerClass_mul (a b : Kˣ) :
    fieldKummerClass (a * b) =
      fieldKummerClass a + fieldKummerClass b := by
  rfl

/-- The exact global Kummer-class readback of the normalization identity:
the raw plus factor is the normalized factor times `zeta - 1`. -/
theorem rawPlusKummerClass59_eq_normalizedPlus_add_denominator
    (hZeta : IsPrimitiveRoot zeta 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    rawPlusKummerClass59 hZeta S =
      normalizedPlusKummerClass hZeta S hz +
        fixedDenominatorKummerClass hZeta := by
  have hunit : rawPlusFieldUnit59 hZeta S =
      normalizedPlusFieldUnit59 hZeta S hz *
        denominatorFieldUnit59 hZeta := by
    apply Units.ext
    change algebraMap (NumberField.RingOfIntegers K) K
        (Fermat.Conservation.KummerDrain.factorNode
          (S.x : NumberField.RingOfIntegers K)
          (S.y : NumberField.RingOfIntegers K) (plusNode hZeta)) =
      algebraMap (NumberField.RingOfIntegers K) K
          (normalizedPlusFactor hZeta S hz) *
        algebraMap (NumberField.RingOfIntegers K) K (fixedDenominator hZeta)
    rw [← map_mul]
    exact congrArg (algebraMap (NumberField.RingOfIntegers K) K)
      (normalizedPlusFactor_spec hZeta S hz).symm
  rw [rawPlusKummerClass59, hunit, fieldKummerClass_mul]
  rfl

private abbrev canonicalZeta59
    (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] : K :=
  globalPrimitiveRoot59 K

private abbrev canonicalZeta59_isPrimitive
    (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] :
    IsPrimitiveRoot (canonicalZeta59 K) 59 :=
  globalPrimitiveRoot59_isPrimitive K

/-! ## Localization at the actual cyclotomic lambda place -/

/-- Under the canonical localization, the fixed global denominator class is
the concrete local lambda class. -/
theorem localize_fixedDenominatorKummerClass59 :
    LocalKummerTransport.map 59 (lambdaLocalization59 K)
        (fixedDenominatorKummerClass (canonicalZeta59_isPrimitive K)) =
      canonicalLambdaKummerClass59 K := by
  have hglobal :
      fixedDenominatorKummerClass (canonicalZeta59_isPrimitive K) =
        fieldKummerClass
          (denominatorFieldUnit59 (canonicalZeta59_isPrimitive K)) := rfl
  have hunit :
      LocalKummerTransport.unitMap (lambdaLocalization59 K)
          (denominatorFieldUnit59 (canonicalZeta59_isPrimitive K)) =
        canonicalLambda59Unit K := by
    apply Units.ext
    change lambdaLocalization59 K
        (algebraMap (NumberField.RingOfIntegers K) K
          ((canonicalZeta59_isPrimitive K).toInteger - 1)) =
      canonicalLambda59 K
    rw [map_sub, map_one]
    rw [show algebraMap (NumberField.RingOfIntegers K) K
        (canonicalZeta59_isPrimitive K).toInteger = canonicalZeta59 K from rfl]
    simp [canonicalLambda59, lambdaLocalPrimitiveRoot59,
      localPrimitiveRoot59, lambdaLocalization59, localization59,
      canonicalZeta59]
  rw [hglobal]
  change LocalKummerTransport.map 59 (lambdaLocalization59 K)
      (classOfUnit 59 K
        (Additive.ofMul
          (denominatorFieldUnit59 (canonicalZeta59_isPrimitive K)))) =
    classOfUnit 59 (LambdaField59 K)
      (Additive.ofMul (canonicalLambda59Unit K))
  rw [LocalKummerTransport.map_classOfUnit, hunit]

/-- The localized Kummer class of the raw plus factor. -/
def localizedRawPlusKummerClass59
    (S : PrimitiveSecondCaseSolution) :
    KummerClass 59 (LambdaField59 K) :=
  LocalKummerTransport.map 59 (lambdaLocalization59 K)
    (rawPlusKummerClass59 (canonicalZeta59_isPrimitive K) S)

/-- The localized Kummer class of the normalized plus factor. -/
def localizedNormalizedPlusKummerClass59
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    KummerClass 59 (LambdaField59 K) :=
  LocalKummerTransport.map 59 (lambdaLocalization59 K)
    (normalizedPlusKummerClass (canonicalZeta59_isPrimitive K) S hz)

/-- Localized normalization readback: the raw factor differs from the
normalized factor by exactly the concrete lambda class. -/
theorem localizedRawPlusKummerClass59_eq_normalizedPlus_add_lambda
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    localizedRawPlusKummerClass59 S =
      localizedNormalizedPlusKummerClass59 S hz +
        canonicalLambdaKummerClass59 K := by
  rw [localizedRawPlusKummerClass59,
    rawPlusKummerClass59_eq_normalizedPlus_add_denominator,
    map_add, localizedNormalizedPlusKummerClass59,
    localize_fixedDenominatorKummerClass59]

/-- The local unit-60 target and the local 60-twisted-lambda target are the
same missing equality before and after restoring the normalization
denominator. -/
theorem localizedNormalizedPlus_eq_twistUnit_iff_rawPlus_eq_twistedLambda
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    localizedNormalizedPlusKummerClass59 S hz =
        twistUnitKummerClass59 K ↔
      localizedRawPlusKummerClass59 S =
        twistedLambdaRadicandKummerClass59 K := by
  rw [localizedRawPlusKummerClass59_eq_normalizedPlus_add_lambda,
    twistedLambdaRadicandKummerClass59_eq_add]
  constructor
  · exact congrArg (fun x ↦ x + canonicalLambdaKummerClass59 K)
  · intro h
    calc
      localizedNormalizedPlusKummerClass59 S hz =
          localizedNormalizedPlusKummerClass59 S hz +
            canonicalLambdaKummerClass59 K +
              -canonicalLambdaKummerClass59 K :=
        (add_neg_cancel_right
          (localizedNormalizedPlusKummerClass59 S hz)
          (canonicalLambdaKummerClass59 K)).symm
      _ = twistUnitKummerClass59 K + canonicalLambdaKummerClass59 K +
            -canonicalLambdaKummerClass59 K :=
        congrArg (fun x ↦ x + -canonicalLambdaKummerClass59 K) h
      _ = twistUnitKummerClass59 K :=
        add_neg_cancel_right (twistUnitKummerClass59 K)
          (canonicalLambdaKummerClass59 K)

/-! ## The literal old-primal state boundary -/

section Statewise

variable
  (rho : Fermat.Conservation.SelmerEigenspace.SelmerDeltaRepresentation
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
    (Delta := GaloisIndex59))
  (chi : Fermat.Conservation.InvolutiveBase.Character
    (PadicInt 59) GaloisIndex59)

/-- Localization of the exact old-primal Kummer class used by the Vostokov
statewise input. -/
def localizedStatewiseKummerClass59
    (x : OldPrimal59 rho chi) : KummerClass 59 (LambdaField59 K) :=
  LocalKummerTransport.map 59 (lambdaLocalization59 K)
    (statewiseKummerClass rho chi x)

/-- The localized old-primal class is represented by the localization of
its literal chosen global representative. -/
theorem localizedStatewiseRepresentative_readback59
    (x : OldPrimal59 rho chi) :
    localizedStatewiseKummerClass59 rho chi x =
      classOfUnit 59 (LambdaField59 K)
        (Additive.ofMul
          (LocalKummerTransport.unitMap (lambdaLocalization59 K)
            (statewiseRepresentative rho chi x))) := by
  rw [localizedStatewiseKummerClass59,
    ← statewiseRepresentative_readback rho chi x]
  exact LocalKummerTransport.map_classOfUnit
    (p := 59) (lambdaLocalization59 K)
      (statewiseRepresentative rho chi x)

/-- Once the historical descent identifies its old-primal state with the
normalized plus factor, the desired statewise unit-60 equality is exactly
the raw 60-twisted-lambda equality.  The premise is intentionally exposed:
it is the first remaining historical arithmetic bridge. -/
theorem
    localizedStatewise_eq_twistUnit_iff_rawPlus_eq_twistedLambda_of_eq_normalized
    (x : OldPrimal59 rho chi)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (hstate : statewiseKummerClass rho chi x =
      normalizedPlusKummerClass (canonicalZeta59_isPrimitive K) S hz) :
    localizedStatewiseKummerClass59 rho chi x =
        twistUnitKummerClass59 K ↔
      localizedRawPlusKummerClass59 S =
        twistedLambdaRadicandKummerClass59 K := by
  rw [localizedStatewiseKummerClass59, hstate]
  exact localizedNormalizedPlus_eq_twistUnit_iff_rawPlus_eq_twistedLambda
    S hz

end Statewise

end Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59
