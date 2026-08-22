/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Fermat-factor sources in the strict 59-Selmer group

The circular-unit source is useful for the tame ledger, but it is real and
therefore dies in the odd irregular character seat.  The source appropriate
to that seat must retain the hypothetical Fermat solution itself.

For each normalized factor selected by `StateLinkedIdealPair`, its principal
ideal is literally the 59th power of the allocated ideal.  The generic
`IdealPowerSelmer` bridge therefore puts the factor's field-unit Kummer class
in Mathlib's empty-support Selmer group.  Only after this arithmetic
construction do we apply the canonical character idempotent.

No nonvanishing assertion is made here: the purpose of this file is to
construct the genuine solution-dependent seated inputs and expose exact
readbacks for the next reciprocity step.
-/
import Fermat.Experiments.Conservation.IdealPowerSelmer
import Fermat.Experiments.Conservation.PrimeCyclotomicSelmerClassNaturality
import Fermat.Exponents.FiftyNine.Conservation.CanonicalIrregularMode827
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.Exponents.FiftyNine.Conservation.StateFactorPair
import Fermat.Exponents.FiftyNine.Conservation.VostokovLocalization59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59

open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-! ## The two literal strict-Selmer sources -/

/-- The normalized plus factor, inserted into Mathlib's empty-support
59-Selmer group using its allocated ideal root. -/
noncomputable def fermatPlusStrictSelmer59
    (pair : StateLinkedIdealPair hζ S hz) :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 :=
  Additive.ofMul <|
    emptySelmerClassOfIdealPower
      (normalizedPlusFactor hζ S hz)
      (normalizedPlusFactor_ne_zero hζ S hz)
      pair.plusIdeal pair.plus_pow

/-- The normalized minus factor, inserted into Mathlib's empty-support
59-Selmer group using its allocated ideal root. -/
noncomputable def fermatMinusStrictSelmer59
    (pair : StateLinkedIdealPair hζ S hz) :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 :=
  Additive.ofMul <|
    emptySelmerClassOfIdealPower
      (normalizedMinusFactor hζ S hz)
      (normalizedMinusFactor_ne_zero hζ S hz)
      pair.minusIdeal pair.minus_pow

/-- Exact Kummer readback for the plus source. -/
theorem fermatPlusStrictSelmer59_kummerQuotient
    (pair : StateLinkedIdealPair hζ S hz) :
    (Additive.toMul (fermatPlusStrictSelmer59 pair)).1 =
      QuotientGroup.mk
        (integralFieldUnit
          (normalizedPlusFactor hζ S hz)
          (normalizedPlusFactor_ne_zero hζ S hz)) := by
  change
    (emptySelmerClassOfIdealPower
      (normalizedPlusFactor hζ S hz)
      (normalizedPlusFactor_ne_zero hζ S hz)
      pair.plusIdeal pair.plus_pow).1 = _
  exact
    emptySelmerClassOfIdealPower_val
      (q := normalizedPlusFactor hζ S hz)
      (hq := normalizedPlusFactor_ne_zero hζ S hz)
      (I := pair.plusIdeal) (hpow := pair.plus_pow)

/-- Exact Kummer readback for the minus source. -/
theorem fermatMinusStrictSelmer59_kummerQuotient
    (pair : StateLinkedIdealPair hζ S hz) :
    (Additive.toMul (fermatMinusStrictSelmer59 pair)).1 =
      QuotientGroup.mk
        (integralFieldUnit
          (normalizedMinusFactor hζ S hz)
          (normalizedMinusFactor_ne_zero hζ S hz)) := by
  change
    (emptySelmerClassOfIdealPower
      (normalizedMinusFactor hζ S hz)
      (normalizedMinusFactor_ne_zero hζ S hz)
      pair.minusIdeal pair.minus_pow).1 = _
  exact
    emptySelmerClassOfIdealPower_val
      (q := normalizedMinusFactor hζ S hz)
      (hq := normalizedMinusFactor_ne_zero hζ S hz)
      (I := pair.minusIdeal) (hpow := pair.minus_pow)

/-- Every height-one localization of the plus source is trivial, as required
by empty support. -/
theorem fermatPlusStrictSelmer59_localCondition
    (pair : StateLinkedIdealPair hζ S hz)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.valuationOfNeZeroMod 59
        (Additive.toMul (fermatPlusStrictSelmer59 pair)).1 = 1 :=
  (Additive.toMul (fermatPlusStrictSelmer59 pair)).2 v (by simp)

/-- Every height-one localization of the minus source is trivial, as
required by empty support. -/
theorem fermatMinusStrictSelmer59_localCondition
    (pair : StateLinkedIdealPair hζ S hz)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.valuationOfNeZeroMod 59
        (Additive.toMul (fermatMinusStrictSelmer59 pair)).1 = 1 :=
  (Additive.toMul (fermatMinusStrictSelmer59 pair)).2 v (by simp)

/-! ## Exact ideal-class receipts -/

/-- The class-group obstruction map on the literal strict Selmer carrier,
written additively so that its output lives in the same carrier as the
allocated factor ledger. -/
noncomputable abbrev strictSelmerIdealClass59 :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 →+
      Additive (ClassGroup (NumberField.RingOfIntegers K)) :=
  Fermat.Conservation.PrimeCyclotomicSelmerClassNaturality.strictSelmerIdealClass
    59 K

/-- The class obstruction of the genuine plus-factor Selmer source is
literally the class of the plus ideal allocated by the Fermat factorization. -/
theorem fermatPlusStrictSelmer59_idealClass
    (pair : StateLinkedIdealPair hζ S hz) :
    strictSelmerIdealClass59 (K := K) (fermatPlusStrictSelmer59 pair) =
      pair.ledger.rootClass 0 := by
  change Additive.ofMul
      (IsDedekindDomain.selmerGroup.toClass
        (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
        (emptySelmerClassOfIdealPower
          (normalizedPlusFactor hζ S hz)
          (normalizedPlusFactor_ne_zero hζ S hz)
          pair.plusIdeal pair.plus_pow)) = _
  rw [emptySelmerClassOfIdealPower_toClass]
  rfl

/-- The class obstruction of the genuine minus-factor Selmer source is
literally the class of the minus ideal allocated by the Fermat factorization. -/
theorem fermatMinusStrictSelmer59_idealClass
    (pair : StateLinkedIdealPair hζ S hz) :
    strictSelmerIdealClass59 (K := K) (fermatMinusStrictSelmer59 pair) =
      pair.ledger.rootClass 1 := by
  change Additive.ofMul
      (IsDedekindDomain.selmerGroup.toClass
        (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
        (emptySelmerClassOfIdealPower
          (normalizedMinusFactor hζ S hz)
          (normalizedMinusFactor_ne_zero hζ S hz)
          pair.minusIdeal pair.minus_pow)) = _
  rw [emptySelmerClassOfIdealPower_toClass]
  rfl

/-! ## The genuine odd-character sources -/

/-- Project the solution-dependent plus factor into the canonical odd
irregular character seat. -/
noncomputable def fermatPlusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
    irregularCharacter59 (fermatPlusStrictSelmer59 pair)

/-- Project the solution-dependent minus factor into the same canonical odd
irregular character seat. -/
noncomputable def fermatMinusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
    irregularCharacter59 (fermatMinusStrictSelmer59 pair)

/-- Carrier readback: the plus source is exactly the character idempotent
acting on the literal Fermat-factor Selmer class. -/
theorem fermatPlusPrimalMode59_toSeatedCarrier
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    toSeatedCarrier (fermatPlusPrimalMode59 pair) =
      (cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
        (characterIdempotent irregularCharacter59)
        (fermatPlusStrictSelmer59 pair) :=
  rfl

/-- Carrier readback for the minus-factor projection. -/
theorem fermatMinusPrimalMode59_toSeatedCarrier
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    toSeatedCarrier (fermatMinusPrimalMode59 pair) =
      (cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
        (characterIdempotent irregularCharacter59)
        (fermatMinusStrictSelmer59 pair) :=
  rfl

/-- Kummer-quotient readback after seating the plus source. -/
theorem fermatPlusPrimalMode59_toKummerQuotient
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    toKummerQuotient (fermatPlusPrimalMode59 pair) =
      (Additive.toMul
        ((cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
          (characterIdempotent irregularCharacter59)
          (fermatPlusStrictSelmer59 pair))).1 :=
  rfl

/-- Kummer-quotient readback after seating the minus source. -/
theorem fermatMinusPrimalMode59_toKummerQuotient
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    toKummerQuotient (fermatMinusPrimalMode59 pair) =
      (Additive.toMul
        ((cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
          (characterIdempotent irregularCharacter59)
          (fermatMinusStrictSelmer59 pair))).1 :=
  rfl

/-! ## Canonical statewise selections -/

/-- The plus source obtained from the canonical allocated ideal pair of a
Fermat state. -/
noncomputable def canonicalFermatPlusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (hζ : IsPrimitiveRoot ζ 59)
    (S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  fermatPlusPrimalMode59 (K := K) (hζ := hζ) (S := S) (hz := hz)
    (allocatedPair hζ S hz)

/-- The corresponding canonical minus-factor source. -/
noncomputable def canonicalFermatMinusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (hζ : IsPrimitiveRoot ζ 59)
    (S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  fermatMinusPrimalMode59 (K := K) (hζ := hζ) (S := S) (hz := hz)
    (allocatedPair hζ S hz)

end Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
