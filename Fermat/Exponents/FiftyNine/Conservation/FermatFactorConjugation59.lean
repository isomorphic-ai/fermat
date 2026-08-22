/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Conjugation of the two Fermat-factor Selmer sources

The normalized minus factor is not literally the conjugate of the plus
factor: the common denominator leaves the root-of-unity correction
`-zeta^-1`.  This file retains that correction through the field-unit,
Kummer-quotient, strict-Selmer, and odd-character-projector layers.

The cyclotomic action indexed by `-1` is identified with complex
conjugation.  In the odd `chi = 15` seat, the conjugated plus contribution
therefore becomes the negative of the projected plus class.  No vanishing
of the separately projected root-of-unity correction is assumed.
-/
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorSelmerSource59
import Fermat.Exponents.FiftyNine.Conservation.StateFactorConjugation
import KummerCriterion.CyclotomicUnits.KummerLogMatrix

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatFactorConjugation59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open DetectorWitness827
open FermatFactorSelmerSource59
open PrimalFourierNonvanishing827
open SplitPrimeFourier827
open StateFactorConjugation
open StateFactorPair
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

/-- The canonical irregular character is odd at the `-1` cyclotomic
automorphism. -/
theorem irregularCharacter59_negOne_reduction :
    PadicInt.toZMod
        (irregularCharacter59 (-1) : PadicInt 59) =
      (-1 : ZMod 59) := by
  have h := DFunLike.congr_fun
    reducedCharacter59_irregularCharacter59 (-1)
  have hval := congrArg Units.val h
  calc
    PadicInt.toZMod
        (irregularCharacter59 (-1) : PadicInt 59) =
        (-1 : ZMod 59) ^ (15 : ZMod 58).val := by
      simpa [reducedCharacter59, powerCharacter59] using hval
    _ = (-1 : ZMod 59) := by decide

/-! ## The correction class -/

/-- The integral root-of-unity correction left by the common normalization
denominator: `-zeta^-1`. -/
noncomputable def normalizationCorrectionRingUnit59
    (hζ : IsPrimitiveRoot ζ 59) : (NumberField.RingOfIntegers K)ˣ :=
  -((zetaUnit hζ)⁻¹)

/-- The same correction embedded as a nonzero field element. -/
noncomputable def normalizationCorrectionFieldUnit59
    (hζ : IsPrimitiveRoot ζ 59) : Kˣ :=
  Units.map (algebraMap (NumberField.RingOfIntegers K) K)
    (normalizationCorrectionRingUnit59 hζ)

/-- The correction's literal empty-support Selmer class, obtained through
Mathlib's unit-to-Selmer map. -/
noncomputable def normalizationCorrectionStrictSelmer59
    (hζ : IsPrimitiveRoot ζ 59) :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 :=
  Additive.ofMul <|
    IsDedekindDomain.selmerGroup.fromUnit
      (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
      (normalizationCorrectionRingUnit59 hζ)

omit [IsCyclotomicExtension {59} ℚ K] in
/-- Exact Kummer readback for the correction class. -/
@[simp]
theorem normalizationCorrectionStrictSelmer59_kummerQuotient
    (hζ : IsPrimitiveRoot ζ 59) :
    (Additive.toMul (normalizationCorrectionStrictSelmer59 hζ)).1 =
      QuotientGroup.mk (normalizationCorrectionFieldUnit59 hζ) :=
  rfl

/-! ## Raw conjugation -/

/-- Embedded in the fraction field, the normalized factor identity is the
correction multiplied by the genuine cyclotomic `-1` action on the plus
factor. -/
theorem integralFieldUnit_normalizedMinusFactor_eq_correction_mul_conj
    (hζ : IsPrimitiveRoot ζ 59)
    (S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z) :
    integralFieldUnit
        (normalizedMinusFactor hζ S hz)
        (normalizedMinusFactor_ne_zero hζ S hz) =
      normalizationCorrectionFieldUnit59 hζ *
        cyclotomicUnitEquiv59 K (-1)
          (integralFieldUnit
            (normalizedPlusFactor hζ S hz)
            (normalizedPlusFactor_ne_zero hζ S hz)) := by
  apply Units.ext
  change algebraMap (NumberField.RingOfIntegers K) K
      (normalizedMinusFactor hζ S hz) =
    algebraMap (NumberField.RingOfIntegers K) K
        (↑(normalizationCorrectionRingUnit59 hζ) :
          NumberField.RingOfIntegers K) *
      KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K (-1)
        (algebraMap (NumberField.RingOfIntegers K) K
          (normalizedPlusFactor hζ S hz))
  rw [KummerCriterion.cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal
    (p := 59) (K := K) (by norm_num)]
  have h := congrArg (algebraMap (NumberField.RingOfIntegers K) K)
    (normalizedMinusFactor_eq_unit_mul_conj hζ S hz)
  simpa [normalizationCorrectionRingUnit59, map_mul,
    KummerCriterion.cyclotomicComplexConjGal,
    NumberField.IsCMField.coe_ringOfIntegersComplexConj] using h

/-- Exact raw Kummer relation between the two strict Selmer sources. -/
theorem fermatMinusStrictSelmer59_kummerQuotient_eq_correction_mul_conj
    (pair : StateLinkedIdealPair hζ S hz) :
    (Additive.toMul (fermatMinusStrictSelmer59 pair)).1 =
      QuotientGroup.mk (normalizationCorrectionFieldUnit59 hζ) *
        cyclotomicKummerHom59 K (-1)
          (Additive.toMul (fermatPlusStrictSelmer59 pair)).1 := by
  rw [fermatMinusStrictSelmer59_kummerQuotient,
    fermatPlusStrictSelmer59_kummerQuotient]
  change QuotientGroup.mk'
      (powMonoidHom 59 : Kˣ →* Kˣ).range
        (integralFieldUnit
          (normalizedMinusFactor hζ S hz)
          (normalizedMinusFactor_ne_zero hζ S hz)) =
    QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (normalizationCorrectionFieldUnit59 hζ) *
      cyclotomicKummerHom59 K (-1)
        (QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (integralFieldUnit
            (normalizedPlusFactor hζ S hz)
            (normalizedPlusFactor_ne_zero hζ S hz)))
  rw [cyclotomicKummerHom59_mk]
  simpa only [map_mul] using congrArg
    (QuotientGroup.mk'
      (powMonoidHom 59 : Kˣ →* Kˣ).range)
    (integralFieldUnit_normalizedMinusFactor_eq_correction_mul_conj
      hζ S hz)

/-- The same identity in the actual additive strict Selmer carrier. -/
theorem fermatMinusStrictSelmer59_eq_correction_add_conj
    (pair : StateLinkedIdealPair hζ S hz) :
    fermatMinusStrictSelmer59 pair =
      normalizationCorrectionStrictSelmer59 hζ +
        cyclotomicStrictSelmerRepresentation59 K (-1)
          (fermatPlusStrictSelmer59 pair) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (Additive.toMul (fermatMinusStrictSelmer59 pair)).1 =
    (Additive.toMul (normalizationCorrectionStrictSelmer59 hζ)).1 *
      cyclotomicKummerHom59 K (-1)
        (Additive.toMul (fermatPlusStrictSelmer59 pair)).1
  rw [normalizationCorrectionStrictSelmer59_kummerQuotient]
  exact fermatMinusStrictSelmer59_kummerQuotient_eq_correction_mul_conj pair

/-! ## The odd character projection -/

/-- The root-of-unity correction projected into the same canonical odd
irregular character seat as the two Fermat factors. -/
noncomputable def normalizationCorrectionPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (hζ : IsPrimitiveRoot ζ 59) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
    irregularCharacter59 (normalizationCorrectionStrictSelmer59 hζ)

/-- Projecting a cyclotomic conjugate into the odd `chi = 15` seat negates
the projected class.  This is purely the character-idempotent algebra. -/
theorem irregularProjector_cyclotomicNegOne_eq_neg
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (x : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59
        (cyclotomicStrictSelmerRepresentation59 K (-1) x) =
      -characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 x := by
  let rho := cyclotomicStrictSelmerRepresentation59 K
  let e := characterIdempotent irregularCharacter59
  apply Subtype.ext
  change rho.asAlgebraHom e (rho (-1) x) =
    -rho.asAlgebraHom e x
  calc
    rho.asAlgebraHom e (rho (-1) x) =
        rho.asAlgebraHom e
          (rho.asAlgebraHom
            (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1)) x) := by
      rw [Representation.asAlgebraHom_of]
    _ =
        rho.asAlgebraHom
          (e * MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1)) x := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 (-1) * e) x := by
      rw [mul_comm]
    _ = rho.asAlgebraHom
          ((irregularCharacter59 (-1) : PadicInt 59) • e) x := by
      rw [groupElement_mul_characterIdempotent]
    _ = (irregularCharacter59 (-1) : PadicInt 59) •
          rho.asAlgebraHom e x := by
      rw [map_smul]
      rfl
    _ = -rho.asAlgebraHom e x := by
      change PadicInt.toZMod
          (irregularCharacter59 (-1) : PadicInt 59) •
            rho.asAlgebraHom e x = -rho.asAlgebraHom e x
      rw [irregularCharacter59_negOne_reduction]
      exact neg_one_smul (R := ZMod 59) (rho.asAlgebraHom e x)

/-- Exact projected relation.  The conjugated plus contribution becomes
negative, while the root-of-unity correction remains explicit. -/
theorem fermatMinusPrimalMode59_eq_correction_sub_plus
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    fermatMinusPrimalMode59 pair =
      normalizationCorrectionPrimalMode59 hζ -
        fermatPlusPrimalMode59 pair := by
  change characterProjectorAt
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59
        (fermatMinusStrictSelmer59 pair) =
    characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59
          (normalizationCorrectionStrictSelmer59 hζ) -
      characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59
          (fermatPlusStrictSelmer59 pair)
  rw [fermatMinusStrictSelmer59_eq_correction_add_conj,
    map_add, irregularProjector_cyclotomicNegOne_eq_neg]
  rw [sub_eq_add_neg]

/-- Removing the correction from the projected plus/minus relation is
equivalent to proving that its actual `chi = 15` projection vanishes. -/
theorem fermatMinusPrimalMode59_eq_neg_plus_iff_correction_eq_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hζ S hz) :
    fermatMinusPrimalMode59 pair = -fermatPlusPrimalMode59 pair ↔
      normalizationCorrectionPrimalMode59 hζ = 0 := by
  rw [fermatMinusPrimalMode59_eq_correction_sub_plus]
  constructor <;> intro h
  · calc
      normalizationCorrectionPrimalMode59 hζ =
          (normalizationCorrectionPrimalMode59 hζ -
            fermatPlusPrimalMode59 pair) + fermatPlusPrimalMode59 pair := by
        abel
      _ = (-fermatPlusPrimalMode59 pair) +
          fermatPlusPrimalMode59 pair := by rw [h]
      _ = 0 := neg_add_cancel _
  · calc
      normalizationCorrectionPrimalMode59 hζ -
          fermatPlusPrimalMode59 pair =
        0 - fermatPlusPrimalMode59 pair := by rw [h]
      _ = -fermatPlusPrimalMode59 pair := zero_sub _

end Fermat.FiftyNine.Conservation.FermatFactorConjugation59
