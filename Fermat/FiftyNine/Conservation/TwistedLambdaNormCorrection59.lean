/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The exact depth-59 correction in the twisted-lambda norm problem

For a selected root `alpha^59 = 60 * lambda`, the elementary identity

`Norm(1 + alpha) = 1 + 60 * lambda`

reduces the question whether `zeta_59` is a norm to the same question for

`(1 + 60 * lambda) / zeta_59 = 1 + 59 * lambda / zeta_59`.

This file proves both directions of that reduction and proves that the
correction differs from one by an element of exact lambda-adic order `59`.
It does not assert the remaining norm-filtration or Artin--Hasse theorem.
-/
import Fermat.Conservation.KummerOnePlusRootNorm59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
import Mathlib.Tactic

open scoped NumberField
open Polynomial

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59

open Fermat.Conservation.KummerCyclicQuotient59
open Fermat.Conservation.KummerOnePlusRootNorm59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- Mathlib's selected 59th root of the 60-twisted lambda radicand. -/
def twistedLambdaRoot59 : twistedLambdaKummerExtension59 K := by
  letI : IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (LambdaField59 K) (twistedLambda59 K)
  exact rootOfSplitsXPowSubC (n := 59) (NeZero.pos 59)
    (twistedLambda59 K) (twistedLambdaKummerExtension59 K)

theorem twistedLambdaRoot59_pow :
    twistedLambdaRoot59 K ^ 59 =
      algebraMap (LambdaField59 K) (twistedLambdaKummerExtension59 K)
        (twistedLambda59 K) := by
  letI : IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (LambdaField59 K) (twistedLambda59 K)
  exact rootOfSplitsXPowSubC_pow (n := 59)
    (twistedLambda59 K) (twistedLambdaKummerExtension59 K)

/-- The one-plus-root norm for the twisted radicand. -/
theorem norm_one_add_twistedLambdaRoot59 :
    Algebra.norm (LambdaField59 K) (1 + twistedLambdaRoot59 K) =
      1 + twistedLambda59 K := by
  letI : IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (LambdaField59 K) (twistedLambda59 K)
  exact norm_one_add_kummerRoot59
    (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (twistedLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambda59_not_pow K)

/-- The critical base-field correction left after dividing a hypothetical
primitive-root norm witness by the elementary one-plus-root norm. -/
def primitiveRootNormCorrection59 : LambdaField59 K :=
  (1 + twistedLambda59 K) / lambdaLocalPrimitiveRoot59 K

/-- The correction is the depth-59 principal unit
`1 + 59 * lambda / zeta`. -/
theorem primitiveRootNormCorrection59_eq :
    primitiveRootNormCorrection59 K =
      1 + (59 : LambdaField59 K) * canonicalLambda59 K /
        lambdaLocalPrimitiveRoot59 K := by
  have hzeta : lambdaLocalPrimitiveRoot59 K ≠ 0 :=
    (lambdaLocalPrimitiveRoot59_isPrimitive K).ne_zero (by norm_num)
  have htwist : twistUnit59 K = (60 : LambdaField59 K) := by
    rw [twistUnit59, map_ofNat]
  rw [primitiveRootNormCorrection59, twistedLambda59, htwist]
  change
    (1 + (60 : LambdaField59 K) * canonicalLambda59 K) /
        lambdaLocalPrimitiveRoot59 K = _
  rw [canonicalLambda59]
  field_simp
  ring

/-- Rational `59` has lambda-adic order `58` in the cyclotomic completion. -/
theorem natCast59_valuation :
    Valued.v (59 : LambdaField59 K) = WithZero.exp (-58 : ℤ) := by
  have hfield : (59 : LambdaField59 K) =
      NumberField.FinitePlace.embedding (lambdaPlace59 K) (59 : K) := by
    exact (map_natCast
      (NumberField.FinitePlace.embedding (lambdaPlace59 K)) 59).symm
  rw [hfield, valuation_embedding59]
  have hglobal :
      Ideal.span ({(59 : NumberField.RingOfIntegers K)} :
        Set (NumberField.RingOfIntegers K)) =
        (lambdaIdeal59 K) ^ 58 := by
    have h := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow
      59 0 (globalPrimitiveRoot59_isPrimitive K)
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos 59)),
      Nat.totient_prime (by decide : Nat.Prime 59)] at h
    simpa [lambdaIdeal59, Ideal.map_span] using h
  change (lambdaPlace59 K).valuation K
      (algebraMap (NumberField.RingOfIntegers K) K
        (59 : NumberField.RingOfIntegers K)) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity]
  rw [hglobal]
  rw [lambdaPlace59_asIdeal]
  rw [multiplicity_pow_self]
  · norm_num
  · exact lambdaIdeal59_ne_bot K
  · exact Ideal.isUnit_iff.not.mpr (lambdaIdeal59_isPrime K).ne_top
  · norm_num

/-- The local primitive root is a valuation unit. -/
theorem primitiveRoot59_valuation :
    Valued.v (lambdaLocalPrimitiveRoot59 K) = 1 := by
  have hpow :
      Valued.v (lambdaLocalPrimitiveRoot59 K) ^ 59 = 1 := by
    rw [← map_pow,
      (lambdaLocalPrimitiveRoot59_isPrimitive K).pow_eq_one, map_one]
  exact (pow_eq_one_iff_left (by norm_num : 59 ≠ 0)).mp hpow

/-- The critical correction differs from one by an element of exact
lambda-adic order `59`. -/
theorem primitiveRootNormCorrection59_sub_one_valuation :
    Valued.v (primitiveRootNormCorrection59 K - 1) =
      WithZero.exp (-59 : ℤ) := by
  rw [primitiveRootNormCorrection59_eq]
  ring_nf
  rw [map_mul, map_mul, map_inv₀, natCast59_valuation,
    canonicalLambda59_valuation, primitiveRoot59_valuation, inv_one]
  rw [mul_one, ← WithZero.exp_add]
  norm_num

theorem primitiveRootNormCorrection59_ne_zero :
    primitiveRootNormCorrection59 K ≠ 0 := by
  intro hzero
  have hval := primitiveRootNormCorrection59_sub_one_valuation K
  rw [hzero, zero_sub, Valuation.map_neg, map_one] at hval
  have hlog := congrArg WithZero.log hval
  norm_num at hlog

/-- Any norm witness for the primitive root in the twisted extension yields
a norm witness for the explicit critical principal-unit correction. -/
theorem exists_correction_norm_of_primitiveRoot_norm
    (beta : twistedLambdaKummerExtension59 K)
    (hbeta : Algebra.norm (LambdaField59 K) beta =
      lambdaLocalPrimitiveRoot59 K) :
    ∃ gamma : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) gamma =
        primitiveRootNormCorrection59 K := by
  letI : IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (LambdaField59 K) (twistedLambda59 K)
  letI : FiniteDimensional (LambdaField59 K)
      (twistedLambdaKummerExtension59 K) :=
    Polynomial.IsSplittingField.finiteDimensional
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K))
  refine ⟨(1 + twistedLambdaRoot59 K) / beta, ?_⟩
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    norm_one_add_twistedLambdaRoot59 K, hbeta]
  rfl

/-- Conversely, a norm witness for the critical correction recovers a norm
witness for the primitive root. -/
theorem exists_primitiveRoot_norm_of_correction_norm
    (gamma : twistedLambdaKummerExtension59 K)
    (hgamma : Algebra.norm (LambdaField59 K) gamma =
      primitiveRootNormCorrection59 K) :
    ∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K := by
  letI : IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (LambdaField59 K) (twistedLambda59 K)
  letI : FiniteDimensional (LambdaField59 K)
      (twistedLambdaKummerExtension59 K) :=
    Polynomial.IsSplittingField.finiteDimensional
      (twistedLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (twistedLambda59 K))
  have hcorrection : primitiveRootNormCorrection59 K ≠ 0 :=
    primitiveRootNormCorrection59_ne_zero K
  have hnum : (1 + twistedLambda59 K) ≠ 0 := by
    intro hzero
    apply hcorrection
    rw [primitiveRootNormCorrection59, hzero, zero_div]
  have hzeta : lambdaLocalPrimitiveRoot59 K ≠ 0 :=
    (lambdaLocalPrimitiveRoot59_isPrimitive K).ne_zero (by norm_num)
  refine ⟨(1 + twistedLambdaRoot59 K) / gamma, ?_⟩
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    norm_one_add_twistedLambdaRoot59 K, hgamma,
    primitiveRootNormCorrection59]
  field_simp

/-- The original primitive-root norm problem is exactly the norm problem for
the explicit depth-59 correction unit. -/
theorem primitiveRoot_is_norm_iff_correction_is_norm :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
    (∃ gamma : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) gamma =
        primitiveRootNormCorrection59 K) := by
  constructor
  · rintro ⟨beta, hbeta⟩
    exact exists_correction_norm_of_primitiveRoot_norm K beta hbeta
  · rintro ⟨gamma, hgamma⟩
    exact exists_primitiveRoot_norm_of_correction_norm K gamma hgamma

end Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
