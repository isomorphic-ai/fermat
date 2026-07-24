import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.FourHundredNinetyOne.VandiverDerivativeValuation491

/-!
# Diagonal isolation in Vandiver's derivative calculation at 491

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (491²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `491`-adic valuation at
least two.

The diagonal residue is `-107803`, not the exponent-37 coincidence `-1`.
After Vandiver's outer factor `490`, the isolated rational coefficient is
the exact `-52823470` used in `diagonalDerivativeFactor491`.
-/

namespace Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.FourHundredNinetyOne.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*491 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder491 (k : SourceIndex 491) : ℕ :=
  derivativeBernoulliIndex491 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries491 (n : SourceIndex 491) : PowerSeries ℚ :=
  integralDiagonalExp 491 2512 463 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat491 (k n : SourceIndex 491) : ℕ :=
  ∑ j ∈ Finset.range 245,
    integralDiagonalWeight 491 2512 (sourceNumber n) j *
      (2512 ^ j) ^ derivativeBernoulliIndex491 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor491 (k : SourceIndex 491) : ℚ :=
  bernoulli (derivativeBernoulliIndex491 k) /
      (derivativeBernoulliIndex491 k : ℚ) *
    ((2512 : ℚ) ^ derivativeBernoulliIndex491 k - 1)

theorem sourceDerivativeOrder491_pos (k : SourceIndex 491) :
    0 < sourceDerivativeOrder491 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder491, derivativeBernoulliIndex491]
  omega

theorem sourceDerivativeOrder491_add_one (k : SourceIndex 491) :
    sourceDerivativeOrder491 k + 1 =
      derivativeBernoulliIndex491 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder491, derivativeBernoulliIndex491]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries491
    (k n : SourceIndex 491) :
    formalDerivativeAtZero (sourceDerivativeOrder491 k)
        (logarithmicDerivative (integralDiagonalSeries491 n)) =
      (characterCoefficientNat491 k n : ℚ) *
        baseDerivativeFactor491 k := by
  rw [integralDiagonalSeries491,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      491 2512 463 (sourceNumber n) (sourceDerivativeOrder491 k)
      (by norm_num) (sourceDerivativeOrder491_pos k)]
  have horder : sourceDerivativeOrder491 k =
      2 * (sourceNumber k * 491) - 1 := by
    simp [sourceDerivativeOrder491, derivativeBernoulliIndex491,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (2512 : ℚ) (sourceNumber k * 491) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 491) =
      derivativeBernoulliIndex491 k := by
    simp [derivativeBernoulliIndex491, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 491) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 491) - 1 + 1 =
      2 * (sourceNumber k * 491) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 491 : ℕ) =
      (derivativeBernoulliIndex491 k : ℚ) := by
    rw [derivativeBernoulliIndex491]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat491, baseDerivativeFactor491,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `491²`. -/
theorem characterCoefficientNat491_cast
    (k n : SourceIndex 491) :
    (characterCoefficientNat491 k n : ZMod (491 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum491 k n := by
  simp only [characterCoefficientNat491,
    VandiverDiagonalArithmetic.positiveCharacterSum491, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent491,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex491, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 491) =
      2 * 491 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `-107803`. -/
theorem characterCoefficientNat491_sub_diagonal_dvd
    (k n : SourceIndex 491) :
    ((491 : ℤ) ^ 2) ∣
      (characterCoefficientNat491 k n : ℤ) -
        (if k = n then -107803 else 0) := by
  have hcast := characterCoefficientNat491_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum491_eq_neg107803_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat491 k n : ℤ) -
        (if k = n then -107803 else 0) : ℤ) :
          ZMod (491 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat491 k n : ℤ) : ZMod (491 ^ 2)) =
          if k = n then -107803 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((491 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat491 k n : ℤ) -
        (if k = n then -107803 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((491 ^ 2 : ℕ) : ℤ) = (491 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `491`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient491_isPIntegral (k : SourceIndex 491) :
    IsPIntegral 491
      (bernoulli (derivativeBernoulliIndex491 k) /
        (derivativeBernoulliIndex491 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj488 : j ≤ 488 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 488
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 491) (j := j) (by norm_num) hj2 hj488 hjEven
  simpa [j, derivativeBernoulliIndex491, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `491`-integral. -/
theorem baseDerivativeFactor491_hasPadicValAtLeast_zero
    (k : SourceIndex 491) :
    HasPadicValAtLeast 491 0 (baseDerivativeFactor491 k) := by
  have hquotient : HasPadicValAtLeast 491 0
      (bernoulli (derivativeBernoulliIndex491 k) /
        (derivativeBernoulliIndex491 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient491_isPIntegral k)
  have hone : 1 ≤ 2512 ^ derivativeBernoulliIndex491 k :=
    Nat.one_le_pow (derivativeBernoulliIndex491 k) 2512 (by norm_num)
  have hrootCast :
      (2512 : ℚ) ^ derivativeBernoulliIndex491 k - 1 =
        ((2512 ^ derivativeBernoulliIndex491 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor491, hrootCast]
  have hroot : HasPadicValAtLeast 491 0
      (((2512 ^ derivativeBernoulliIndex491 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 490`. -/
def relationDerivative491
    (a : SourceIndex 491 → ℤ) (k : SourceIndex 491) : ℚ :=
  ∑ n, ((490 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder491 k)
      (logarithmicDerivative (integralDiagonalSeries491 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative491_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 491 → ℤ) (k : SourceIndex 491) :
    HasPadicValAtLeast 491 2
      (relationDerivative491 a k -
        (a k : ℚ) * diagonalDerivativeFactor491 k) := by
  classical
  let delta : SourceIndex 491 → ℤ :=
    fun n ↦ if k = n then -107803 else 0
  have hdeltaInt : (∑ n, a n * delta n) = -107803 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (-107803 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor491_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 491) :
      HasPadicValAtLeast 491 2
        ((((490 * a n) *
            ((characterCoefficientNat491 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor491 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat491_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat491 k n : ℤ) - delta n =
        (491 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (490 * a n) *
            ((characterCoefficientNat491 k n : ℤ) - delta n) =
          (491 : ℤ) ^ 2 * (490 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 491) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 491) (490 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 491 2
      (∑ n, ((((490 * a n) *
          ((characterCoefficientNat491 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor491 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor491 k =
      ((490 : ℚ) * (-107803 : ℚ)) * baseDerivativeFactor491 k := by
    simp only [diagonalDerivativeFactor491, baseDerivativeFactor491]
    ring
  have halgebra :
      relationDerivative491 a k -
          (a k : ℚ) * diagonalDerivativeFactor491 k =
        ∑ n, ((((490 * a n) *
            ((characterCoefficientNat491 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor491 k) := by
    symm
    calc
      (∑ n, ((((490 * a n) *
            ((characterCoefficientNat491 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor491 k)) =
          (∑ n, (((490 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat491 k n : ℚ) *
                baseDerivativeFactor491 k) -
            (490 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor491 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((490 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat491 k n : ℚ) *
                baseDerivativeFactor491 k)) -
            (490 : ℚ) * baseDerivativeFactor491 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative491 a k -
          (a k : ℚ) * diagonalDerivativeFactor491 k := by
        rw [hdeltaRat, hdiag, relationDerivative491]
        simp_rw [formalDerivative_integralDiagonalSeries491]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `491²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 491 → ℤ) (k : SourceIndex 491)
    (hrelation : HasPadicValAtLeast 491 2
      (relationDerivative491 a k)) :
    PadicValAtLeast 491 2
      ((a k : ℚ) * diagonalDerivativeFactor491 k) := by
  have herr :=
    relationDerivative491_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 491 2
      ((a k : ℚ) * diagonalDerivativeFactor491 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 491 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 491 2
      (relationDerivative491 a k)) :
    ∀ k, (491 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 491 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative
