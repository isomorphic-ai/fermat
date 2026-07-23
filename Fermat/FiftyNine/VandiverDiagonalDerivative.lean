import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.FiftyNine.VandiverDerivativeValuation

/-!
# Diagonal isolation in Vandiver's derivative calculation at 59

This module joins the exact formal-power-series calculation to the finite
`ZMod (59^2)` character-sum certificate.  It proves that the logarithmic
derivative of an arbitrary exponent relation differs from its single
diagonal Bernoulli term by a rational of `59`-adic valuation at least two.

The only downstream input still needed is the source's polynomial-remainder
argument asserting that the derivative of the whole relation also has
valuation at least two.
-/

namespace Fermat.FiftyNine.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.FiftyNine.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*59 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder59 (k : SourceIndex 59) : ℕ :=
  derivativeBernoulliIndex59 k - 1

/-- Vandiver's positive integral diagonal polynomial series at source
index `n`. -/
def integralDiagonalSeries59 (n : SourceIndex 59) : PowerSeries ℚ :=
  integralDiagonalExp 59 946 29 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat59 (k n : SourceIndex 59) : ℕ :=
  ∑ j ∈ Finset.range 29,
    integralDiagonalWeight 59 946 (sourceNumber n) j *
      (946 ^ j) ^ derivativeBernoulliIndex59 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor59 (k : SourceIndex 59) : ℚ :=
  bernoulli (derivativeBernoulliIndex59 k) /
      (derivativeBernoulliIndex59 k : ℚ) *
    ((946 : ℚ) ^ derivativeBernoulliIndex59 k - 1)

theorem sourceDerivativeOrder59_pos (k : SourceIndex 59) :
    0 < sourceDerivativeOrder59 k := by
  fin_cases k <;>
    norm_num [sourceDerivativeOrder59, derivativeBernoulliIndex59, sourceNumber]

theorem sourceDerivativeOrder59_add_one (k : SourceIndex 59) :
    sourceDerivativeOrder59 k + 1 = derivativeBernoulliIndex59 k := by
  fin_cases k <;>
    norm_num [sourceDerivativeOrder59, derivativeBernoulliIndex59, sourceNumber]

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries59
    (k n : SourceIndex 59) :
    formalDerivativeAtZero (sourceDerivativeOrder59 k)
        (logarithmicDerivative (integralDiagonalSeries59 n)) =
      (characterCoefficientNat59 k n : ℚ) *
        baseDerivativeFactor59 k := by
  rw [integralDiagonalSeries59,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      59 946 29 (sourceNumber n) (sourceDerivativeOrder59 k)
      (by norm_num) (sourceDerivativeOrder59_pos k)]
  have horder : sourceDerivativeOrder59 k =
      2 * (sourceNumber k * 59) - 1 := by
    simp [sourceDerivativeOrder59, derivativeBernoulliIndex59,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (946 : ℚ) (sourceNumber k * 59) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 59) =
      derivativeBernoulliIndex59 k := by
    simp [derivativeBernoulliIndex59, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 59) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 59) - 1 + 1 =
      2 * (sourceNumber k * 59) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 59 : ℕ) =
      (derivativeBernoulliIndex59 k : ℚ) := by
    rw [derivativeBernoulliIndex59]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat59, baseDerivativeFactor59,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `59^2`. -/
theorem characterCoefficientNat59_cast
    (k n : SourceIndex 59) :
    (characterCoefficientNat59 k n : ZMod (59 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum59 k n := by
  simp only [characterCoefficientNat59,
    VandiverDiagonalArithmetic.positiveCharacterSum59, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent59,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex59, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 59) =
      2 * 59 * (k.val + 1) * j by ac_rfl]

/-- Integral form of the diagonal congruence: the coefficient is `3067`
modulo `59^2` on the diagonal and zero off it. -/
theorem characterCoefficientNat59_sub_diagonal_dvd
    (k n : SourceIndex 59) :
    ((59 : ℤ) ^ 2) ∣
      (characterCoefficientNat59 k n : ℤ) -
        (if k = n then 3067 else 0) := by
  have hcast := characterCoefficientNat59_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum59_eq_diagonal]
    at hcast
  have hzero :
      (((characterCoefficientNat59 k n : ℤ) -
        (if k = n then 3067 else 0) : ℤ) : ZMod (59 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat59 k n : ℤ) : ZMod (59 ^ 2)) =
          if k = n then 3067 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((59 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat59 k n : ℤ) -
        (if k = n then 3067 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((59 ^ 2 : ℕ) : ℤ) = (59 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `59`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient59_isPIntegral (k : SourceIndex 59) :
    IsPIntegral 59
      (bernoulli (derivativeBernoulliIndex59 k) /
        (derivativeBernoulliIndex59 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj56 : j ≤ 56 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 56
    norm_num at hk
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 59) (j := j) (by norm_num) hj2 hj56 hjEven
  simpa [j, derivativeBernoulliIndex59, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `59`-integral; the root factor
is a `59`-adic unit. -/
theorem baseDerivativeFactor59_hasPadicValAtLeast_zero
    (k : SourceIndex 59) :
    HasPadicValAtLeast 59 0 (baseDerivativeFactor59 k) := by
  have hquotient : HasPadicValAtLeast 59 0
      (bernoulli (derivativeBernoulliIndex59 k) /
        (derivativeBernoulliIndex59 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient59_isPIntegral k)
  have hone : 1 ≤ 946 ^ derivativeBernoulliIndex59 k :=
    Nat.one_le_pow (derivativeBernoulliIndex59 k) 946 (by norm_num)
  have hrootCast :
      (946 : ℚ) ^ derivativeBernoulliIndex59 k - 1 =
        ((946 ^ derivativeBernoulliIndex59 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor59, hrootCast]
  have hroot : HasPadicValAtLeast 59 0
      (((946 ^ derivativeBernoulliIndex59 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative of the left side of
Vandiver's polynomial identity, including the source's outer factor
`p - 1 = 58`. -/
def relationDerivative59
    (a : SourceIndex 59 → ℤ) (k : SourceIndex 59) : ℚ :=
  ∑ n, ((58 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder59 k)
      (logarithmicDerivative (integralDiagonalSeries59 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative59_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 59 → ℤ) (k : SourceIndex 59) :
    HasPadicValAtLeast 59 2
      (relationDerivative59 a k -
        (a k : ℚ) * diagonalDerivativeFactor59 k) := by
  classical
  let delta : SourceIndex 59 → ℤ :=
    fun n ↦ if k = n then 3067 else 0
  have hdeltaInt : (∑ n, a n * delta n) = 3067 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        3067 * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor59_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 59) :
      HasPadicValAtLeast 59 2
        ((((58 * a n) *
            ((characterCoefficientNat59 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor59 k) := by
    obtain ⟨z, hz⟩ := characterCoefficientNat59_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat59 k n : ℤ) - delta n =
        (59 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (58 * a n) *
            ((characterCoefficientNat59 k n : ℤ) - delta n) =
          (59 : ℤ) ^ 2 * (58 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 59) 2
    have hzIntegral := HasPadicValAtLeast.intCast (p := 59) (58 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 59 2
      (∑ n, ((((58 * a n) *
          ((characterCoefficientNat59 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor59 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor59 k =
      (177886 : ℚ) * baseDerivativeFactor59 k := by
    simp only [diagonalDerivativeFactor59, baseDerivativeFactor59]
    ring
  have halgebra :
      relationDerivative59 a k -
          (a k : ℚ) * diagonalDerivativeFactor59 k =
        ∑ n, ((((58 * a n) *
            ((characterCoefficientNat59 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor59 k) := by
    symm
    calc
      (∑ n, ((((58 * a n) *
            ((characterCoefficientNat59 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor59 k)) =
          (∑ n, (((58 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat59 k n : ℚ) *
                baseDerivativeFactor59 k) -
            (58 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor59 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((58 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat59 k n : ℚ) *
                baseDerivativeFactor59 k)) -
            (58 : ℚ) * baseDerivativeFactor59 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative59 a k -
          (a k : ℚ) * diagonalDerivativeFactor59 k := by
        rw [hdeltaRat, hdiag, relationDerivative59]
        simp_rw [formalDerivative_integralDiagonalSeries59]
        ring
  rw [halgebra]
  exact hsum

/-- Once the polynomial-remainder side says that the total relation
derivative is divisible by `59^2`, the diagonal term is too. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 59 → ℤ) (k : SourceIndex 59)
    (hrelation : HasPadicValAtLeast 59 2 (relationDerivative59 a k)) :
    PadicValAtLeast 59 2
      ((a k : ℚ) * diagonalDerivativeFactor59 k) := by
  have herr :=
    relationDerivative59_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 59 2
      ((a k : ℚ) * diagonalDerivativeFactor59 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 59 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 59 2
      (relationDerivative59 a k)) :
    ∀ k, (59 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 59 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.FiftyNine.VandiverDiagonalDerivative
