import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.ThirtySeven.VandiverDerivativeValuation

/-!
# Diagonal isolation in Vandiver's derivative calculation at 37

This module joins the exact formal-power-series calculation to the finite
`ZMod (37^2)` character-sum certificate.  It proves that the logarithmic
derivative of an arbitrary exponent relation differs from its single
diagonal Bernoulli term by a rational of `37`-adic valuation at least two.

The only downstream input still needed is the source's polynomial-remainder
argument asserting that the derivative of the whole relation also has
valuation at least two.
-/

namespace Fermat.ThirtySeven.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.ThirtySeven.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*37 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder37 (k : SourceIndex 37) : ℕ :=
  derivativeBernoulliIndex37 k - 1

/-- Vandiver's positive integral diagonal polynomial series at source
index `n`. -/
def integralDiagonalSeries37 (n : SourceIndex 37) : PowerSeries ℚ :=
  integralDiagonalExp 37 76 18 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat37 (k n : SourceIndex 37) : ℕ :=
  ∑ j ∈ Finset.range 18,
    integralDiagonalWeight 37 76 (sourceNumber n) j *
      (76 ^ j) ^ derivativeBernoulliIndex37 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor37 (k : SourceIndex 37) : ℚ :=
  bernoulli (derivativeBernoulliIndex37 k) /
      (derivativeBernoulliIndex37 k : ℚ) *
    ((76 : ℚ) ^ derivativeBernoulliIndex37 k - 1)

theorem sourceDerivativeOrder37_pos (k : SourceIndex 37) :
    0 < sourceDerivativeOrder37 k := by
  fin_cases k <;>
    norm_num [sourceDerivativeOrder37, derivativeBernoulliIndex37, sourceNumber]

theorem sourceDerivativeOrder37_add_one (k : SourceIndex 37) :
    sourceDerivativeOrder37 k + 1 = derivativeBernoulliIndex37 k := by
  fin_cases k <;>
    norm_num [sourceDerivativeOrder37, derivativeBernoulliIndex37, sourceNumber]

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries37
    (k n : SourceIndex 37) :
    formalDerivativeAtZero (sourceDerivativeOrder37 k)
        (logarithmicDerivative (integralDiagonalSeries37 n)) =
      (characterCoefficientNat37 k n : ℚ) *
        baseDerivativeFactor37 k := by
  rw [integralDiagonalSeries37,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      37 76 18 (sourceNumber n) (sourceDerivativeOrder37 k)
      (by norm_num) (sourceDerivativeOrder37_pos k)]
  have horder : sourceDerivativeOrder37 k =
      2 * (sourceNumber k * 37) - 1 := by
    simp [sourceDerivativeOrder37, derivativeBernoulliIndex37,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (76 : ℚ) (sourceNumber k * 37) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 37) =
      derivativeBernoulliIndex37 k := by
    simp [derivativeBernoulliIndex37, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 37) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 37) - 1 + 1 =
      2 * (sourceNumber k * 37) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 37 : ℕ) =
      (derivativeBernoulliIndex37 k : ℚ) := by
    rw [derivativeBernoulliIndex37]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat37, baseDerivativeFactor37,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `37^2`. -/
theorem characterCoefficientNat37_cast
    (k n : SourceIndex 37) :
    (characterCoefficientNat37 k n : ZMod (37 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum37 k n := by
  simp only [characterCoefficientNat37,
    VandiverDiagonalArithmetic.positiveCharacterSum37, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent37,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex37, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 37) =
      2 * 37 * (k.val + 1) * j by ac_rfl]

/-- Integral form of the diagonal congruence: the coefficient is `-1`
modulo `37^2` on the diagonal and zero off it. -/
theorem characterCoefficientNat37_sub_diagonal_dvd
    (k n : SourceIndex 37) :
    ((37 : ℤ) ^ 2) ∣
      (characterCoefficientNat37 k n : ℤ) -
        (if k = n then -1 else 0) := by
  have hcast := characterCoefficientNat37_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum37_eq_neg_one_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat37 k n : ℤ) -
        (if k = n then -1 else 0) : ℤ) : ZMod (37 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat37 k n : ℤ) : ZMod (37 ^ 2)) =
          if k = n then -1 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((37 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat37 k n : ℤ) -
        (if k = n then -1 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((37 ^ 2 : ℕ) : ℤ) = (37 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `37`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient37_isPIntegral (k : SourceIndex 37) :
    IsPIntegral 37
      (bernoulli (derivativeBernoulliIndex37 k) /
        (derivativeBernoulliIndex37 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj34 : j ≤ 34 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 34
    norm_num at hk
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 37) (j := j) (by norm_num) hj2 hj34 hjEven
  simpa [j, derivativeBernoulliIndex37, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `37`-integral; the root factor
is a `37`-adic unit. -/
theorem baseDerivativeFactor37_hasPadicValAtLeast_zero
    (k : SourceIndex 37) :
    HasPadicValAtLeast 37 0 (baseDerivativeFactor37 k) := by
  have hquotient : HasPadicValAtLeast 37 0
      (bernoulli (derivativeBernoulliIndex37 k) /
        (derivativeBernoulliIndex37 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient37_isPIntegral k)
  have hone : 1 ≤ 76 ^ derivativeBernoulliIndex37 k :=
    Nat.one_le_pow (derivativeBernoulliIndex37 k) 76 (by norm_num)
  have hrootCast :
      (76 : ℚ) ^ derivativeBernoulliIndex37 k - 1 =
        ((76 ^ derivativeBernoulliIndex37 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor37, hrootCast]
  have hroot : HasPadicValAtLeast 37 0
      (((76 ^ derivativeBernoulliIndex37 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative of the left side of
Vandiver's polynomial identity, including the source's outer factor
`p - 1 = 36`. -/
def relationDerivative37
    (a : SourceIndex 37 → ℤ) (k : SourceIndex 37) : ℚ :=
  ∑ n, ((36 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder37 k)
      (logarithmicDerivative (integralDiagonalSeries37 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative37_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 37 → ℤ) (k : SourceIndex 37) :
    HasPadicValAtLeast 37 2
      (relationDerivative37 a k -
        (a k : ℚ) * diagonalDerivativeFactor37 k) := by
  classical
  let delta : SourceIndex 37 → ℤ :=
    fun n ↦ if k = n then -1 else 0
  have hdeltaInt : (∑ n, a n * delta n) = -a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) = -(a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor37_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 37) :
      HasPadicValAtLeast 37 2
        ((((36 * a n) *
            ((characterCoefficientNat37 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor37 k) := by
    obtain ⟨z, hz⟩ := characterCoefficientNat37_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat37 k n : ℤ) - delta n =
        (37 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (36 * a n) *
            ((characterCoefficientNat37 k n : ℤ) - delta n) =
          (37 : ℤ) ^ 2 * (36 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 37) 2
    have hzIntegral := HasPadicValAtLeast.intCast (p := 37) (36 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 37 2
      (∑ n, ((((36 * a n) *
          ((characterCoefficientNat37 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor37 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor37 k =
      (-36 : ℚ) * baseDerivativeFactor37 k := by
    simp only [diagonalDerivativeFactor37, baseDerivativeFactor37]
    ring
  have halgebra :
      relationDerivative37 a k -
          (a k : ℚ) * diagonalDerivativeFactor37 k =
        ∑ n, ((((36 * a n) *
            ((characterCoefficientNat37 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor37 k) := by
    symm
    calc
      (∑ n, ((((36 * a n) *
            ((characterCoefficientNat37 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor37 k)) =
          (∑ n, (((36 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat37 k n : ℚ) *
                baseDerivativeFactor37 k) -
            (36 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor37 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((36 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat37 k n : ℚ) *
                baseDerivativeFactor37 k)) -
            (36 : ℚ) * baseDerivativeFactor37 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative37 a k -
          (a k : ℚ) * diagonalDerivativeFactor37 k := by
        rw [hdeltaRat, hdiag, relationDerivative37]
        simp_rw [formalDerivative_integralDiagonalSeries37]
        ring
  rw [halgebra]
  exact hsum

/-- Once the polynomial-remainder side says that the total relation
derivative is divisible by `37^2`, the diagonal term is too. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 37 → ℤ) (k : SourceIndex 37)
    (hrelation : HasPadicValAtLeast 37 2 (relationDerivative37 a k)) :
    PadicValAtLeast 37 2
      ((a k : ℚ) * diagonalDerivativeFactor37 k) := by
  have herr :=
    relationDerivative37_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 37 2
      ((a k : ℚ) * diagonalDerivativeFactor37 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 37 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 37 2
      (relationDerivative37 a k)) :
    ∀ k, (37 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 37 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.ThirtySeven.VandiverDiagonalDerivative
