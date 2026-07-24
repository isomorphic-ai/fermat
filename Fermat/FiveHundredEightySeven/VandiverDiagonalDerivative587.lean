import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.FiveHundredEightySeven.VandiverDerivativeValuation587

/-!
# Diagonal isolation in Vandiver's derivative calculation at 587

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (587²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `587`-adic valuation at
least two.

The diagonal residue is `-154417`, not the exponent-37 coincidence `-1`.
After Vandiver's outer factor `586`, the isolated rational coefficient is
the exact `-90488362` used in `diagonalDerivativeFactor587`.
-/

namespace Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.FiveHundredEightySeven.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*587 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder587 (k : SourceIndex 587) : ℕ :=
  derivativeBernoulliIndex587 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries587 (n : SourceIndex 587) : PowerSeries ℚ :=
  integralDiagonalExp 587 6529 258 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat587 (k n : SourceIndex 587) : ℕ :=
  ∑ j ∈ Finset.range 293,
    integralDiagonalWeight 587 6529 (sourceNumber n) j *
      (6529 ^ j) ^ derivativeBernoulliIndex587 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor587 (k : SourceIndex 587) : ℚ :=
  bernoulli (derivativeBernoulliIndex587 k) /
      (derivativeBernoulliIndex587 k : ℚ) *
    ((6529 : ℚ) ^ derivativeBernoulliIndex587 k - 1)

theorem sourceDerivativeOrder587_pos (k : SourceIndex 587) :
    0 < sourceDerivativeOrder587 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder587, derivativeBernoulliIndex587]
  omega

theorem sourceDerivativeOrder587_add_one (k : SourceIndex 587) :
    sourceDerivativeOrder587 k + 1 =
      derivativeBernoulliIndex587 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder587, derivativeBernoulliIndex587]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries587
    (k n : SourceIndex 587) :
    formalDerivativeAtZero (sourceDerivativeOrder587 k)
        (logarithmicDerivative (integralDiagonalSeries587 n)) =
      (characterCoefficientNat587 k n : ℚ) *
        baseDerivativeFactor587 k := by
  rw [integralDiagonalSeries587,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      587 6529 258 (sourceNumber n) (sourceDerivativeOrder587 k)
      (by norm_num) (sourceDerivativeOrder587_pos k)]
  have horder : sourceDerivativeOrder587 k =
      2 * (sourceNumber k * 587) - 1 := by
    simp [sourceDerivativeOrder587, derivativeBernoulliIndex587,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (6529 : ℚ) (sourceNumber k * 587) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 587) =
      derivativeBernoulliIndex587 k := by
    simp [derivativeBernoulliIndex587, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 587) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 587) - 1 + 1 =
      2 * (sourceNumber k * 587) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 587 : ℕ) =
      (derivativeBernoulliIndex587 k : ℚ) := by
    rw [derivativeBernoulliIndex587]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat587, baseDerivativeFactor587,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `587²`. -/
theorem characterCoefficientNat587_cast
    (k n : SourceIndex 587) :
    (characterCoefficientNat587 k n : ZMod (587 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum587 k n := by
  simp only [characterCoefficientNat587,
    VandiverDiagonalArithmetic.positiveCharacterSum587, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent587,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex587, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 587) =
      2 * 587 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `-154417`. -/
theorem characterCoefficientNat587_sub_diagonal_dvd
    (k n : SourceIndex 587) :
    ((587 : ℤ) ^ 2) ∣
      (characterCoefficientNat587 k n : ℤ) -
        (if k = n then -154417 else 0) := by
  have hcast := characterCoefficientNat587_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum587_eq_neg154417_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat587 k n : ℤ) -
        (if k = n then -154417 else 0) : ℤ) :
          ZMod (587 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat587 k n : ℤ) : ZMod (587 ^ 2)) =
          if k = n then -154417 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((587 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat587 k n : ℤ) -
        (if k = n then -154417 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((587 ^ 2 : ℕ) : ℤ) = (587 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `587`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient587_isPIntegral (k : SourceIndex 587) :
    IsPIntegral 587
      (bernoulli (derivativeBernoulliIndex587 k) /
        (derivativeBernoulliIndex587 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj584 : j ≤ 584 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 584
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 587) (j := j) (by norm_num) hj2 hj584 hjEven
  simpa [j, derivativeBernoulliIndex587, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `587`-integral. -/
theorem baseDerivativeFactor587_hasPadicValAtLeast_zero
    (k : SourceIndex 587) :
    HasPadicValAtLeast 587 0 (baseDerivativeFactor587 k) := by
  have hquotient : HasPadicValAtLeast 587 0
      (bernoulli (derivativeBernoulliIndex587 k) /
        (derivativeBernoulliIndex587 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient587_isPIntegral k)
  have hone : 1 ≤ 6529 ^ derivativeBernoulliIndex587 k :=
    Nat.one_le_pow (derivativeBernoulliIndex587 k) 6529 (by norm_num)
  have hrootCast :
      (6529 : ℚ) ^ derivativeBernoulliIndex587 k - 1 =
        ((6529 ^ derivativeBernoulliIndex587 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor587, hrootCast]
  have hroot : HasPadicValAtLeast 587 0
      (((6529 ^ derivativeBernoulliIndex587 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 586`. -/
def relationDerivative587
    (a : SourceIndex 587 → ℤ) (k : SourceIndex 587) : ℚ :=
  ∑ n, ((586 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder587 k)
      (logarithmicDerivative (integralDiagonalSeries587 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative587_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 587 → ℤ) (k : SourceIndex 587) :
    HasPadicValAtLeast 587 2
      (relationDerivative587 a k -
        (a k : ℚ) * diagonalDerivativeFactor587 k) := by
  classical
  let delta : SourceIndex 587 → ℤ :=
    fun n ↦ if k = n then -154417 else 0
  have hdeltaInt : (∑ n, a n * delta n) = -154417 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (-154417 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor587_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 587) :
      HasPadicValAtLeast 587 2
        ((((586 * a n) *
            ((characterCoefficientNat587 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor587 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat587_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat587 k n : ℤ) - delta n =
        (587 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (586 * a n) *
            ((characterCoefficientNat587 k n : ℤ) - delta n) =
          (587 : ℤ) ^ 2 * (586 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 587) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 587) (586 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 587 2
      (∑ n, ((((586 * a n) *
          ((characterCoefficientNat587 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor587 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor587 k =
      ((586 : ℚ) * (-154417 : ℚ)) * baseDerivativeFactor587 k := by
    simp only [diagonalDerivativeFactor587, baseDerivativeFactor587]
    ring
  have halgebra :
      relationDerivative587 a k -
          (a k : ℚ) * diagonalDerivativeFactor587 k =
        ∑ n, ((((586 * a n) *
            ((characterCoefficientNat587 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor587 k) := by
    symm
    calc
      (∑ n, ((((586 * a n) *
            ((characterCoefficientNat587 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor587 k)) =
          (∑ n, (((586 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat587 k n : ℚ) *
                baseDerivativeFactor587 k) -
            (586 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor587 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((586 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat587 k n : ℚ) *
                baseDerivativeFactor587 k)) -
            (586 : ℚ) * baseDerivativeFactor587 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative587 a k -
          (a k : ℚ) * diagonalDerivativeFactor587 k := by
        rw [hdeltaRat, hdiag, relationDerivative587]
        simp_rw [formalDerivative_integralDiagonalSeries587]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `587²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 587 → ℤ) (k : SourceIndex 587)
    (hrelation : HasPadicValAtLeast 587 2
      (relationDerivative587 a k)) :
    PadicValAtLeast 587 2
      ((a k : ℚ) * diagonalDerivativeFactor587 k) := by
  have herr :=
    relationDerivative587_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 587 2
      ((a k : ℚ) * diagonalDerivativeFactor587 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 587 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 587 2
      (relationDerivative587 a k)) :
    ∀ k, (587 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 587 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative
