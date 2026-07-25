import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.OneThousandThreeHundredEightyOne.VandiverDerivativeValuation1381

/-!
# Diagonal isolation in Vandiver's derivative calculation at 1381

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (1381²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `1381`-adic valuation at
least two.

The diagonal residue is `450570`, not the exponent-37 coincidence `-1`.
After Vandiver's outer factor `1380`, the isolated rational coefficient is
the exact `621786600` used in `diagonalDerivativeFactor1381`.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.OneThousandThreeHundredEightyOne.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*1381 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder1381 (k : SourceIndex 1381) : ℕ :=
  derivativeBernoulliIndex1381 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries1381 (n : SourceIndex 1381) : PowerSeries ℚ :=
  integralDiagonalExp 1381 653 1055 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat1381 (k n : SourceIndex 1381) : ℕ :=
  ∑ j ∈ Finset.range 690,
    integralDiagonalWeight 1381 653 (sourceNumber n) j *
      (653 ^ j) ^ derivativeBernoulliIndex1381 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor1381 (k : SourceIndex 1381) : ℚ :=
  bernoulli (derivativeBernoulliIndex1381 k) /
      (derivativeBernoulliIndex1381 k : ℚ) *
    ((653 : ℚ) ^ derivativeBernoulliIndex1381 k - 1)

theorem sourceDerivativeOrder1381_pos (k : SourceIndex 1381) :
    0 < sourceDerivativeOrder1381 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder1381, derivativeBernoulliIndex1381]
  omega

theorem sourceDerivativeOrder1381_add_one (k : SourceIndex 1381) :
    sourceDerivativeOrder1381 k + 1 =
      derivativeBernoulliIndex1381 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder1381, derivativeBernoulliIndex1381]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries1381
    (k n : SourceIndex 1381) :
    formalDerivativeAtZero (sourceDerivativeOrder1381 k)
        (logarithmicDerivative (integralDiagonalSeries1381 n)) =
      (characterCoefficientNat1381 k n : ℚ) *
        baseDerivativeFactor1381 k := by
  rw [integralDiagonalSeries1381,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      1381 653 1055 (sourceNumber n) (sourceDerivativeOrder1381 k)
      (by norm_num) (sourceDerivativeOrder1381_pos k)]
  have horder : sourceDerivativeOrder1381 k =
      2 * (sourceNumber k * 1381) - 1 := by
    simp [sourceDerivativeOrder1381, derivativeBernoulliIndex1381,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (653 : ℚ) (sourceNumber k * 1381) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 1381) =
      derivativeBernoulliIndex1381 k := by
    simp [derivativeBernoulliIndex1381, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 1381) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 1381) - 1 + 1 =
      2 * (sourceNumber k * 1381) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 1381 : ℕ) =
      (derivativeBernoulliIndex1381 k : ℚ) := by
    rw [derivativeBernoulliIndex1381]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat1381, baseDerivativeFactor1381,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `1381²`. -/
theorem characterCoefficientNat1381_cast
    (k n : SourceIndex 1381) :
    (characterCoefficientNat1381 k n : ZMod (1381 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum1381 k n := by
  simp only [characterCoefficientNat1381,
    VandiverDiagonalArithmetic.positiveCharacterSum1381, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent1381,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex1381, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 1381) =
      2 * 1381 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `450570`. -/
theorem characterCoefficientNat1381_sub_diagonal_dvd
    (k n : SourceIndex 1381) :
    ((1381 : ℤ) ^ 2) ∣
      (characterCoefficientNat1381 k n : ℤ) -
        (if k = n then 450570 else 0) := by
  have hcast := characterCoefficientNat1381_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum1381_eq_450570_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat1381 k n : ℤ) -
        (if k = n then 450570 else 0) : ℤ) :
          ZMod (1381 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat1381 k n : ℤ) : ZMod (1381 ^ 2)) =
          if k = n then 450570 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((1381 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat1381 k n : ℤ) -
        (if k = n then 450570 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((1381 ^ 2 : ℕ) : ℤ) = (1381 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `1381`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient1381_isPIntegral (k : SourceIndex 1381) :
    IsPIntegral 1381
      (bernoulli (derivativeBernoulliIndex1381 k) /
        (derivativeBernoulliIndex1381 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj1378 : j ≤ 1378 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 1378
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 1381) (j := j) (by norm_num) hj2 hj1378 hjEven
  simpa [j, derivativeBernoulliIndex1381, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `1381`-integral. -/
theorem baseDerivativeFactor1381_hasPadicValAtLeast_zero
    (k : SourceIndex 1381) :
    HasPadicValAtLeast 1381 0 (baseDerivativeFactor1381 k) := by
  have hquotient : HasPadicValAtLeast 1381 0
      (bernoulli (derivativeBernoulliIndex1381 k) /
        (derivativeBernoulliIndex1381 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient1381_isPIntegral k)
  have hone : 1 ≤ 653 ^ derivativeBernoulliIndex1381 k :=
    Nat.one_le_pow (derivativeBernoulliIndex1381 k) 653 (by norm_num)
  have hrootCast :
      (653 : ℚ) ^ derivativeBernoulliIndex1381 k - 1 =
        ((653 ^ derivativeBernoulliIndex1381 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor1381, hrootCast]
  have hroot : HasPadicValAtLeast 1381 0
      (((653 ^ derivativeBernoulliIndex1381 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 1380`. -/
def relationDerivative1381
    (a : SourceIndex 1381 → ℤ) (k : SourceIndex 1381) : ℚ :=
  ∑ n, ((1380 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder1381 k)
      (logarithmicDerivative (integralDiagonalSeries1381 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative1381_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 1381 → ℤ) (k : SourceIndex 1381) :
    HasPadicValAtLeast 1381 2
      (relationDerivative1381 a k -
        (a k : ℚ) * diagonalDerivativeFactor1381 k) := by
  classical
  let delta : SourceIndex 1381 → ℤ :=
    fun n ↦ if k = n then 450570 else 0
  have hdeltaInt : (∑ n, a n * delta n) = 450570 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (450570 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor1381_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 1381) :
      HasPadicValAtLeast 1381 2
        ((((1380 * a n) *
            ((characterCoefficientNat1381 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor1381 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat1381_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat1381 k n : ℤ) - delta n =
        (1381 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (1380 * a n) *
            ((characterCoefficientNat1381 k n : ℤ) - delta n) =
          (1381 : ℤ) ^ 2 * (1380 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 1381) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 1381) (1380 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1
    all_goals norm_num [Int.cast_mul, Int.cast_pow]
    all_goals ring
  have hsum : HasPadicValAtLeast 1381 2
      (∑ n, ((((1380 * a n) *
          ((characterCoefficientNat1381 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor1381 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor1381 k =
      ((1380 : ℚ) * (450570 : ℚ)) * baseDerivativeFactor1381 k := by
    simp only [diagonalDerivativeFactor1381, baseDerivativeFactor1381]
    ring
  have halgebra :
      relationDerivative1381 a k -
          (a k : ℚ) * diagonalDerivativeFactor1381 k =
        ∑ n, ((((1380 * a n) *
            ((characterCoefficientNat1381 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor1381 k) := by
    symm
    calc
      (∑ n, ((((1380 * a n) *
            ((characterCoefficientNat1381 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor1381 k)) =
          (∑ n, (((1380 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat1381 k n : ℚ) *
                baseDerivativeFactor1381 k) -
            (1380 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor1381 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((1380 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat1381 k n : ℚ) *
                baseDerivativeFactor1381 k)) -
            (1380 : ℚ) * baseDerivativeFactor1381 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative1381 a k -
          (a k : ℚ) * diagonalDerivativeFactor1381 k := by
        rw [hdeltaRat, hdiag, relationDerivative1381]
        simp_rw [formalDerivative_integralDiagonalSeries1381]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `1381²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 1381 → ℤ) (k : SourceIndex 1381)
    (hrelation : HasPadicValAtLeast 1381 2
      (relationDerivative1381 a k)) :
    PadicValAtLeast 1381 2
      ((a k : ℚ) * diagonalDerivativeFactor1381 k) := by
  have herr :=
    relationDerivative1381_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 1381 2
      ((a k : ℚ) * diagonalDerivativeFactor1381 k) := by
    have := hrelation.sub herr
    convert this using 1
    ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 1381 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 1381 2
      (relationDerivative1381 a k)) :
    ∀ k, (1381 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 1381 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative
