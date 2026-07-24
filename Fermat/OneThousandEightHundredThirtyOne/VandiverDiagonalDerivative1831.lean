import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.OneThousandEightHundredThirtyOne.VandiverDerivativeValuation1831

/-!
# Diagonal isolation in Vandiver's derivative calculation at 1831

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (1831²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `1831`-adic valuation at
least two.

The diagonal residue is `4342590`, not the exponent-37 coincidence `-1`.
After Vandiver's outer factor `1830`, the isolated rational coefficient is
the exact `7946939700` used in `diagonalDerivativeFactor1831`.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.OneThousandEightHundredThirtyOne.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*1831 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder1831 (k : SourceIndex 1831) : ℕ :=
  derivativeBernoulliIndex1831 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries1831 (n : SourceIndex 1831) : PowerSeries ℚ :=
  integralDiagonalExp 1831 4746 374 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat1831 (k n : SourceIndex 1831) : ℕ :=
  ∑ j ∈ Finset.range 915,
    integralDiagonalWeight 1831 4746 (sourceNumber n) j *
      (4746 ^ j) ^ derivativeBernoulliIndex1831 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor1831 (k : SourceIndex 1831) : ℚ :=
  bernoulli (derivativeBernoulliIndex1831 k) /
      (derivativeBernoulliIndex1831 k : ℚ) *
    ((4746 : ℚ) ^ derivativeBernoulliIndex1831 k - 1)

theorem sourceDerivativeOrder1831_pos (k : SourceIndex 1831) :
    0 < sourceDerivativeOrder1831 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder1831, derivativeBernoulliIndex1831]
  omega

theorem sourceDerivativeOrder1831_add_one (k : SourceIndex 1831) :
    sourceDerivativeOrder1831 k + 1 =
      derivativeBernoulliIndex1831 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder1831, derivativeBernoulliIndex1831]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries1831
    (k n : SourceIndex 1831) :
    formalDerivativeAtZero (sourceDerivativeOrder1831 k)
        (logarithmicDerivative (integralDiagonalSeries1831 n)) =
      (characterCoefficientNat1831 k n : ℚ) *
        baseDerivativeFactor1831 k := by
  rw [integralDiagonalSeries1831,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      1831 4746 374 (sourceNumber n) (sourceDerivativeOrder1831 k)
      (by norm_num) (sourceDerivativeOrder1831_pos k)]
  have horder : sourceDerivativeOrder1831 k =
      2 * (sourceNumber k * 1831) - 1 := by
    simp [sourceDerivativeOrder1831, derivativeBernoulliIndex1831,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (4746 : ℚ) (sourceNumber k * 1831) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 1831) =
      derivativeBernoulliIndex1831 k := by
    simp [derivativeBernoulliIndex1831, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 1831) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 1831) - 1 + 1 =
      2 * (sourceNumber k * 1831) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 1831 : ℕ) =
      (derivativeBernoulliIndex1831 k : ℚ) := by
    rw [derivativeBernoulliIndex1831]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat1831, baseDerivativeFactor1831,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `1831²`. -/
theorem characterCoefficientNat1831_cast
    (k n : SourceIndex 1831) :
    (characterCoefficientNat1831 k n : ZMod (1831 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum1831 k n := by
  simp only [characterCoefficientNat1831,
    VandiverDiagonalArithmetic.positiveCharacterSum1831, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent1831,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex1831, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 1831) =
      2 * 1831 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `4342590`. -/
theorem characterCoefficientNat1831_sub_diagonal_dvd
    (k n : SourceIndex 1831) :
    ((1831 : ℤ) ^ 2) ∣
      (characterCoefficientNat1831 k n : ℤ) -
        (if k = n then 4342590 else 0) := by
  have hcast := characterCoefficientNat1831_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum1831_eq_4342590_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat1831 k n : ℤ) -
        (if k = n then 4342590 else 0) : ℤ) :
          ZMod (1831 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat1831 k n : ℤ) : ZMod (1831 ^ 2)) =
          if k = n then 4342590 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((1831 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat1831 k n : ℤ) -
        (if k = n then 4342590 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((1831 ^ 2 : ℕ) : ℤ) = (1831 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `1831`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient1831_isPIntegral (k : SourceIndex 1831) :
    IsPIntegral 1831
      (bernoulli (derivativeBernoulliIndex1831 k) /
        (derivativeBernoulliIndex1831 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj1828 : j ≤ 1828 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 1828
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 1831) (j := j) (by norm_num) hj2 hj1828 hjEven
  simpa [j, derivativeBernoulliIndex1831, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `1831`-integral. -/
theorem baseDerivativeFactor1831_hasPadicValAtLeast_zero
    (k : SourceIndex 1831) :
    HasPadicValAtLeast 1831 0 (baseDerivativeFactor1831 k) := by
  have hquotient : HasPadicValAtLeast 1831 0
      (bernoulli (derivativeBernoulliIndex1831 k) /
        (derivativeBernoulliIndex1831 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient1831_isPIntegral k)
  have hone : 1 ≤ 4746 ^ derivativeBernoulliIndex1831 k :=
    Nat.one_le_pow (derivativeBernoulliIndex1831 k) 4746 (by norm_num)
  have hrootCast :
      (4746 : ℚ) ^ derivativeBernoulliIndex1831 k - 1 =
        ((4746 ^ derivativeBernoulliIndex1831 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor1831, hrootCast]
  have hroot : HasPadicValAtLeast 1831 0
      (((4746 ^ derivativeBernoulliIndex1831 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 1830`. -/
def relationDerivative1831
    (a : SourceIndex 1831 → ℤ) (k : SourceIndex 1831) : ℚ :=
  ∑ n, ((1830 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder1831 k)
      (logarithmicDerivative (integralDiagonalSeries1831 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative1831_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 1831 → ℤ) (k : SourceIndex 1831) :
    HasPadicValAtLeast 1831 2
      (relationDerivative1831 a k -
        (a k : ℚ) * diagonalDerivativeFactor1831 k) := by
  classical
  let delta : SourceIndex 1831 → ℤ :=
    fun n ↦ if k = n then 4342590 else 0
  have hdeltaInt : (∑ n, a n * delta n) = 4342590 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (4342590 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor1831_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 1831) :
      HasPadicValAtLeast 1831 2
        ((((1830 * a n) *
            ((characterCoefficientNat1831 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor1831 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat1831_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat1831 k n : ℤ) - delta n =
        (1831 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (1830 * a n) *
            ((characterCoefficientNat1831 k n : ℤ) - delta n) =
          (1831 : ℤ) ^ 2 * (1830 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 1831) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 1831) (1830 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1
    all_goals norm_num [Int.cast_mul, Int.cast_pow]
    all_goals ring
  have hsum : HasPadicValAtLeast 1831 2
      (∑ n, ((((1830 * a n) *
          ((characterCoefficientNat1831 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor1831 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor1831 k =
      ((1830 : ℚ) * (4342590 : ℚ)) * baseDerivativeFactor1831 k := by
    simp only [diagonalDerivativeFactor1831, baseDerivativeFactor1831]
    ring
  have halgebra :
      relationDerivative1831 a k -
          (a k : ℚ) * diagonalDerivativeFactor1831 k =
        ∑ n, ((((1830 * a n) *
            ((characterCoefficientNat1831 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor1831 k) := by
    symm
    calc
      (∑ n, ((((1830 * a n) *
            ((characterCoefficientNat1831 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor1831 k)) =
          (∑ n, (((1830 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat1831 k n : ℚ) *
                baseDerivativeFactor1831 k) -
            (1830 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor1831 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((1830 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat1831 k n : ℚ) *
                baseDerivativeFactor1831 k)) -
            (1830 : ℚ) * baseDerivativeFactor1831 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative1831 a k -
          (a k : ℚ) * diagonalDerivativeFactor1831 k := by
        rw [hdeltaRat, hdiag, relationDerivative1831]
        simp_rw [formalDerivative_integralDiagonalSeries1831]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `1831²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 1831 → ℤ) (k : SourceIndex 1831)
    (hrelation : HasPadicValAtLeast 1831 2
      (relationDerivative1831 a k)) :
    PadicValAtLeast 1831 2
      ((a k : ℚ) * diagonalDerivativeFactor1831 k) := by
  have herr :=
    relationDerivative1831_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 1831 2
      ((a k : ℚ) * diagonalDerivativeFactor1831 k) := by
    have := hrelation.sub herr
    convert this using 1
    ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 1831 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 1831 2
      (relationDerivative1831 a k)) :
    ∀ k, (1831 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 1831 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalDerivative
