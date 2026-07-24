import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.SixHundredNinetyOne.VandiverDerivativeValuation691

/-!
# Diagonal isolation in Vandiver's derivative calculation at 691

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (691²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `691`-adic valuation at
least two.

The diagonal residue is `-200449`, not the exponent-37 coincidence `-1`.
After Vandiver's outer factor `690`, the isolated rational coefficient is
the exact `-138309810` used in `diagonalDerivativeFactor691`.
-/

namespace Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.SixHundredNinetyOne.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*691 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder691 (k : SourceIndex 691) : ℕ :=
  derivativeBernoulliIndex691 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries691 (n : SourceIndex 691) : PowerSeries ℚ :=
  integralDiagonalExp 691 4955 287 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat691 (k n : SourceIndex 691) : ℕ :=
  ∑ j ∈ Finset.range 345,
    integralDiagonalWeight 691 4955 (sourceNumber n) j *
      (4955 ^ j) ^ derivativeBernoulliIndex691 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor691 (k : SourceIndex 691) : ℚ :=
  bernoulli (derivativeBernoulliIndex691 k) /
      (derivativeBernoulliIndex691 k : ℚ) *
    ((4955 : ℚ) ^ derivativeBernoulliIndex691 k - 1)

theorem sourceDerivativeOrder691_pos (k : SourceIndex 691) :
    0 < sourceDerivativeOrder691 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder691, derivativeBernoulliIndex691]
  omega

theorem sourceDerivativeOrder691_add_one (k : SourceIndex 691) :
    sourceDerivativeOrder691 k + 1 =
      derivativeBernoulliIndex691 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder691, derivativeBernoulliIndex691]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries691
    (k n : SourceIndex 691) :
    formalDerivativeAtZero (sourceDerivativeOrder691 k)
        (logarithmicDerivative (integralDiagonalSeries691 n)) =
      (characterCoefficientNat691 k n : ℚ) *
        baseDerivativeFactor691 k := by
  rw [integralDiagonalSeries691,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      691 4955 287 (sourceNumber n) (sourceDerivativeOrder691 k)
      (by norm_num) (sourceDerivativeOrder691_pos k)]
  have horder : sourceDerivativeOrder691 k =
      2 * (sourceNumber k * 691) - 1 := by
    simp [sourceDerivativeOrder691, derivativeBernoulliIndex691,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (4955 : ℚ) (sourceNumber k * 691) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 691) =
      derivativeBernoulliIndex691 k := by
    simp [derivativeBernoulliIndex691, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 691) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 691) - 1 + 1 =
      2 * (sourceNumber k * 691) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 691 : ℕ) =
      (derivativeBernoulliIndex691 k : ℚ) := by
    rw [derivativeBernoulliIndex691]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat691, baseDerivativeFactor691,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `691²`. -/
theorem characterCoefficientNat691_cast
    (k n : SourceIndex 691) :
    (characterCoefficientNat691 k n : ZMod (691 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum691 k n := by
  simp only [characterCoefficientNat691,
    VandiverDiagonalArithmetic.positiveCharacterSum691, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent691,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex691, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 691) =
      2 * 691 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `-200449`. -/
theorem characterCoefficientNat691_sub_diagonal_dvd
    (k n : SourceIndex 691) :
    ((691 : ℤ) ^ 2) ∣
      (characterCoefficientNat691 k n : ℤ) -
        (if k = n then -200449 else 0) := by
  have hcast := characterCoefficientNat691_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum691_eq_neg200449_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat691 k n : ℤ) -
        (if k = n then -200449 else 0) : ℤ) :
          ZMod (691 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat691 k n : ℤ) : ZMod (691 ^ 2)) =
          if k = n then -200449 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((691 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat691 k n : ℤ) -
        (if k = n then -200449 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((691 ^ 2 : ℕ) : ℤ) = (691 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `691`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient691_isPIntegral (k : SourceIndex 691) :
    IsPIntegral 691
      (bernoulli (derivativeBernoulliIndex691 k) /
        (derivativeBernoulliIndex691 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj688 : j ≤ 688 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 688
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 691) (j := j) (by norm_num) hj2 hj688 hjEven
  simpa [j, derivativeBernoulliIndex691, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `691`-integral. -/
theorem baseDerivativeFactor691_hasPadicValAtLeast_zero
    (k : SourceIndex 691) :
    HasPadicValAtLeast 691 0 (baseDerivativeFactor691 k) := by
  have hquotient : HasPadicValAtLeast 691 0
      (bernoulli (derivativeBernoulliIndex691 k) /
        (derivativeBernoulliIndex691 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient691_isPIntegral k)
  have hone : 1 ≤ 4955 ^ derivativeBernoulliIndex691 k :=
    Nat.one_le_pow (derivativeBernoulliIndex691 k) 4955 (by norm_num)
  have hrootCast :
      (4955 : ℚ) ^ derivativeBernoulliIndex691 k - 1 =
        ((4955 ^ derivativeBernoulliIndex691 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor691, hrootCast]
  have hroot : HasPadicValAtLeast 691 0
      (((4955 ^ derivativeBernoulliIndex691 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 690`. -/
def relationDerivative691
    (a : SourceIndex 691 → ℤ) (k : SourceIndex 691) : ℚ :=
  ∑ n, ((690 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder691 k)
      (logarithmicDerivative (integralDiagonalSeries691 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative691_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 691 → ℤ) (k : SourceIndex 691) :
    HasPadicValAtLeast 691 2
      (relationDerivative691 a k -
        (a k : ℚ) * diagonalDerivativeFactor691 k) := by
  classical
  let delta : SourceIndex 691 → ℤ :=
    fun n ↦ if k = n then -200449 else 0
  have hdeltaInt : (∑ n, a n * delta n) = -200449 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (-200449 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor691_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 691) :
      HasPadicValAtLeast 691 2
        ((((690 * a n) *
            ((characterCoefficientNat691 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor691 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat691_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat691 k n : ℤ) - delta n =
        (691 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (690 * a n) *
            ((characterCoefficientNat691 k n : ℤ) - delta n) =
          (691 : ℤ) ^ 2 * (690 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 691) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 691) (690 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 691 2
      (∑ n, ((((690 * a n) *
          ((characterCoefficientNat691 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor691 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor691 k =
      ((690 : ℚ) * (-200449 : ℚ)) * baseDerivativeFactor691 k := by
    simp only [diagonalDerivativeFactor691, baseDerivativeFactor691]
    ring
  have halgebra :
      relationDerivative691 a k -
          (a k : ℚ) * diagonalDerivativeFactor691 k =
        ∑ n, ((((690 * a n) *
            ((characterCoefficientNat691 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor691 k) := by
    symm
    calc
      (∑ n, ((((690 * a n) *
            ((characterCoefficientNat691 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor691 k)) =
          (∑ n, (((690 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat691 k n : ℚ) *
                baseDerivativeFactor691 k) -
            (690 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor691 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((690 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat691 k n : ℚ) *
                baseDerivativeFactor691 k)) -
            (690 : ℚ) * baseDerivativeFactor691 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative691 a k -
          (a k : ℚ) * diagonalDerivativeFactor691 k := by
        rw [hdeltaRat, hdiag, relationDerivative691]
        simp_rw [formalDerivative_integralDiagonalSeries691]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `691²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 691 → ℤ) (k : SourceIndex 691)
    (hrelation : HasPadicValAtLeast 691 2
      (relationDerivative691 a k)) :
    PadicValAtLeast 691 2
      ((a k : ℚ) * diagonalDerivativeFactor691 k) := by
  have herr :=
    relationDerivative691_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 691 2
      ((a k : ℚ) * diagonalDerivativeFactor691 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 691 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 691 2
      (relationDerivative691 a k)) :
    ∀ k, (691 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 691 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative
