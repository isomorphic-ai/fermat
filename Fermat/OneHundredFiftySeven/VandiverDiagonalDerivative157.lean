import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.OneHundredFiftySeven.VandiverDerivativeValuation157

/-!
# Diagonal isolation in Vandiver's derivative calculation at 157

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (157²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `157`-adic valuation at
least two.

The diagonal residue is `-7021`, not the exponent-37 coincidence `-1`.
After Vandiver's outer factor `156`, the isolated rational coefficient is
the exact `-1095276` used in `diagonalDerivativeFactor157`.
-/

namespace Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.OneHundredFiftySeven.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*157 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder157 (k : SourceIndex 157) : ℕ :=
  derivativeBernoulliIndex157 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries157 (n : SourceIndex 157) : PowerSeries ℚ :=
  integralDiagonalExp 157 226 78 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat157 (k n : SourceIndex 157) : ℕ :=
  ∑ j ∈ Finset.range 78,
    integralDiagonalWeight 157 226 (sourceNumber n) j *
      (226 ^ j) ^ derivativeBernoulliIndex157 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor157 (k : SourceIndex 157) : ℚ :=
  bernoulli (derivativeBernoulliIndex157 k) /
      (derivativeBernoulliIndex157 k : ℚ) *
    ((226 : ℚ) ^ derivativeBernoulliIndex157 k - 1)

theorem sourceDerivativeOrder157_pos (k : SourceIndex 157) :
    0 < sourceDerivativeOrder157 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder157, derivativeBernoulliIndex157]
  omega

theorem sourceDerivativeOrder157_add_one (k : SourceIndex 157) :
    sourceDerivativeOrder157 k + 1 =
      derivativeBernoulliIndex157 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder157, derivativeBernoulliIndex157]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries157
    (k n : SourceIndex 157) :
    formalDerivativeAtZero (sourceDerivativeOrder157 k)
        (logarithmicDerivative (integralDiagonalSeries157 n)) =
      (characterCoefficientNat157 k n : ℚ) *
        baseDerivativeFactor157 k := by
  rw [integralDiagonalSeries157,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      157 226 78 (sourceNumber n) (sourceDerivativeOrder157 k)
      (by norm_num) (sourceDerivativeOrder157_pos k)]
  have horder : sourceDerivativeOrder157 k =
      2 * (sourceNumber k * 157) - 1 := by
    simp [sourceDerivativeOrder157, derivativeBernoulliIndex157,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (226 : ℚ) (sourceNumber k * 157) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 157) =
      derivativeBernoulliIndex157 k := by
    simp [derivativeBernoulliIndex157, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 157) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 157) - 1 + 1 =
      2 * (sourceNumber k * 157) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 157 : ℕ) =
      (derivativeBernoulliIndex157 k : ℚ) := by
    rw [derivativeBernoulliIndex157]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat157, baseDerivativeFactor157,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `157²`. -/
theorem characterCoefficientNat157_cast
    (k n : SourceIndex 157) :
    (characterCoefficientNat157 k n : ZMod (157 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum157 k n := by
  simp only [characterCoefficientNat157,
    VandiverDiagonalArithmetic.positiveCharacterSum157, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent157,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex157, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 157) =
      2 * 157 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `-7021`. -/
theorem characterCoefficientNat157_sub_diagonal_dvd
    (k n : SourceIndex 157) :
    ((157 : ℤ) ^ 2) ∣
      (characterCoefficientNat157 k n : ℤ) -
        (if k = n then -7021 else 0) := by
  have hcast := characterCoefficientNat157_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum157_eq_neg7021_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat157 k n : ℤ) -
        (if k = n then -7021 else 0) : ℤ) :
          ZMod (157 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat157 k n : ℤ) : ZMod (157 ^ 2)) =
          if k = n then -7021 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((157 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat157 k n : ℤ) -
        (if k = n then -7021 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((157 ^ 2 : ℕ) : ℤ) = (157 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `157`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient157_isPIntegral (k : SourceIndex 157) :
    IsPIntegral 157
      (bernoulli (derivativeBernoulliIndex157 k) /
        (derivativeBernoulliIndex157 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj154 : j ≤ 154 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 154
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 157) (j := j) (by norm_num) hj2 hj154 hjEven
  simpa [j, derivativeBernoulliIndex157, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `157`-integral. -/
theorem baseDerivativeFactor157_hasPadicValAtLeast_zero
    (k : SourceIndex 157) :
    HasPadicValAtLeast 157 0 (baseDerivativeFactor157 k) := by
  have hquotient : HasPadicValAtLeast 157 0
      (bernoulli (derivativeBernoulliIndex157 k) /
        (derivativeBernoulliIndex157 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient157_isPIntegral k)
  have hone : 1 ≤ 226 ^ derivativeBernoulliIndex157 k :=
    Nat.one_le_pow (derivativeBernoulliIndex157 k) 226 (by norm_num)
  have hrootCast :
      (226 : ℚ) ^ derivativeBernoulliIndex157 k - 1 =
        ((226 ^ derivativeBernoulliIndex157 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor157, hrootCast]
  have hroot : HasPadicValAtLeast 157 0
      (((226 ^ derivativeBernoulliIndex157 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 156`. -/
def relationDerivative157
    (a : SourceIndex 157 → ℤ) (k : SourceIndex 157) : ℚ :=
  ∑ n, ((156 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder157 k)
      (logarithmicDerivative (integralDiagonalSeries157 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative157_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 157 → ℤ) (k : SourceIndex 157) :
    HasPadicValAtLeast 157 2
      (relationDerivative157 a k -
        (a k : ℚ) * diagonalDerivativeFactor157 k) := by
  classical
  let delta : SourceIndex 157 → ℤ :=
    fun n ↦ if k = n then -7021 else 0
  have hdeltaInt : (∑ n, a n * delta n) = -7021 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (-7021 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor157_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 157) :
      HasPadicValAtLeast 157 2
        ((((156 * a n) *
            ((characterCoefficientNat157 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor157 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat157_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat157 k n : ℤ) - delta n =
        (157 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (156 * a n) *
            ((characterCoefficientNat157 k n : ℤ) - delta n) =
          (157 : ℤ) ^ 2 * (156 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 157) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 157) (156 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 157 2
      (∑ n, ((((156 * a n) *
          ((characterCoefficientNat157 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor157 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor157 k =
      ((156 : ℚ) * (-7021 : ℚ)) * baseDerivativeFactor157 k := by
    simp only [diagonalDerivativeFactor157, baseDerivativeFactor157]
    ring
  have halgebra :
      relationDerivative157 a k -
          (a k : ℚ) * diagonalDerivativeFactor157 k =
        ∑ n, ((((156 * a n) *
            ((characterCoefficientNat157 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor157 k) := by
    symm
    calc
      (∑ n, ((((156 * a n) *
            ((characterCoefficientNat157 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor157 k)) =
          (∑ n, (((156 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat157 k n : ℚ) *
                baseDerivativeFactor157 k) -
            (156 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor157 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((156 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat157 k n : ℚ) *
                baseDerivativeFactor157 k)) -
            (156 : ℚ) * baseDerivativeFactor157 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative157 a k -
          (a k : ℚ) * diagonalDerivativeFactor157 k := by
        rw [hdeltaRat, hdiag, relationDerivative157]
        simp_rw [formalDerivative_integralDiagonalSeries157]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `157²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 157 → ℤ) (k : SourceIndex 157)
    (hrelation : HasPadicValAtLeast 157 2
      (relationDerivative157 a k)) :
    PadicValAtLeast 157 2
      ((a k : ℚ) * diagonalDerivativeFactor157 k) := by
  have herr :=
    relationDerivative157_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 157 2
      ((a k : ℚ) * diagonalDerivativeFactor157 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 157 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 157 2
      (relationDerivative157 a k)) :
    ∀ k, (157 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 157 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative
