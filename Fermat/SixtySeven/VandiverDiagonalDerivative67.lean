import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.SixtySeven.VandiverDerivativeValuation67

/-!
# Diagonal isolation in Vandiver's derivative calculation at 67

This module joins the exact formal-power-series calculation to the finite
`ZMod (67^2)` character-sum certificate.  It proves that the logarithmic
derivative of an arbitrary exponent relation differs from its single
diagonal Bernoulli term by a rational of `67`-adic valuation at least two.

The only downstream input still needed is the source's polynomial-remainder
argument asserting that the derivative of the whole relation also has
valuation at least two.
-/

namespace Fermat.SixtySeven.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.SixtySeven.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*67 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder67 (k : SourceIndex 67) : ℕ :=
  derivativeBernoulliIndex67 k - 1

/-- Vandiver's positive integral diagonal polynomial series at source
index `n`. -/
def integralDiagonalSeries67 (n : SourceIndex 67) : PowerSeries ℚ :=
  integralDiagonalExp 67 1342 33 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat67 (k n : SourceIndex 67) : ℕ :=
  ∑ j ∈ Finset.range 33,
    integralDiagonalWeight 67 1342 (sourceNumber n) j *
      (1342 ^ j) ^ derivativeBernoulliIndex67 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor67 (k : SourceIndex 67) : ℚ :=
  bernoulli (derivativeBernoulliIndex67 k) /
      (derivativeBernoulliIndex67 k : ℚ) *
    ((1342 : ℚ) ^ derivativeBernoulliIndex67 k - 1)

theorem sourceDerivativeOrder67_pos (k : SourceIndex 67) :
    0 < sourceDerivativeOrder67 k := by
  fin_cases k <;>
    norm_num [sourceDerivativeOrder67, derivativeBernoulliIndex67, sourceNumber]

theorem sourceDerivativeOrder67_add_one (k : SourceIndex 67) :
    sourceDerivativeOrder67 k + 1 = derivativeBernoulliIndex67 k := by
  fin_cases k <;>
    norm_num [sourceDerivativeOrder67, derivativeBernoulliIndex67, sourceNumber]

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries67
    (k n : SourceIndex 67) :
    formalDerivativeAtZero (sourceDerivativeOrder67 k)
        (logarithmicDerivative (integralDiagonalSeries67 n)) =
      (characterCoefficientNat67 k n : ℚ) *
        baseDerivativeFactor67 k := by
  rw [integralDiagonalSeries67,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      67 1342 33 (sourceNumber n) (sourceDerivativeOrder67 k)
      (by norm_num) (sourceDerivativeOrder67_pos k)]
  have horder : sourceDerivativeOrder67 k =
      2 * (sourceNumber k * 67) - 1 := by
    simp [sourceDerivativeOrder67, derivativeBernoulliIndex67,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (1342 : ℚ) (sourceNumber k * 67) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 67) =
      derivativeBernoulliIndex67 k := by
    simp [derivativeBernoulliIndex67, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 67) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 67) - 1 + 1 =
      2 * (sourceNumber k * 67) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 67 : ℕ) =
      (derivativeBernoulliIndex67 k : ℚ) := by
    rw [derivativeBernoulliIndex67]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat67, baseDerivativeFactor67,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `67^2`. -/
theorem characterCoefficientNat67_cast
    (k n : SourceIndex 67) :
    (characterCoefficientNat67 k n : ZMod (67 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum67 k n := by
  simp only [characterCoefficientNat67,
    VandiverDiagonalArithmetic.positiveCharacterSum67, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent67,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex67, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 67) =
      2 * 67 * (k.val + 1) * j by ac_rfl]

/-- Integral form of the diagonal congruence: the coefficient is `-604`
modulo `67^2` on the diagonal and zero off it. -/
theorem characterCoefficientNat67_sub_diagonal_dvd
    (k n : SourceIndex 67) :
    ((67 : ℤ) ^ 2) ∣
      (characterCoefficientNat67 k n : ℤ) -
        (if k = n then -604 else 0) := by
  have hcast := characterCoefficientNat67_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum67_eq_neg604_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat67 k n : ℤ) -
        (if k = n then -604 else 0) : ℤ) : ZMod (67 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat67 k n : ℤ) : ZMod (67 ^ 2)) =
          if k = n then -604 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((67 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat67 k n : ℤ) -
        (if k = n then -604 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((67 ^ 2 : ℕ) : ℤ) = (67 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `67`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient67_isPIntegral (k : SourceIndex 67) :
    IsPIntegral 67
      (bernoulli (derivativeBernoulliIndex67 k) /
        (derivativeBernoulliIndex67 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj64 : j ≤ 64 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 64
    norm_num at hk
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 67) (j := j) (by norm_num) hj2 hj64 hjEven
  simpa [j, derivativeBernoulliIndex67, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `67`-integral; the root factor
is a `67`-adic unit. -/
theorem baseDerivativeFactor67_hasPadicValAtLeast_zero
    (k : SourceIndex 67) :
    HasPadicValAtLeast 67 0 (baseDerivativeFactor67 k) := by
  have hquotient : HasPadicValAtLeast 67 0
      (bernoulli (derivativeBernoulliIndex67 k) /
        (derivativeBernoulliIndex67 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient67_isPIntegral k)
  have hone : 1 ≤ 1342 ^ derivativeBernoulliIndex67 k :=
    Nat.one_le_pow (derivativeBernoulliIndex67 k) 1342 (by norm_num)
  have hrootCast :
      (1342 : ℚ) ^ derivativeBernoulliIndex67 k - 1 =
        ((1342 ^ derivativeBernoulliIndex67 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor67, hrootCast]
  have hroot : HasPadicValAtLeast 67 0
      (((1342 ^ derivativeBernoulliIndex67 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1 <;> norm_num

/-- The exponent-weighted logarithmic derivative of the left side of
Vandiver's polynomial identity, including the source's outer factor
`p - 1 = 66`. -/
def relationDerivative67
    (a : SourceIndex 67 → ℤ) (k : SourceIndex 67) : ℚ :=
  ∑ n, ((66 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder67 k)
      (logarithmicDerivative (integralDiagonalSeries67 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative67_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 67 → ℤ) (k : SourceIndex 67) :
    HasPadicValAtLeast 67 2
      (relationDerivative67 a k -
        (a k : ℚ) * diagonalDerivativeFactor67 k) := by
  classical
  let delta : SourceIndex 67 → ℤ :=
    fun n ↦ if k = n then -604 else 0
  have hdeltaInt : (∑ n, a n * delta n) = -604 * a k := by
    rw [Finset.sum_eq_single k]
    · simp only [delta, ↓reduceIte, mul_neg]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (-604 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor67_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 67) :
      HasPadicValAtLeast 67 2
        ((((66 * a n) *
            ((characterCoefficientNat67 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor67 k) := by
    obtain ⟨z, hz⟩ := characterCoefficientNat67_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat67 k n : ℤ) - delta n =
        (67 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (66 * a n) *
            ((characterCoefficientNat67 k n : ℤ) - delta n) =
          (67 : ℤ) ^ 2 * (66 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 67) 2
    have hzIntegral := HasPadicValAtLeast.intCast (p := 67) (66 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1 <;>
      norm_num [Int.cast_mul, Int.cast_pow] <;> ring
  have hsum : HasPadicValAtLeast 67 2
      (∑ n, ((((66 * a n) *
          ((characterCoefficientNat67 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor67 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor67 k =
      (-39864 : ℚ) * baseDerivativeFactor67 k := by
    simp only [diagonalDerivativeFactor67, baseDerivativeFactor67]
    ring
  have halgebra :
      relationDerivative67 a k -
          (a k : ℚ) * diagonalDerivativeFactor67 k =
        ∑ n, ((((66 * a n) *
            ((characterCoefficientNat67 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor67 k) := by
    symm
    calc
      (∑ n, ((((66 * a n) *
            ((characterCoefficientNat67 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor67 k)) =
          (∑ n, (((66 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat67 k n : ℚ) *
                baseDerivativeFactor67 k) -
            (66 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor67 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((66 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat67 k n : ℚ) *
                baseDerivativeFactor67 k)) -
            (66 : ℚ) * baseDerivativeFactor67 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative67 a k -
          (a k : ℚ) * diagonalDerivativeFactor67 k := by
        rw [hdeltaRat, hdiag, relationDerivative67]
        simp_rw [formalDerivative_integralDiagonalSeries67]
        ring
  rw [halgebra]
  exact hsum

/-- Once the polynomial-remainder side says that the total relation
derivative is divisible by `67^2`, the diagonal term is too. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 67 → ℤ) (k : SourceIndex 67)
    (hrelation : HasPadicValAtLeast 67 2 (relationDerivative67 a k)) :
    PadicValAtLeast 67 2
      ((a k : ℚ) * diagonalDerivativeFactor67 k) := by
  have herr :=
    relationDerivative67_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 67 2
      ((a k : ℚ) * diagonalDerivativeFactor67 k) := by
    have := hrelation.sub herr
    convert this using 1 <;> ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 67 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 67 2
      (relationDerivative67 a k)) :
    ∀ k, (67 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 67 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.SixtySeven.VandiverDiagonalDerivative
