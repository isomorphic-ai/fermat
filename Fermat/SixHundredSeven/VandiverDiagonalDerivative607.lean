import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.SixHundredSeven.VandiverDerivativeValuation607

/-!
# Diagonal isolation in Vandiver's derivative calculation at 607

This module joins the exact formal-power-series calculation to the
algebraic `ZMod (607²)` character-sum certificate.  It proves that the
logarithmic derivative of an arbitrary exponent relation differs from its
single diagonal Bernoulli term by a rational of `607`-adic valuation at
least two.

The diagonal residue is the exact value `246339`.  After Vandiver's outer
factor `606`, the isolated rational coefficient is
the exact `149281434` used in `diagonalDerivativeFactor607`.
-/

namespace Fermat.SixHundredSeven.VandiverDiagonalDerivative

open PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.Voronoi
open Fermat.SixHundredSeven.VandiverDerivativeValuation

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

noncomputable section

/-- The `2*k*607 - 1` order of the logarithmic derivative series. -/
def sourceDerivativeOrder607 (k : SourceIndex 607) : ℕ :=
  derivativeBernoulliIndex607 k - 1

/-- Vandiver's positive integral diagonal polynomial series. -/
def integralDiagonalSeries607 (n : SourceIndex 607) : PowerSeries ℚ :=
  integralDiagonalExp 607 813 201 (sourceNumber n)

/-- The exact positive integer coefficient multiplying the common
Bernoulli derivative at row `k`, column `n`. -/
def characterCoefficientNat607 (k n : SourceIndex 607) : ℕ :=
  ∑ j ∈ Finset.range 303,
    integralDiagonalWeight 607 813 (sourceNumber n) j *
      (813 ^ j) ^ derivativeBernoulliIndex607 k

/-- The common Bernoulli factor in row `k`. -/
def baseDerivativeFactor607 (k : SourceIndex 607) : ℚ :=
  bernoulli (derivativeBernoulliIndex607 k) /
      (derivativeBernoulliIndex607 k : ℚ) *
    ((813 : ℚ) ^ derivativeBernoulliIndex607 k - 1)

theorem sourceDerivativeOrder607_pos (k : SourceIndex 607) :
    0 < sourceDerivativeOrder607 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder607, derivativeBernoulliIndex607]
  omega

theorem sourceDerivativeOrder607_add_one (k : SourceIndex 607) :
    sourceDerivativeOrder607 k + 1 =
      derivativeBernoulliIndex607 k := by
  have hs : 0 < sourceNumber k := by simp [sourceNumber]
  simp only [sourceDerivativeOrder607, derivativeBernoulliIndex607]
  omega

/-- Specialization of the generic exact character-sum derivative. -/
theorem formalDerivative_integralDiagonalSeries607
    (k n : SourceIndex 607) :
    formalDerivativeAtZero (sourceDerivativeOrder607 k)
        (logarithmicDerivative (integralDiagonalSeries607 n)) =
      (characterCoefficientNat607 k n : ℚ) *
        baseDerivativeFactor607 k := by
  rw [integralDiagonalSeries607,
    formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
      607 813 201 (sourceNumber n) (sourceDerivativeOrder607 k)
      (by norm_num) (sourceDerivativeOrder607_pos k)]
  have horder : sourceDerivativeOrder607 k =
      2 * (sourceNumber k * 607) - 1 := by
    simp [sourceDerivativeOrder607, derivativeBernoulliIndex607,
      Nat.mul_assoc]
  rw [horder]
  have hlog := even_formalDerivativeAtZero_vandiverLogDerivative
    (813 : ℚ) (sourceNumber k * 607) (by
      exact Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  rw [hlog]
  have hindex : 2 * (sourceNumber k * 607) =
      derivativeBernoulliIndex607 k := by
    simp [derivativeBernoulliIndex607, Nat.mul_assoc]
  have hpositive : 0 < 2 * (sourceNumber k * 607) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (by simp [sourceNumber]) (by norm_num))
  have hadd : 2 * (sourceNumber k * 607) - 1 + 1 =
      2 * (sourceNumber k * 607) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpositive.ne')
  have hdenom : (2 : ℚ) * (sourceNumber k * 607 : ℕ) =
      (derivativeBernoulliIndex607 k : ℚ) := by
    rw [derivativeBernoulliIndex607]
    push_cast
    ring
  rw [hadd, hindex, hdenom]
  simp only [characterCoefficientNat607, baseDerivativeFactor607,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

set_option maxHeartbeats 2000000 in
/-- The generic positive coefficient is exactly the finite character sum
already certified modulo `607²`. -/
theorem characterCoefficientNat607_cast
    (k n : SourceIndex 607) :
    (characterCoefficientNat607 k n : ZMod (607 ^ 2)) =
      VandiverDiagonalArithmetic.positiveCharacterSum607 k n := by
  simp only [characterCoefficientNat607,
    VandiverDiagonalArithmetic.positiveCharacterSum607, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, integralDiagonalWeight,
    VandiverDiagonalArithmetic.positiveCharacterExponent607,
    VandiverDiagonalArithmetic.sourceIndex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  simp only [derivativeBernoulliIndex607, sourceNumber]
  rw [show j * (2 * (k.val + 1) * 607) =
      2 * 607 * (k.val + 1) * j by ac_rfl]

/-- Integral diagonal congruence at the actual residue `246339`. -/
theorem characterCoefficientNat607_sub_diagonal_dvd
    (k n : SourceIndex 607) :
    ((607 : ℤ) ^ 2) ∣
      (characterCoefficientNat607 k n : ℤ) -
        (if k = n then 246339 else 0) := by
  have hcast := characterCoefficientNat607_cast k n
  rw [VandiverDiagonalArithmetic.positiveCharacterSum607_eq_246339_or_zero]
    at hcast
  have hzero :
      (((characterCoefficientNat607 k n : ℤ) -
        (if k = n then 246339 else 0) : ℤ) :
          ZMod (607 ^ 2)) = 0 := by
    rw [Int.cast_sub]
    have hcast' :
        ((characterCoefficientNat607 k n : ℤ) : ZMod (607 ^ 2)) =
          if k = n then 246339 else 0 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    split_ifs <;> ring
  have hdvd : (((607 ^ 2 : ℕ) : ℤ) ∣
      (characterCoefficientNat607 k n : ℤ) -
        (if k = n then 246339 else 0)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hmodulus : ((607 ^ 2 : ℕ) : ℤ) = (607 : ℤ) ^ 2 := by
    norm_num
  rwa [hmodulus] at hdvd

/-- Kummer's proved congruence supplies `607`-integrality of the common
high-Bernoulli quotient. -/
theorem baseBernoulliQuotient607_isPIntegral (k : SourceIndex 607) :
    IsPIntegral 607
      (bernoulli (derivativeBernoulliIndex607 k) /
        (derivativeBernoulliIndex607 k : ℚ)) := by
  let j := 2 * sourceNumber k
  have hj2 : 2 ≤ j := by simp [j, sourceNumber]
  have hj604 : j ≤ 604 := by
    have hk := k.isLt
    change 2 * (k.val + 1) ≤ 604
    omega
  have hjEven : Even j := even_two.mul_right (sourceNumber k)
  have h := KummerTheorem.kummerCongruenceModPrime_irregularRange
    (p := 607) (j := j) (by norm_num) hj2 hj604 hjEven
  simpa [j, derivativeBernoulliIndex607, Nat.mul_assoc] using h.2.1

/-- The entire common derivative factor is `607`-integral. -/
theorem baseDerivativeFactor607_hasPadicValAtLeast_zero
    (k : SourceIndex 607) :
    HasPadicValAtLeast 607 0 (baseDerivativeFactor607 k) := by
  have hquotient : HasPadicValAtLeast 607 0
      (bernoulli (derivativeBernoulliIndex607 k) /
        (derivativeBernoulliIndex607 k : ℚ)) :=
    Or.inr (baseBernoulliQuotient607_isPIntegral k)
  have hone : 1 ≤ 813 ^ derivativeBernoulliIndex607 k :=
    Nat.one_le_pow (derivativeBernoulliIndex607 k) 813 (by norm_num)
  have hrootCast :
      (813 : ℚ) ^ derivativeBernoulliIndex607 k - 1 =
        ((813 ^ derivativeBernoulliIndex607 k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  rw [baseDerivativeFactor607, hrootCast]
  have hroot : HasPadicValAtLeast 607 0
      (((813 ^ derivativeBernoulliIndex607 k - 1 : ℕ) : ℤ) : ℚ) :=
    HasPadicValAtLeast.intCast _
  convert hquotient.mul hroot using 1

/-- The exponent-weighted logarithmic derivative, including Vandiver's
outer factor `p - 1 = 606`. -/
def relationDerivative607
    (a : SourceIndex 607 → ℤ) (k : SourceIndex 607) : ℚ :=
  ∑ n, ((606 * a n : ℤ) : ℚ) *
    formalDerivativeAtZero (sourceDerivativeOrder607 k)
      (logarithmicDerivative (integralDiagonalSeries607 n))

/-- The total derivative differs from the isolated diagonal term by a
quantity of valuation at least two. -/
theorem relationDerivative607_sub_diagonal_hasPadicValAtLeast_two
    (a : SourceIndex 607 → ℤ) (k : SourceIndex 607) :
    HasPadicValAtLeast 607 2
      (relationDerivative607 a k -
        (a k : ℚ) * diagonalDerivativeFactor607 k) := by
  classical
  let delta : SourceIndex 607 → ℤ :=
    fun n ↦ if k = n then 246339 else 0
  have hdeltaInt : (∑ n, a n * delta n) = 246339 * a k := by
    rw [Finset.sum_eq_single k]
    · simp [delta]
      ring
    · intro n _ hnk
      simp [delta, Ne.symm hnk]
    · simp
  have hdeltaRat :
      (∑ n, (a n : ℚ) * (delta n : ℚ)) =
        (246339 : ℚ) * (a k : ℚ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℚ)) hdeltaInt
    push_cast at h
    exact h
  have hbase := baseDerivativeFactor607_hasPadicValAtLeast_zero k
  have hterm (n : SourceIndex 607) :
      HasPadicValAtLeast 607 2
        ((((606 * a n) *
            ((characterCoefficientNat607 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor607 k) := by
    obtain ⟨z, hz⟩ :=
      characterCoefficientNat607_sub_diagonal_dvd k n
    have hz' : (characterCoefficientNat607 k n : ℤ) - delta n =
        (607 : ℤ) ^ 2 * z := by
      simpa only [delta] using hz
    have hcoefficient :
        (606 * a n) *
            ((characterCoefficientNat607 k n : ℤ) - delta n) =
          (607 : ℤ) ^ 2 * (606 * a n * z) := by
      rw [hz']
      ring
    rw [hcoefficient]
    have hp := HasPadicValAtLeast.primePow (p := 607) 2
    have hzIntegral :=
      HasPadicValAtLeast.intCast (p := 607) (606 * a n * z)
    have hproduct := hp.mul (hzIntegral.mul hbase)
    convert hproduct using 1
    all_goals norm_num [Int.cast_mul, Int.cast_pow]
    all_goals ring
  have hsum : HasPadicValAtLeast 607 2
      (∑ n, ((((606 * a n) *
          ((characterCoefficientNat607 k n : ℤ) - delta n) : ℤ) : ℚ) *
        baseDerivativeFactor607 k)) := by
    apply HasPadicValAtLeast.sum
    intro n _
    exact hterm n
  have hdiag : diagonalDerivativeFactor607 k =
      ((606 : ℚ) * (246339 : ℚ)) * baseDerivativeFactor607 k := by
    simp only [diagonalDerivativeFactor607, baseDerivativeFactor607]
    ring
  have halgebra :
      relationDerivative607 a k -
          (a k : ℚ) * diagonalDerivativeFactor607 k =
        ∑ n, ((((606 * a n) *
            ((characterCoefficientNat607 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor607 k) := by
    symm
    calc
      (∑ n, ((((606 * a n) *
            ((characterCoefficientNat607 k n : ℤ) - delta n) : ℤ) : ℚ) *
          baseDerivativeFactor607 k)) =
          (∑ n, (((606 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat607 k n : ℚ) *
                baseDerivativeFactor607 k) -
            (606 : ℚ) * (a n : ℚ) * (delta n : ℚ) *
              baseDerivativeFactor607 k)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      _ = (∑ n, ((606 * a n : ℤ) : ℚ) *
              ((characterCoefficientNat607 k n : ℚ) *
                baseDerivativeFactor607 k)) -
            (606 : ℚ) * baseDerivativeFactor607 k *
              (∑ n, (a n : ℚ) * (delta n : ℚ)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = relationDerivative607 a k -
          (a k : ℚ) * diagonalDerivativeFactor607 k := by
        rw [hdeltaRat, hdiag, relationDerivative607]
        simp_rw [formalDerivative_integralDiagonalSeries607]
        ring
  rw [halgebra]
  exact hsum

/-- A relation derivative divisible by `607²` forces its diagonal term to
the same depth. -/
theorem diagonal_hasPadicValAtLeast_two_of_relation
    (a : SourceIndex 607 → ℤ) (k : SourceIndex 607)
    (hrelation : HasPadicValAtLeast 607 2
      (relationDerivative607 a k)) :
    PadicValAtLeast 607 2
      ((a k : ℚ) * diagonalDerivativeFactor607 k) := by
  have herr :=
    relationDerivative607_sub_diagonal_hasPadicValAtLeast_two a k
  have hdiag : HasPadicValAtLeast 607 2
      ((a k : ℚ) * diagonalDerivativeFactor607 k) := by
    have := hrelation.sub herr
    convert this using 1
    ring
  exact hdiag

/-- Source-shaped endpoint of the complete diagonal calculation. -/
theorem cubeCongruence_of_relationDerivative
    (a : SourceIndex 607 → ℤ)
    (hrelation : ∀ k, HasPadicValAtLeast 607 2
      (relationDerivative607 a k)) :
    ∀ k, (607 : ℤ) ^ 3 ∣
      a k * vandiverBernoulliNumerator 607 k := by
  intro k
  apply cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
  exact diagonal_hasPadicValAtLeast_two_of_relation a k (hrelation k)

end

end Fermat.SixHundredSeven.VandiverDiagonalDerivative
