import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic491

/-!
# The valuation step in Vandiver's diagonal calculation at 491

The finite diagonal sum leaves, at source index `k`, the rational factor

`-52823470 * B_(2*k*491) / (2*k*491) *
  (2512^(2*k*491) - 1)`.

The coefficient `-52823470 = 490 * (-107803)` is the exact integer
representative supplied by the positive diagonal character calculation.
It is a `491`-adic unit.  All factors except the displayed `491` in the
Bernoulli index and the Bernoulli numerator are likewise `491`-adic units.
Thus divisibility of this rational by `491²` is exactly divisibility of the
relation exponent times the Bernoulli numerator by `491³`.
-/

namespace Fermat.FourHundredNinetyOne.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex491 (k : SourceIndex 491) : ℕ :=
  (2 * sourceNumber k) * 491

/-- The complete diagonal coefficient after Vandiver's outer factor
`p - 1` and the positive character sum have been included. -/
def diagonalDerivativeFactor491 (k : SourceIndex 491) : ℚ :=
  (-52823470 : ℚ) *
    (bernoulli (derivativeBernoulliIndex491 k) /
      (derivativeBernoulliIndex491 k : ℚ)) *
    ((2512 : ℚ) ^ derivativeBernoulliIndex491 k - 1)

theorem derivativeBernoulliIndex491_even (k : SourceIndex 491) :
    Even (derivativeBernoulliIndex491 k) := by
  rw [derivativeBernoulliIndex491, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 491)

theorem fourHundredNinety_not_dvd_derivativeBernoulliIndex491
    (k : SourceIndex 491) :
    ¬490 ∣ derivativeBernoulliIndex491 k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 244 := by
    simp [sourceNumber]
  simp only [derivativeBernoulliIndex491] at hq
  omega

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo491 (k : SourceIndex 491) :
    DenominatorPrimeTo 491 (bernoulli (derivativeBernoulliIndex491 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex491_even k)
    (fourHundredNinety_not_dvd_derivativeBernoulliIndex491 k)

theorem fourHundredNinetyOne_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 491) :
    ¬491 ∣ 2 * sourceNumber k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 244 := by
    simp [sourceNumber]
  omega

theorem fourHundredNinetyOne_not_dvd_rootFactor491
    (k : SourceIndex 491) :
    ¬491 ∣ 2512 ^ derivativeBernoulliIndex491 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 2512 ^ derivativeBernoulliIndex491 k :=
    Nat.one_le_pow (derivativeBernoulliIndex491 k) 2512 (by norm_num)
  have hmod : 1 ≡ 2512 ^ derivativeBernoulliIndex491 k [MOD 491] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((2512 ^ derivativeBernoulliIndex491 k : ℕ) : ZMod 491) =
        ((1 : ℕ) : ZMod 491) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (2512 : ZMod 491) ^ derivativeBernoulliIndex491 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply fourHundredNinety_not_dvd_derivativeBernoulliIndex491 k
  have hprimitive :=
    VandiverDiagonalArithmetic.teichmullerRoot491_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [VandiverDiagonalArithmetic.teichmullerRoot491] using hpow

private theorem diagonalDerivativeFactor491_ne_zero
    (k : SourceIndex 491)
    (hB : bernoulli (derivativeBernoulliIndex491 k) ≠ 0) :
    diagonalDerivativeFactor491 k ≠ 0 := by
  unfold diagonalDerivativeFactor491
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 2512 ^ derivativeBernoulliIndex491 k ≠ 1 := by
      intro hone
      apply fourHundredNinetyOne_not_dvd_rootFactor491 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor491
    (k : SourceIndex 491) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex491 k) ≠ 0) :
    padicValRat 491 ((a : ℚ) * diagonalDerivativeFactor491 k) =
      padicValInt 491
          (a * (bernoulli (derivativeBernoulliIndex491 k)).num) - 1 := by
  let N := derivativeBernoulliIndex491 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex491]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 2512 ^ N - 1 ≠ 0 := by
    intro hzero
    apply fourHundredNinetyOne_not_dvd_rootFactor491 k
    simpa [N] using hzero ▸ dvd_zero 491
  have hroot : (2512 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 2512 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 491 N = 1 := by
    dsimp [N, derivativeBernoulliIndex491]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (fourHundredNinetyOne_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 491 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 2512 ^ N :=
    Nat.one_le_pow N 2512 (by norm_num)
  have hrootCast :
      (2512 : ℚ) ^ N - 1 = ((2512 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 491 ((2512 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using fourHundredNinetyOne_not_dvd_rootFactor491 k
  have hcoefficientVal : padicValRat 491 (-52823470 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 491 B =
      padicValInt 491 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo491 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 491
      ((a : ℚ) * (((-52823470 : ℚ) * (B / (N : ℚ))) *
        ((2512 : ℚ) ^ N - 1))) =
    padicValInt 491 (a * B.num) - 1
  rw [padicValRat.mul (Int.cast_ne_zero.mpr ha)
      (mul_ne_zero (mul_ne_zero (by norm_num) hquotient) hroot),
    padicValRat.mul (mul_ne_zero (by norm_num) hquotient) hroot,
    padicValRat.mul (by norm_num) hquotient,
    padicValRat.div hB hN,
    padicValRat.of_int, hcoefficientVal, hBval, hNval, hrootVal,
    padicValInt.mul ha hBnum]
  push_cast
  ring

/-- Vandiver's last valuation implication: a diagonal logarithmic
derivative divisible by `491²` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 491) (a : ℤ)
    (hderivative : PadicValAtLeast 491 2
      ((a : ℚ) * diagonalDerivativeFactor491 k)) :
    (491 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 491 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex491 k) = 0
  · change (491 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex491 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor491 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor491_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 491 ((a : ℚ) * diagonalDerivativeFactor491 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor491 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 491
      (a * (bernoulli (derivativeBernoulliIndex491 k)).num) := by
    omega
  change (491 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex491 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex491 k)).num)).2
      (Or.inr hthree)

end Fermat.FourHundredNinetyOne.VandiverDerivativeValuation
