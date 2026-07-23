import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.FiftyNine.VandiverDiagonalArithmetic

/-!
# The valuation step in Vandiver's diagonal calculation at 59

The finite diagonal sum leaves, at source index `k`, the rational factor

`355 * B_(2*k*59) / (2*k*59) * (946^(2*k*59) - 1)`.

All factors except the displayed `59` in the denominator and the Bernoulli
numerator are `59`-adic units.  Consequently divisibility of this rational
by `59^2` is exactly divisibility of the exponent times the Bernoulli
numerator by `59^3`.
-/

namespace Fermat.FiftyNine.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex59 (k : SourceIndex 59) : ℕ :=
  (2 * sourceNumber k) * 59

/-- The diagonal coefficient remaining after Vandiver's outer factor
`p - 1` and the positive integral character sum have been included. -/
def diagonalDerivativeFactor59 (k : SourceIndex 59) : ℚ :=
  (355 : ℚ) *
    (bernoulli (derivativeBernoulliIndex59 k) /
      (derivativeBernoulliIndex59 k : ℚ)) *
    ((946 : ℚ) ^ derivativeBernoulliIndex59 k - 1)

theorem derivativeBernoulliIndex59_even (k : SourceIndex 59) :
    Even (derivativeBernoulliIndex59 k) := by
  rw [derivativeBernoulliIndex59, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 59)

theorem fiftyEight_not_dvd_derivativeBernoulliIndex59
    (k : SourceIndex 59) :
    ¬58 ∣ derivativeBernoulliIndex59 k := by
  fin_cases k <;> norm_num [derivativeBernoulliIndex59, sourceNumber]

/-- Von Staudt--Clausen supplies the required denominator control. -/
theorem bernoulli_denominatorPrimeTo59 (k : SourceIndex 59) :
    DenominatorPrimeTo 59 (bernoulli (derivativeBernoulliIndex59 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex59_even k)
    (fiftyEight_not_dvd_derivativeBernoulliIndex59 k)

theorem fiftyNine_not_dvd_two_mul_sourceNumber (k : SourceIndex 59) :
    ¬59 ∣ 2 * sourceNumber k := by
  fin_cases k <;> norm_num [sourceNumber]

theorem fiftyNine_not_dvd_rootFactor59 (k : SourceIndex 59) :
    ¬59 ∣ 946 ^ derivativeBernoulliIndex59 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 946 ^ derivativeBernoulliIndex59 k :=
    Nat.one_le_pow (derivativeBernoulliIndex59 k) 946 (by norm_num)
  have hmod : 1 ≡ 946 ^ derivativeBernoulliIndex59 k [MOD 59] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((946 ^ derivativeBernoulliIndex59 k : ℕ) : ZMod 59) =
        ((1 : ℕ) : ZMod 59) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (946 : ZMod 59) ^ derivativeBernoulliIndex59 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply fiftyEight_not_dvd_derivativeBernoulliIndex59 k
  have hprimitive :=
    VandiverDiagonalArithmetic.teichmullerRoot59_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [VandiverDiagonalArithmetic.teichmullerRoot59] using hpow

private theorem diagonalDerivativeFactor59_ne_zero
    (k : SourceIndex 59)
    (hB : bernoulli (derivativeBernoulliIndex59 k) ≠ 0) :
    diagonalDerivativeFactor59 k ≠ 0 := by
  unfold diagonalDerivativeFactor59
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 946 ^ derivativeBernoulliIndex59 k ≠ 1 := by
      intro hone
      apply fiftyNine_not_dvd_rootFactor59 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor59
    (k : SourceIndex 59) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex59 k) ≠ 0) :
    padicValRat 59 ((a : ℚ) * diagonalDerivativeFactor59 k) =
      padicValInt 59
          (a * (bernoulli (derivativeBernoulliIndex59 k)).num) - 1 := by
  let N := derivativeBernoulliIndex59 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex59]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 946 ^ N - 1 ≠ 0 := by
    intro hzero
    apply fiftyNine_not_dvd_rootFactor59 k
    simpa [N] using hzero ▸ dvd_zero 59
  have hroot : (946 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 946 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 59 N = 1 := by
    dsimp [N, derivativeBernoulliIndex59]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (fiftyNine_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 59 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 946 ^ N :=
    Nat.one_le_pow N 946 (by norm_num)
  have hrootCast :
      (946 : ℚ) ^ N - 1 = ((946 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 59 ((946 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using fiftyNine_not_dvd_rootFactor59 k
  have hcoefficientVal : padicValRat 59 (355 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 59 B =
      padicValInt 59 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo59 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 59
      ((a : ℚ) * (((355 : ℚ) * (B / (N : ℚ))) *
        ((946 : ℚ) ^ N - 1))) =
    padicValInt 59 (a * B.num) - 1
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
derivative divisible by `59^2` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 59) (a : ℤ)
    (hderivative : PadicValAtLeast 59 2
      ((a : ℚ) * diagonalDerivativeFactor59 k)) :
    (59 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 59 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex59 k) = 0
  · change (59 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex59 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor59 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor59_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 59 ((a : ℚ) * diagonalDerivativeFactor59 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor59 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 59
      (a * (bernoulli (derivativeBernoulliIndex59 k)).num) := by omega
  change (59 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex59 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex59 k)).num)).2
      (Or.inr hthree)

end Fermat.FiftyNine.VandiverDerivativeValuation
