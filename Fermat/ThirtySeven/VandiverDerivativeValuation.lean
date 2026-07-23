import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.ThirtySeven.VandiverDiagonalArithmetic

/-!
# The valuation step in Vandiver's diagonal calculation at 37

The finite diagonal sum leaves, at source index `k`, the rational factor

`-36 * B_(2*k*37) / (2*k*37) * (76^(2*k*37) - 1)`.

All factors except the displayed `37` in the denominator and the Bernoulli
numerator are `37`-adic units.  Consequently divisibility of this rational
by `37^2` is exactly divisibility of the exponent times the Bernoulli
numerator by `37^3`.  This file makes that final denominator bookkeeping
explicit.
-/

namespace Fermat.ThirtySeven.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex37 (k : SourceIndex 37) : ℕ :=
  (2 * sourceNumber k) * 37

/-- The diagonal coefficient remaining after Vandiver's outer factor
`p - 1` and the positive integral character sum have been included. -/
def diagonalDerivativeFactor37 (k : SourceIndex 37) : ℚ :=
  (-36 : ℚ) *
    (bernoulli (derivativeBernoulliIndex37 k) /
      (derivativeBernoulliIndex37 k : ℚ)) *
    ((76 : ℚ) ^ derivativeBernoulliIndex37 k - 1)

theorem derivativeBernoulliIndex37_even (k : SourceIndex 37) :
    Even (derivativeBernoulliIndex37 k) := by
  rw [derivativeBernoulliIndex37, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 37)

theorem thirtySix_not_dvd_derivativeBernoulliIndex37
    (k : SourceIndex 37) :
    ¬36 ∣ derivativeBernoulliIndex37 k := by
  fin_cases k <;> norm_num [derivativeBernoulliIndex37, sourceNumber]

/-- Von Staudt--Clausen supplies the required denominator control. -/
theorem bernoulli_denominatorPrimeTo37 (k : SourceIndex 37) :
    DenominatorPrimeTo 37 (bernoulli (derivativeBernoulliIndex37 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex37_even k)
    (thirtySix_not_dvd_derivativeBernoulliIndex37 k)

theorem thirtySeven_not_dvd_two_mul_sourceNumber (k : SourceIndex 37) :
    ¬37 ∣ 2 * sourceNumber k := by
  fin_cases k <;> norm_num [sourceNumber]

theorem thirtySeven_not_dvd_rootFactor37 (k : SourceIndex 37) :
    ¬37 ∣ 76 ^ derivativeBernoulliIndex37 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 76 ^ derivativeBernoulliIndex37 k :=
    Nat.one_le_pow (derivativeBernoulliIndex37 k) 76 (by norm_num)
  have hmod : 1 ≡ 76 ^ derivativeBernoulliIndex37 k [MOD 37] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((76 ^ derivativeBernoulliIndex37 k : ℕ) : ZMod 37) =
        ((1 : ℕ) : ZMod 37) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (76 : ZMod 37) ^ derivativeBernoulliIndex37 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply thirtySix_not_dvd_derivativeBernoulliIndex37 k
  have hprimitive :=
    VandiverDiagonalArithmetic.teichmullerRoot37_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [VandiverDiagonalArithmetic.teichmullerRoot37] using hpow

private theorem diagonalDerivativeFactor37_ne_zero
    (k : SourceIndex 37)
    (hB : bernoulli (derivativeBernoulliIndex37 k) ≠ 0) :
    diagonalDerivativeFactor37 k ≠ 0 := by
  unfold diagonalDerivativeFactor37
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 76 ^ derivativeBernoulliIndex37 k ≠ 1 := by
      intro hone
      apply thirtySeven_not_dvd_rootFactor37 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor37
    (k : SourceIndex 37) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex37 k) ≠ 0) :
    padicValRat 37 ((a : ℚ) * diagonalDerivativeFactor37 k) =
      padicValInt 37
          (a * (bernoulli (derivativeBernoulliIndex37 k)).num) - 1 := by
  let N := derivativeBernoulliIndex37 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex37]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 76 ^ N - 1 ≠ 0 := by
    intro hzero
    apply thirtySeven_not_dvd_rootFactor37 k
    simpa [N] using hzero ▸ dvd_zero 37
  have hroot : (76 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 76 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 37 N = 1 := by
    dsimp [N, derivativeBernoulliIndex37]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (thirtySeven_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 37 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 76 ^ N :=
    Nat.one_le_pow N 76 (by norm_num)
  have hrootCast :
      (76 : ℚ) ^ N - 1 = ((76 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 37 ((76 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using thirtySeven_not_dvd_rootFactor37 k
  have hminusVal : padicValRat 37 (-36 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 37 B =
      padicValInt 37 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo37 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 37
      ((a : ℚ) * (((-36 : ℚ) * (B / (N : ℚ))) *
        ((76 : ℚ) ^ N - 1))) =
    padicValInt 37 (a * B.num) - 1
  rw [padicValRat.mul (Int.cast_ne_zero.mpr ha)
      (mul_ne_zero (mul_ne_zero (by norm_num) hquotient) hroot),
    padicValRat.mul (mul_ne_zero (by norm_num) hquotient) hroot,
    padicValRat.mul (by norm_num) hquotient,
    padicValRat.div hB hN,
    padicValRat.of_int, hminusVal, hBval, hNval, hrootVal,
    padicValInt.mul ha hBnum]
  push_cast
  ring

/-- Vandiver's last valuation implication: a diagonal logarithmic
derivative divisible by `37^2` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 37) (a : ℤ)
    (hderivative : PadicValAtLeast 37 2
      ((a : ℚ) * diagonalDerivativeFactor37 k)) :
    (37 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 37 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex37 k) = 0
  · change (37 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex37 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor37 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor37_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 37 ((a : ℚ) * diagonalDerivativeFactor37 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor37 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 37
      (a * (bernoulli (derivativeBernoulliIndex37 k)).num) := by omega
  change (37 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex37 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex37 k)).num)).2
      (Or.inr hthree)

end Fermat.ThirtySeven.VandiverDerivativeValuation
