import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.SixHundredNinetyOne.VandiverDiagonalArithmetic691

/-!
# The valuation step in Vandiver's diagonal calculation at 691

The finite diagonal sum leaves, at source index `k`, the rational factor

`-138309810 * B_(2*k*691) / (2*k*691) *
  (4955^(2*k*691) - 1)`.

The coefficient `-138309810 = 690 * (-200449)` is the exact integer
representative supplied by the positive diagonal character calculation.
It is a `691`-adic unit.  All factors except the displayed `691` in the
Bernoulli index and the Bernoulli numerator are likewise `691`-adic units.
Thus divisibility of this rational by `691²` is exactly divisibility of the
relation exponent times the Bernoulli numerator by `691³`.
-/

namespace Fermat.SixHundredNinetyOne.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex691 (k : SourceIndex 691) : ℕ :=
  (2 * sourceNumber k) * 691

/-- The complete diagonal coefficient after Vandiver's outer factor
`p - 1` and the positive character sum have been included. -/
def diagonalDerivativeFactor691 (k : SourceIndex 691) : ℚ :=
  (-138309810 : ℚ) *
    (bernoulli (derivativeBernoulliIndex691 k) /
      (derivativeBernoulliIndex691 k : ℚ)) *
    ((4955 : ℚ) ^ derivativeBernoulliIndex691 k - 1)

theorem derivativeBernoulliIndex691_even (k : SourceIndex 691) :
    Even (derivativeBernoulliIndex691 k) := by
  rw [derivativeBernoulliIndex691, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 691)

theorem sixHundredNinety_not_dvd_derivativeBernoulliIndex691
    (k : SourceIndex 691) :
    ¬690 ∣ derivativeBernoulliIndex691 k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 344 := by
    simp [sourceNumber]
  simp only [derivativeBernoulliIndex691] at hq
  omega

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo691 (k : SourceIndex 691) :
    DenominatorPrimeTo 691 (bernoulli (derivativeBernoulliIndex691 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex691_even k)
    (sixHundredNinety_not_dvd_derivativeBernoulliIndex691 k)

theorem sixHundredNinetyOne_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 691) :
    ¬691 ∣ 2 * sourceNumber k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 344 := by
    simp [sourceNumber]
  omega

theorem sixHundredNinetyOne_not_dvd_rootFactor691
    (k : SourceIndex 691) :
    ¬691 ∣ 4955 ^ derivativeBernoulliIndex691 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 4955 ^ derivativeBernoulliIndex691 k :=
    Nat.one_le_pow (derivativeBernoulliIndex691 k) 4955 (by norm_num)
  have hmod : 1 ≡ 4955 ^ derivativeBernoulliIndex691 k [MOD 691] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((4955 ^ derivativeBernoulliIndex691 k : ℕ) : ZMod 691) =
        ((1 : ℕ) : ZMod 691) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (4955 : ZMod 691) ^ derivativeBernoulliIndex691 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply sixHundredNinety_not_dvd_derivativeBernoulliIndex691 k
  have hprimitive :=
    VandiverDiagonalArithmetic.teichmullerRoot691_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [VandiverDiagonalArithmetic.teichmullerRoot691] using hpow

private theorem diagonalDerivativeFactor691_ne_zero
    (k : SourceIndex 691)
    (hB : bernoulli (derivativeBernoulliIndex691 k) ≠ 0) :
    diagonalDerivativeFactor691 k ≠ 0 := by
  unfold diagonalDerivativeFactor691
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 4955 ^ derivativeBernoulliIndex691 k ≠ 1 := by
      intro hone
      apply sixHundredNinetyOne_not_dvd_rootFactor691 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor691
    (k : SourceIndex 691) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex691 k) ≠ 0) :
    padicValRat 691 ((a : ℚ) * diagonalDerivativeFactor691 k) =
      padicValInt 691
          (a * (bernoulli (derivativeBernoulliIndex691 k)).num) - 1 := by
  let N := derivativeBernoulliIndex691 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex691]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 4955 ^ N - 1 ≠ 0 := by
    intro hzero
    apply sixHundredNinetyOne_not_dvd_rootFactor691 k
    simpa [N] using hzero ▸ dvd_zero 691
  have hroot : (4955 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 4955 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 691 N = 1 := by
    dsimp [N, derivativeBernoulliIndex691]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (sixHundredNinetyOne_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 691 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 4955 ^ N :=
    Nat.one_le_pow N 4955 (by norm_num)
  have hrootCast :
      (4955 : ℚ) ^ N - 1 = ((4955 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 691 ((4955 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using sixHundredNinetyOne_not_dvd_rootFactor691 k
  have hcoefficientVal : padicValRat 691 (-138309810 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 691 B =
      padicValInt 691 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo691 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 691
      ((a : ℚ) * (((-138309810 : ℚ) * (B / (N : ℚ))) *
        ((4955 : ℚ) ^ N - 1))) =
    padicValInt 691 (a * B.num) - 1
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
derivative divisible by `691²` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 691) (a : ℤ)
    (hderivative : PadicValAtLeast 691 2
      ((a : ℚ) * diagonalDerivativeFactor691 k)) :
    (691 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 691 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex691 k) = 0
  · change (691 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex691 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor691 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor691_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 691 ((a : ℚ) * diagonalDerivativeFactor691 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor691 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 691
      (a * (bernoulli (derivativeBernoulliIndex691 k)).num) := by
    omega
  change (691 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex691 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex691 k)).num)).2
      (Or.inr hthree)

end Fermat.SixHundredNinetyOne.VandiverDerivativeValuation
