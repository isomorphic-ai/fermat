import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.FiveHundredEightySeven.VandiverDiagonalArithmetic587

/-!
# The valuation step in Vandiver's diagonal calculation at 587

The finite diagonal sum leaves, at source index `k`, the rational factor

`-90488362 * B_(2*k*587) / (2*k*587) *
  (6529^(2*k*587) - 1)`.

The coefficient `-90488362 = 586 * (-154417)` is the exact integer
representative supplied by the positive diagonal character calculation.
It is a `587`-adic unit.  All factors except the displayed `587` in the
Bernoulli index and the Bernoulli numerator are likewise `587`-adic units.
Thus divisibility of this rational by `587²` is exactly divisibility of the
relation exponent times the Bernoulli numerator by `587³`.
-/

namespace Fermat.FiveHundredEightySeven.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex587 (k : SourceIndex 587) : ℕ :=
  (2 * sourceNumber k) * 587

/-- The complete diagonal coefficient after Vandiver's outer factor
`p - 1` and the positive character sum have been included. -/
def diagonalDerivativeFactor587 (k : SourceIndex 587) : ℚ :=
  (-90488362 : ℚ) *
    (bernoulli (derivativeBernoulliIndex587 k) /
      (derivativeBernoulliIndex587 k : ℚ)) *
    ((6529 : ℚ) ^ derivativeBernoulliIndex587 k - 1)

theorem derivativeBernoulliIndex587_even (k : SourceIndex 587) :
    Even (derivativeBernoulliIndex587 k) := by
  rw [derivativeBernoulliIndex587, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 587)

theorem fiveHundredEightySix_not_dvd_derivativeBernoulliIndex587
    (k : SourceIndex 587) :
    ¬586 ∣ derivativeBernoulliIndex587 k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 292 := by
    simp [sourceNumber]
  simp only [derivativeBernoulliIndex587] at hq
  omega

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo587 (k : SourceIndex 587) :
    DenominatorPrimeTo 587 (bernoulli (derivativeBernoulliIndex587 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex587_even k)
    (fiveHundredEightySix_not_dvd_derivativeBernoulliIndex587 k)

theorem fiveHundredEightySeven_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 587) :
    ¬587 ∣ 2 * sourceNumber k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 292 := by
    simp [sourceNumber]
  omega

theorem fiveHundredEightySeven_not_dvd_rootFactor587
    (k : SourceIndex 587) :
    ¬587 ∣ 6529 ^ derivativeBernoulliIndex587 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 6529 ^ derivativeBernoulliIndex587 k :=
    Nat.one_le_pow (derivativeBernoulliIndex587 k) 6529 (by norm_num)
  have hmod : 1 ≡ 6529 ^ derivativeBernoulliIndex587 k [MOD 587] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((6529 ^ derivativeBernoulliIndex587 k : ℕ) : ZMod 587) =
        ((1 : ℕ) : ZMod 587) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (6529 : ZMod 587) ^ derivativeBernoulliIndex587 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply fiveHundredEightySix_not_dvd_derivativeBernoulliIndex587 k
  have hprimitive :=
    VandiverDiagonalArithmetic.teichmullerRoot587_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [VandiverDiagonalArithmetic.teichmullerRoot587] using hpow

private theorem diagonalDerivativeFactor587_ne_zero
    (k : SourceIndex 587)
    (hB : bernoulli (derivativeBernoulliIndex587 k) ≠ 0) :
    diagonalDerivativeFactor587 k ≠ 0 := by
  unfold diagonalDerivativeFactor587
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 6529 ^ derivativeBernoulliIndex587 k ≠ 1 := by
      intro hone
      apply fiveHundredEightySeven_not_dvd_rootFactor587 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor587
    (k : SourceIndex 587) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex587 k) ≠ 0) :
    padicValRat 587 ((a : ℚ) * diagonalDerivativeFactor587 k) =
      padicValInt 587
          (a * (bernoulli (derivativeBernoulliIndex587 k)).num) - 1 := by
  let N := derivativeBernoulliIndex587 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex587]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 6529 ^ N - 1 ≠ 0 := by
    intro hzero
    apply fiveHundredEightySeven_not_dvd_rootFactor587 k
    simpa [N] using hzero ▸ dvd_zero 587
  have hroot : (6529 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 6529 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 587 N = 1 := by
    dsimp [N, derivativeBernoulliIndex587]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (fiveHundredEightySeven_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 587 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 6529 ^ N :=
    Nat.one_le_pow N 6529 (by norm_num)
  have hrootCast :
      (6529 : ℚ) ^ N - 1 = ((6529 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 587 ((6529 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using fiveHundredEightySeven_not_dvd_rootFactor587 k
  have hcoefficientVal : padicValRat 587 (-90488362 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 587 B =
      padicValInt 587 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo587 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 587
      ((a : ℚ) * (((-90488362 : ℚ) * (B / (N : ℚ))) *
        ((6529 : ℚ) ^ N - 1))) =
    padicValInt 587 (a * B.num) - 1
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
derivative divisible by `587²` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 587) (a : ℤ)
    (hderivative : PadicValAtLeast 587 2
      ((a : ℚ) * diagonalDerivativeFactor587 k)) :
    (587 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 587 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex587 k) = 0
  · change (587 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex587 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor587 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor587_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 587 ((a : ℚ) * diagonalDerivativeFactor587 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor587 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 587
      (a * (bernoulli (derivativeBernoulliIndex587 k)).num) := by
    omega
  change (587 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex587 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex587 k)).num)).2
      (Or.inr hthree)

end Fermat.FiveHundredEightySeven.VandiverDerivativeValuation
