import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.OneHundredFiftySeven.VandiverDiagonalArithmetic157

/-!
# The valuation step in Vandiver's diagonal calculation at 157

The finite diagonal sum leaves, at source index `k`, the rational factor

`-1095276 * B_(2*k*157) / (2*k*157) *
  (226^(2*k*157) - 1)`.

The coefficient `-1095276 = 156 * (-7021)` is the exact integer
representative supplied by the positive diagonal character calculation.
It is a `157`-adic unit.  All factors except the displayed `157` in the
Bernoulli index and the Bernoulli numerator are likewise `157`-adic units.
Thus divisibility of this rational by `157²` is exactly divisibility of the
relation exponent times the Bernoulli numerator by `157³`.
-/

namespace Fermat.OneHundredFiftySeven.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex157 (k : SourceIndex 157) : ℕ :=
  (2 * sourceNumber k) * 157

/-- The complete diagonal coefficient after Vandiver's outer factor
`p - 1` and the positive character sum have been included. -/
def diagonalDerivativeFactor157 (k : SourceIndex 157) : ℚ :=
  (-1095276 : ℚ) *
    (bernoulli (derivativeBernoulliIndex157 k) /
      (derivativeBernoulliIndex157 k : ℚ)) *
    ((226 : ℚ) ^ derivativeBernoulliIndex157 k - 1)

theorem derivativeBernoulliIndex157_even (k : SourceIndex 157) :
    Even (derivativeBernoulliIndex157 k) := by
  rw [derivativeBernoulliIndex157, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 157)

theorem oneHundredFiftySix_not_dvd_derivativeBernoulliIndex157
    (k : SourceIndex 157) :
    ¬156 ∣ derivativeBernoulliIndex157 k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 77 := by
    simp [sourceNumber]
  simp only [derivativeBernoulliIndex157] at hq
  omega

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo157 (k : SourceIndex 157) :
    DenominatorPrimeTo 157 (bernoulli (derivativeBernoulliIndex157 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex157_even k)
    (oneHundredFiftySix_not_dvd_derivativeBernoulliIndex157 k)

theorem oneHundredFiftySeven_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 157) :
    ¬157 ∣ 2 * sourceNumber k := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hk := k.isLt
  have hspos : 0 < sourceNumber k := by simp [sourceNumber]
  have hsle : sourceNumber k ≤ 77 := by
    simp [sourceNumber]
  omega

theorem oneHundredFiftySeven_not_dvd_rootFactor157
    (k : SourceIndex 157) :
    ¬157 ∣ 226 ^ derivativeBernoulliIndex157 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 226 ^ derivativeBernoulliIndex157 k :=
    Nat.one_le_pow (derivativeBernoulliIndex157 k) 226 (by norm_num)
  have hmod : 1 ≡ 226 ^ derivativeBernoulliIndex157 k [MOD 157] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((226 ^ derivativeBernoulliIndex157 k : ℕ) : ZMod 157) =
        ((1 : ℕ) : ZMod 157) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (226 : ZMod 157) ^ derivativeBernoulliIndex157 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply oneHundredFiftySix_not_dvd_derivativeBernoulliIndex157 k
  have hprimitive :=
    VandiverDiagonalArithmetic.teichmullerRoot157_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [VandiverDiagonalArithmetic.teichmullerRoot157] using hpow

private theorem diagonalDerivativeFactor157_ne_zero
    (k : SourceIndex 157)
    (hB : bernoulli (derivativeBernoulliIndex157 k) ≠ 0) :
    diagonalDerivativeFactor157 k ≠ 0 := by
  unfold diagonalDerivativeFactor157
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 226 ^ derivativeBernoulliIndex157 k ≠ 1 := by
      intro hone
      apply oneHundredFiftySeven_not_dvd_rootFactor157 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor157
    (k : SourceIndex 157) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex157 k) ≠ 0) :
    padicValRat 157 ((a : ℚ) * diagonalDerivativeFactor157 k) =
      padicValInt 157
          (a * (bernoulli (derivativeBernoulliIndex157 k)).num) - 1 := by
  let N := derivativeBernoulliIndex157 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex157]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 226 ^ N - 1 ≠ 0 := by
    intro hzero
    apply oneHundredFiftySeven_not_dvd_rootFactor157 k
    simpa [N] using hzero ▸ dvd_zero 157
  have hroot : (226 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 226 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 157 N = 1 := by
    dsimp [N, derivativeBernoulliIndex157]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (oneHundredFiftySeven_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 157 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 226 ^ N :=
    Nat.one_le_pow N 226 (by norm_num)
  have hrootCast :
      (226 : ℚ) ^ N - 1 = ((226 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 157 ((226 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using oneHundredFiftySeven_not_dvd_rootFactor157 k
  have hcoefficientVal : padicValRat 157 (-1095276 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 157 B =
      padicValInt 157 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo157 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 157
      ((a : ℚ) * (((-1095276 : ℚ) * (B / (N : ℚ))) *
        ((226 : ℚ) ^ N - 1))) =
    padicValInt 157 (a * B.num) - 1
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
derivative divisible by `157²` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 157) (a : ℤ)
    (hderivative : PadicValAtLeast 157 2
      ((a : ℚ) * diagonalDerivativeFactor157 k)) :
    (157 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 157 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex157 k) = 0
  · change (157 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex157 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor157 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor157_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 157 ((a : ℚ) * diagonalDerivativeFactor157 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor157 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 157
      (a * (bernoulli (derivativeBernoulliIndex157 k)).num) := by
    omega
  change (157 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex157 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex157 k)).num)).2
      (Or.inr hthree)

end Fermat.OneHundredFiftySeven.VandiverDerivativeValuation
