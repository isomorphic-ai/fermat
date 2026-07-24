import Fermat.Irregular.BernoulliData
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.SixtySeven.VandiverDiagonalArithmetic67

/-!
# The valuation step in Vandiver's diagonal calculation at 67

The finite diagonal sum leaves, at source index `k`, the rational factor

`-39864 * B_(2*k*67) / (2*k*67) * (1342^(2*k*67) - 1)`.

Here `-39864 = 66 * (-604)` is the product of Vandiver's outer factor
`p - 1` and the exact diagonal residue from
`VandiverDiagonalArithmetic67`.  It is a `67`-adic unit.  All other
factors except the displayed `67` in the denominator and the Bernoulli
numerator are also `67`-adic units.  Thus divisibility of this rational by
`67²` is equivalent to divisibility of the relation exponent times the
Bernoulli numerator by `67³`.
-/

namespace Fermat.SixtySeven.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex67 (k : SourceIndex 67) : ℕ :=
  (2 * sourceNumber k) * 67

/-- The diagonal coefficient after Vandiver's outer factor and the
positive integral character sum have been included. -/
def diagonalDerivativeFactor67 (k : SourceIndex 67) : ℚ :=
  (-39864 : ℚ) *
    (bernoulli (derivativeBernoulliIndex67 k) /
      (derivativeBernoulliIndex67 k : ℚ)) *
    ((1342 : ℚ) ^ derivativeBernoulliIndex67 k - 1)

theorem derivativeBernoulliIndex67_even (k : SourceIndex 67) :
    Even (derivativeBernoulliIndex67 k) := by
  rw [derivativeBernoulliIndex67, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * 67)

theorem sixtySix_not_dvd_derivativeBernoulliIndex67
    (k : SourceIndex 67) :
    ¬66 ∣ derivativeBernoulliIndex67 k := by
  fin_cases k <;> norm_num [derivativeBernoulliIndex67, sourceNumber]

/-- Von Staudt--Clausen supplies the required denominator control. -/
theorem bernoulli_denominatorPrimeTo67 (k : SourceIndex 67) :
    DenominatorPrimeTo 67 (bernoulli (derivativeBernoulliIndex67 k)) :=
  bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex67_even k)
    (sixtySix_not_dvd_derivativeBernoulliIndex67 k)

theorem sixtySeven_not_dvd_two_mul_sourceNumber (k : SourceIndex 67) :
    ¬67 ∣ 2 * sourceNumber k := by
  fin_cases k <;> norm_num [sourceNumber]

theorem sixtySeven_not_dvd_rootFactor67 (k : SourceIndex 67) :
    ¬67 ∣ 1342 ^ derivativeBernoulliIndex67 k - 1 := by
  intro hdvd
  have hone : 1 ≤ 1342 ^ derivativeBernoulliIndex67 k :=
    Nat.one_le_pow (derivativeBernoulliIndex67 k) 1342 (by norm_num)
  have hmod : 1 ≡ 1342 ^ derivativeBernoulliIndex67 k [MOD 67] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((1342 ^ derivativeBernoulliIndex67 k : ℕ) : ZMod 67) =
        ((1 : ℕ) : ZMod 67) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (1342 : ZMod 67) ^ derivativeBernoulliIndex67 k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  apply sixtySix_not_dvd_derivativeBernoulliIndex67 k
  have hprimitive :=
    Fermat.SixtySeven.VandiverDiagonalArithmetic.teichmullerRoot67_isPrimitive
  apply (hprimitive.pow_eq_one_iff_dvd _).mp
  simpa [
    Fermat.SixtySeven.VandiverDiagonalArithmetic.teichmullerRoot67] using
      hpow

private theorem diagonalDerivativeFactor67_ne_zero
    (k : SourceIndex 67)
    (hB : bernoulli (derivativeBernoulliIndex67 k) ≠ 0) :
    diagonalDerivativeFactor67 k ≠ 0 := by
  unfold diagonalDerivativeFactor67
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by simp [sourceNumber]
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs) (by norm_num)))
  · have hnat : 1342 ^ derivativeBernoulliIndex67 k ≠ 1 := by
      intro hone
      apply sixtySeven_not_dvd_rootFactor67 k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor67
    (k : SourceIndex 67) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex67 k) ≠ 0) :
    padicValRat 67 ((a : ℚ) * diagonalDerivativeFactor67 k) =
      padicValInt 67
          (a * (bernoulli (derivativeBernoulliIndex67 k)).num) - 1 := by
  let N := derivativeBernoulliIndex67 k
  let B := bernoulli N
  have hsource : sourceNumber k ≠ 0 := by simp [sourceNumber]
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex67]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : 1342 ^ N - 1 ≠ 0 := by
    intro hzero
    apply sixtySeven_not_dvd_rootFactor67 k
    simpa [N] using hzero ▸ dvd_zero 67
  have hroot : (1342 : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : 1342 ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat 67 N = 1 := by
    dsimp [N, derivativeBernoulliIndex67]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource) (by norm_num),
      padicValNat.eq_zero_of_not_dvd
        (sixtySeven_not_dvd_two_mul_sourceNumber k),
      padicValNat_self]
  have hNval : padicValRat 67 (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have hone : 1 ≤ 1342 ^ N :=
    Nat.one_le_pow N 1342 (by norm_num)
  have hrootCast :
      (1342 : ℚ) ^ N - 1 = ((1342 ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat 67 ((1342 : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using sixtySeven_not_dvd_rootFactor67 k
  have hcoefficientVal : padicValRat 67 (-39864 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hBval : padicValRat 67 B =
      padicValInt 67 B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo67 k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat 67
      ((a : ℚ) * (((-39864 : ℚ) * (B / (N : ℚ))) *
        ((1342 : ℚ) ^ N - 1))) =
    padicValInt 67 (a * B.num) - 1
  rw [padicValRat.mul (Int.cast_ne_zero.mpr ha)
      (mul_ne_zero (mul_ne_zero (by norm_num) hquotient) hroot),
    padicValRat.mul (mul_ne_zero (by norm_num) hquotient) hroot,
    padicValRat.mul (by norm_num) hquotient,
    padicValRat.div hB hN,
    padicValRat.of_int, hcoefficientVal, hBval, hNval, hrootVal,
    padicValInt.mul ha hBnum]
  push_cast
  ring

/-- Vandiver's valuation implication: a diagonal logarithmic derivative
divisible by `67²` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 67) (a : ℤ)
    (hderivative : PadicValAtLeast 67 2
      ((a : ℚ) * diagonalDerivativeFactor67 k)) :
    (67 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 67 k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex67 k) = 0
  · change (67 : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex67 k)).num
    rw [hB]
    simp
  have hnonzero : (a : ℚ) * diagonalDerivativeFactor67 k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor67_ne_zero k hB)
  have hval : (2 : ℤ) ≤
      padicValRat 67 ((a : ℚ) * diagonalDerivativeFactor67 k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor67 k a ha hB] at hval
  have hthree : 3 ≤ padicValInt 67
      (a * (bernoulli (derivativeBernoulliIndex67 k)).num) := by
    omega
  change (67 : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex67 k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex67 k)).num)).2
      (Or.inr hthree)

end Fermat.SixtySeven.VandiverDerivativeValuation
