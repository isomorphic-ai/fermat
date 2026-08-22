import Fermat.Descent.Irregular.BernoulliData
import Fermat.Descent.Irregular.KummerCongruence
import Fermat.Descent.Irregular.VandiverLemmaTwoCore

/-!
# Prime-generic valuation step in Vandiver's diagonal calculation

After the finite character sum has diagonalized Vandiver's relation, the
`k`th logarithmic derivative is an integral coefficient times

`B_((2 * sourceNumber k) * p) / ((2 * sourceNumber k) * p) *
  (t ^ ((2 * sourceNumber k) * p) - 1)`.

If `t` is primitive modulo `p` and the integral coefficient is a
`p`-adic unit, every factor except the displayed `p` in the Bernoulli
index has valuation zero.  This file proves the resulting cube
divisibility uniformly for primes `p = 2 * r + 1`.
-/

namespace Fermat.Irregular.VandiverDerivativeValuationPrime

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverLemmaTwoCore

variable {p r t : ℕ} [Fact p.Prime]

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex (p : ℕ) (k : SourceIndex p) : ℕ :=
  (2 * sourceNumber k) * p

/-- The diagonal logarithmic-derivative factor.  The signed integer `c`
is the exact coefficient left by the finite character calculation. -/
def diagonalDerivativeFactor (p t : ℕ) (c : ℤ)
    (k : SourceIndex p) : ℚ :=
  (c : ℚ) *
    (bernoulli (derivativeBernoulliIndex p k) /
      (derivativeBernoulliIndex p k : ℚ)) *
    ((t : ℚ) ^ derivativeBernoulliIndex p k - 1)

omit [Fact p.Prime] in
theorem derivativeBernoulliIndex_even (k : SourceIndex p) :
    Even (derivativeBernoulliIndex p k) := by
  rw [derivativeBernoulliIndex, Nat.mul_assoc]
  exact even_two.mul_right (sourceNumber k * p)

omit [Fact p.Prime] in
private theorem sourceNumber_pos (k : SourceIndex p) :
    0 < sourceNumber k := by
  simp [sourceNumber]

omit [Fact p.Prime] in
private theorem two_mul_sourceNumber_lt
    (hp : p = 2 * r + 1) (k : SourceIndex p) :
    2 * sourceNumber k < p - 1 := by
  have hk := k.isLt
  simp only [sourceNumber] at hk ⊢
  omega

private theorem p_sub_one_coprime_p :
    Nat.Coprime (p - 1) p := by
  exact
    (Nat.coprime_self_sub_left
      (Fact.out : p.Prime).one_le).mpr
      (Nat.coprime_one_left p)

/-- The Bernoulli index is not divisible by `p - 1`. -/
theorem p_sub_one_not_dvd_derivativeBernoulliIndex
    (hp : p = 2 * r + 1)
    (k : SourceIndex p) :
    ¬p - 1 ∣ derivativeBernoulliIndex p k := by
  intro hdiv
  have hsmall : p - 1 ∣ 2 * sourceNumber k :=
    (p_sub_one_coprime_p (p := p)).dvd_of_dvd_mul_right
      (by simpa [derivativeBernoulliIndex, Nat.mul_assoc] using hdiv)
  have hpos : 0 < 2 * sourceNumber k := by
    exact Nat.mul_pos (by omega) (sourceNumber_pos k)
  have hle : p - 1 ≤ 2 * sourceNumber k :=
    Nat.le_of_dvd hpos hsmall
  exact (not_le_of_gt (two_mul_sourceNumber_lt hp k)) hle

/-- Von Staudt--Clausen supplies denominator control uniformly. -/
theorem bernoulli_denominatorPrimeTo
    (hp : p = 2 * r + 1)
    (k : SourceIndex p) :
    DenominatorPrimeTo p
      (bernoulli (derivativeBernoulliIndex p k)) :=
  Fermat.Irregular.BernoulliData.bernoulli_denominatorPrimeTo
    (derivativeBernoulliIndex_even k)
    (p_sub_one_not_dvd_derivativeBernoulliIndex hp k)

omit [Fact p.Prime] in
theorem p_not_dvd_two_mul_sourceNumber
    (hp : p = 2 * r + 1) (k : SourceIndex p) :
    ¬p ∣ 2 * sourceNumber k := by
  intro hdiv
  have hpos : 0 < 2 * sourceNumber k := by
    exact Nat.mul_pos (by omega) (sourceNumber_pos k)
  have hle : p ≤ 2 * sourceNumber k := Nat.le_of_dvd hpos hdiv
  have hlt := two_mul_sourceNumber_lt hp k
  omega

/-- Primitivity of `t mod p` makes the root factor a `p`-adic unit. -/
theorem p_not_dvd_rootFactor
    (hp : p = 2 * r + 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (k : SourceIndex p) :
    ¬p ∣ t ^ derivativeBernoulliIndex p k - 1 := by
  intro hdvd
  have htpos : 0 < t := by
    apply Nat.pos_of_ne_zero
    intro ht
    subst t
    exact htprim.ne_zero (by
      have hp1 := (Fact.out : p.Prime).one_lt
      omega) (by simp)
  have hone : 1 ≤ t ^ derivativeBernoulliIndex p k :=
    Nat.one_le_pow (derivativeBernoulliIndex p k) t
      htpos
  have hmod :
      1 ≡ t ^ derivativeBernoulliIndex p k [MOD p] :=
    (Nat.modEq_iff_dvd' hone).2 hdvd
  have hcast :
      ((t ^ derivativeBernoulliIndex p k : ℕ) : ZMod p) =
        ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod.symm
  have hpow :
      (t : ZMod p) ^ derivativeBernoulliIndex p k = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  apply p_sub_one_not_dvd_derivativeBernoulliIndex
    (p := p) (r := r) hp k
  exact (htprim.pow_eq_one_iff_dvd _).mp hpow

private theorem diagonalDerivativeFactor_ne_zero
    (hp : p = 2 * r + 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (c : ℤ) (hc : c ≠ 0)
    (k : SourceIndex p)
    (hB : bernoulli (derivativeBernoulliIndex p k) ≠ 0) :
    diagonalDerivativeFactor p t c k ≠ 0 := by
  unfold diagonalDerivativeFactor
  apply mul_ne_zero
  · exact mul_ne_zero (Int.cast_ne_zero.mpr hc)
      (div_ne_zero hB (by
        have hs : sourceNumber k ≠ 0 := by
          exact Nat.ne_of_gt (sourceNumber_pos k)
        exact_mod_cast Nat.mul_ne_zero
          (Nat.mul_ne_zero (by norm_num) hs)
          (Fact.out : p.Prime).ne_zero))
  · have hnat : t ^ derivativeBernoulliIndex p k ≠ 1 := by
      intro hone
      apply p_not_dvd_rootFactor hp htprim k
      rw [hone]
      simp
    norm_num only [sub_ne_zero]
    exact_mod_cast hnat

/-- Exact valuation of the generic diagonal factor multiplied by a
nonzero relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor
    (hp : p = 2 * r + 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (c : ℤ) (hc : ¬(p : ℤ) ∣ c)
    (k : SourceIndex p) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex p k) ≠ 0) :
    padicValRat p ((a : ℚ) * diagonalDerivativeFactor p t c k) =
      padicValInt p
          (a * (bernoulli (derivativeBernoulliIndex p k)).num) - 1 := by
  let N := derivativeBernoulliIndex p k
  let B := bernoulli N
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hc
    simp [hzero]
  have hsource : sourceNumber k ≠ 0 :=
    Nat.ne_of_gt (sourceNumber_pos k)
  have hNnat : N ≠ 0 := by
    dsimp [N, derivativeBernoulliIndex]
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (by norm_num) hsource)
      (Fact.out : p.Prime).ne_zero
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNnat
  have hrootNat : t ^ N - 1 ≠ 0 := by
    intro hzero
    apply p_not_dvd_rootFactor hp htprim k
    simpa [N] using hzero ▸ dvd_zero p
  have hroot : (t : ℚ) ^ N - 1 ≠ 0 := by
    have hpowne : t ^ N ≠ 1 := by
      intro hone
      exact hrootNat (by omega)
    norm_num only [sub_ne_zero]
    exact_mod_cast hpowne
  have hquotient : B / (N : ℚ) ≠ 0 := div_ne_zero hB hN
  have hNvalNat : padicValNat p N = 1 := by
    dsimp [N, derivativeBernoulliIndex]
    rw [padicValNat.mul
      (Nat.mul_ne_zero (by norm_num) hsource)
        (Fact.out : p.Prime).ne_zero,
      padicValNat.eq_zero_of_not_dvd
        (p_not_dvd_two_mul_sourceNumber hp k),
      padicValNat_self]
  have hNval : padicValRat p (N : ℚ) = 1 := by
    rw [padicValRat.of_nat, hNvalNat]
    norm_num
  have htpos : 0 < t := by
    apply Nat.pos_of_ne_zero
    intro ht
    subst t
    exact htprim.ne_zero (by
      have hp1 := (Fact.out : p.Prime).one_lt
      omega) (by simp)
  have hone : 1 ≤ t ^ N :=
    Nat.one_le_pow N t htpos
  have hrootCast :
      (t : ℚ) ^ N - 1 = ((t ^ N - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hone, Nat.cast_pow]
    norm_num
  have hrootVal : padicValRat p ((t : ℚ) ^ N - 1) = 0 := by
    rw [hrootCast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · norm_num
    · simpa [N] using p_not_dvd_rootFactor hp htprim k
  have hcoefficientVal : padicValRat p (c : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hc]
    norm_num
  have hBval : padicValRat p B =
      padicValInt p B.num := by
    exact padicValRat_eq_numeratorVal
      (by simpa [B, N] using bernoulli_denominatorPrimeTo hp k)
  have hBnum : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  change padicValRat p
      ((a : ℚ) * (((c : ℚ) * (B / (N : ℚ))) *
        ((t : ℚ) ^ N - 1))) =
    padicValInt p (a * B.num) - 1
  rw [padicValRat.mul (Int.cast_ne_zero.mpr ha)
      (mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hc0) hquotient) hroot),
    padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc0) hquotient) hroot,
    padicValRat.mul (Int.cast_ne_zero.mpr hc0) hquotient,
    padicValRat.div hB hN,
    padicValRat.of_int, hcoefficientVal, hBval, hNval, hrootVal,
    padicValInt.mul ha hBnum]
  push_cast
  ring

/-- Vandiver's valuation implication: a diagonal derivative divisible by
`p²` forces the source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (hp : p = 2 * r + 1)
    (htprim : IsPrimitiveRoot (t : ZMod p) (p - 1))
    (c : ℤ) (hc : ¬(p : ℤ) ∣ c)
    (k : SourceIndex p) (a : ℤ)
    (hderivative : PadicValAtLeast p 2
      ((a : ℚ) * diagonalDerivativeFactor p t c k)) :
    (p : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator p k := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hB : bernoulli (derivativeBernoulliIndex p k) = 0
  · change (p : ℤ) ^ 3 ∣
      a * (bernoulli (derivativeBernoulliIndex p k)).num
    rw [hB]
    simp
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hc
    simp [hzero]
  have hnonzero :
      (a : ℚ) * diagonalDerivativeFactor p t c k ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (diagonalDerivativeFactor_ne_zero hp htprim c hc0 k hB)
  have hval : (2 : ℤ) ≤
      padicValRat p
        ((a : ℚ) * diagonalDerivativeFactor p t c k) := by
    rcases hderivative with hzero | hval
    · exact (hnonzero hzero).elim
    · exact hval
  rw [padicValRat_intCast_mul_diagonalDerivativeFactor
    hp htprim c hc k a ha hB] at hval
  have hthree : 3 ≤ padicValInt p
      (a * (bernoulli (derivativeBernoulliIndex p k)).num) := by
    omega
  change (p : ℤ) ^ 3 ∣
    a * (bernoulli (derivativeBernoulliIndex p k)).num
  exact (padicValInt_dvd_iff 3
    (a * (bernoulli (derivativeBernoulliIndex p k)).num)).2
      (Or.inr hthree)

end Fermat.Irregular.VandiverDerivativeValuationPrime
