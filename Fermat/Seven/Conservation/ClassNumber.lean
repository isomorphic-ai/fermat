import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime

/-!
# Class number one for the seventh cyclotomic field

This is a local, pure-Mathlib reconstruction of the small Minkowski
calculation used in the `flt-regular` exponent-seven development.  We credit
that development for the proof shape, but deliberately do not import it.

The Minkowski bound has floor `4`.  Thus only rational primes `2` and `3`
can contribute a nontrivial ideal class.  Mathlib's cyclotomic inertia-degree
theorem computes their residual degrees as the orders of `2` and `3` modulo
`7`, namely `3` and `6`; consequently their prime-ideal norms are already
larger than the bound.
-/

open scoped NumberField

namespace Fermat.Seven.Conservation

noncomputable section

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  Finset IsCyclotomicExtension.Rat

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {7} ℚ K]

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- The numerical core of the seventh-cyclotomic Minkowski calculation. -/
private lemma minkowskiNumericalFloor :
    ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 3 *
          (6! / 6 ^ 6 * √16807) := by
        gcongr
        exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 3 *
          (6! / 6 ^ 6 * 129) := by
        gcongr
        exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 4 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 3 *
          (6! / 6 ^ 6 * √16807) := by
        gcongr
        exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 3 *
          (6! / 6 ^ 6 * 130) := by
        gcongr
        exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

/-- The Minkowski bound of every seventh cyclotomic field has floor `4`. -/
theorem minkowskiFloor_seven : ⌊(M K)⌋₊ = 4 := by
  rw [IsCyclotomicExtension.Rat.discr_prime 7 K,
    IsCyclotomicExtension.finrank (n := 7) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num)),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 7,
    Nat.totient_prime Nat.prime_seven]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg,
    Int.cast_ofNat, abs_neg, abs_ofNat]
  exact minkowskiNumericalFloor

private theorem orderOf_two_mod_seven : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · decide
  · intro m hm hm0
    interval_cases m <;> decide

private theorem orderOf_three_mod_seven : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · decide
  · intro m hm hm0
    interval_cases m <;> decide

/-- The ring of integers of a seventh cyclotomic number field is a PID. -/
theorem ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 K) := by
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  intro p hpMem hpPrime
  rw [minkowskiFloor_seven] at hpMem ⊢
  simp only [Finset.mem_Icc] at hpMem
  rcases hpMem with ⟨hpLower, hpUpper⟩
  have hp23 : p = 2 ∨ p = 3 := by
    interval_cases p
    · norm_num at hpPrime
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num at hpPrime
  letI : Fact (Nat.Prime p) := ⟨hpPrime⟩
  let pIdeal : Ideal ℤ := Ideal.span {(p : ℤ)}
  obtain ⟨⟨P, hPPrime, hPLies⟩⟩ :=
    pIdeal.nonempty_primesOver (S := 𝓞 K)
  letI : P.IsPrime := hPPrime
  letI : P.LiesOver pIdeal := hPLies
  refine ⟨P, ⟨hPPrime, hPLies⟩, Or.inl ?_⟩
  change 4 < p ^ (pIdeal.inertiaDeg P)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
    (m := 7) p K P (by rcases hp23 with rfl | rfl <;> norm_num)]
  rcases hp23 with rfl | rfl
  · change 4 < 2 ^ orderOf (2 : ZMod 7)
    rw [orderOf_two_mod_seven]
    norm_num
  · change 4 < 3 ^ orderOf (3 : ZMod 7)
    rw [orderOf_three_mod_seven]
    norm_num

/-- Every seventh cyclotomic number field has class number one. -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    ringOfIntegers_isPrincipalIdealRing

end

end Fermat.Seven.Conservation
