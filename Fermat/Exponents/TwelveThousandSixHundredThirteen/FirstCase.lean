import Fermat.Core.SophieGermain

/-!
# The first case for exponent 12613

The finite proof package supplies the auxiliary prime
`126131 = 10 * 12613 + 1`. Every nonzero `12613`th power modulo
`126131` is therefore a tenth root of unity.

The package generator `81684 = 2 ^ 12613` has exact order ten.  A complete
ten-element subgroup scan proves that no two nonzero `12613`th powers
differ by one.  The second Sophie--Germain condition is witnessed by
`12613 ^ 10 = 25711 ≠ 1 (mod 126131)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen

open Fermat.SophieGermain

theorem prime_12613 : Nat.Prime 12613 := by
  norm_num

theorem prime_126131 : Nat.Prime 126131 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `12613`. -/
theorem auxiliaryPrimeRelation : 126131 = 10 * 12613 + 1 := by
  norm_num

/-- The package generator of the subgroup of nonzero `12613`th powers. -/
def powerSubgroupGenerator : ZMod 126131 := 81684

/-- The generator is `2 ^ 12613` modulo the auxiliary prime. -/
theorem two_pow_12613_eq_powerSubgroupGenerator :
    (2 : ZMod 126131) ^ 12613 = powerSubgroupGenerator := by
  set_option maxRecDepth 100000 in
    decide

/-- The package residue `81684` has exact multiplicative order ten. -/
theorem powerSubgroupGenerator_isPrimitive :
    IsPrimitiveRoot powerSubgroupGenerator 10 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · decide
  · intro p hp hdiv
    have hfactor : p ∣ 2 * 5 := by
      norm_num at hdiv ⊢
      exact hdiv
    rcases hp.dvd_mul.mp hfactor with htwo | hfive
    · have hp2 : p = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp htwo).resolve_left hp.ne_one
      subst p
      norm_num
      decide
    · have hp5 : p = 5 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hfive).resolve_left
          hp.ne_one
      subst p
      norm_num
      decide

/-- The complete ten-element adjacency scan, compressed to one test per
subgroup element. -/
private theorem powerSubgroupGenerator_power_sub_one_not_root :
    ∀ i : Fin 10,
      ((powerSubgroupGenerator ^ (i : ℕ) - 1) ^ 10) ≠ 1 := by
  decide

private theorem powerSubgroupGenerator_powers_not_consecutive
    (i j : Fin 10) :
    powerSubgroupGenerator ^ (i : ℕ) ≠
      1 + powerSubgroupGenerator ^ (j : ℕ) := by
  intro h
  apply powerSubgroupGenerator_power_sub_one_not_root i
  rw [h, add_sub_cancel_left]
  calc
    (powerSubgroupGenerator ^ (j : ℕ)) ^ 10 =
        powerSubgroupGenerator ^ ((j : ℕ) * 10) := (pow_mul _ _ _).symm
    _ = (powerSubgroupGenerator ^ 10) ^ (j : ℕ) := by
      rw [Nat.mul_comm, pow_mul]
    _ = 1 := by
      rw [powerSubgroupGenerator_isPrimitive.pow_eq_one, one_pow]

/-- Every nonzero `12613`th power belongs to the enumerated subgroup of
order ten. -/
theorem pow_12613_eq_powerSubgroupGenerator_pow
    {x : ZMod 126131} (hx : x ≠ 0) :
    ∃ i : Fin 10,
      x ^ 12613 = powerSubgroupGenerator ^ (i : ℕ) := by
  letI : Fact (Nat.Prime 126131) := ⟨prime_126131⟩
  have hroot : (x ^ 12613) ^ 10 = 1 := by
    calc
      (x ^ 12613) ^ 10 = x ^ (12613 * 10) := (pow_mul _ _ _).symm
      _ = x ^ 126130 := by norm_num
      _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx
  obtain ⟨i, hi, hpow⟩ :=
    powerSubgroupGenerator_isPrimitive.eq_pow_of_pow_eq_one hroot
  exact ⟨⟨i, hi⟩, hpow.symm⟩

/-- No two nonzero `12613`th powers modulo `126131` differ by one. -/
theorem noConsecutivePowers_12613_126131 :
    NoConsecutivePowers 12613 126131 := by
  intro x y hx hy hxy
  obtain ⟨i, hi⟩ := pow_12613_eq_powerSubgroupGenerator_pow hx
  obtain ⟨j, hj⟩ := pow_12613_eq_powerSubgroupGenerator_pow hy
  apply powerSubgroupGenerator_powers_not_consecutive i j
  simpa only [← hi, ← hj] using hxy

/-- The package's numerical obstruction for Sophie Germain's second
residue condition. -/
theorem twelveThousandSixHundredThirteen_pow_ten_mod_126131 :
    (12613 : ZMod 126131) ^ 10 = 25711 := by
  decide

/-- The exponent `12613` is not itself a `12613`th-power residue modulo
`126131`. -/
theorem exponentNotPower_12613_126131 :
    ExponentNotPower 12613 126131 := by
  intro x hxpow
  letI : Fact (Nat.Prime 126131) := ⟨prime_126131⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 126131) ≠ 12613) (by simpa using hxpow)
  have hfermat : x ^ 126130 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 126131 ↦ t ^ 10) hxpow
  have heq : x ^ 126130 = (12613 : ZMod 126131) ^ 10 := by
    calc
      x ^ 126130 = x ^ (12613 * 10) := by norm_num
      _ = (x ^ 12613) ^ 10 := pow_mul x 12613 10
      _ = (12613 : ZMod 126131) ^ 10 := hraise
  have hbad : (25711 : ZMod 126131) = 1 := by
    rw [← twelveThousandSixHundredThirteen_pow_ten_mod_126131,
      ← heq, hfermat]
  exact (by decide : (25711 : ZMod 126131) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `12613`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 12613 + y ^ 12613 = z ^ 12613) :
    (12613 : ℤ) ∣ x ∨ (12613 : ℤ) ∣ y ∨ (12613 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_12613 (by norm_num) prime_126131
    noConsecutivePowers_12613_126131 exponentNotPower_12613_126131
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 12613 + y ^ 12613 = z ^ 12613)
    (hx : ¬(12613 : ℤ) ∣ x) (hy : ¬(12613 : ℤ) ∣ y)
    (hz : ¬(12613 : ℤ) ∣ z) : False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with
    hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.TwelveThousandSixHundredThirteen
