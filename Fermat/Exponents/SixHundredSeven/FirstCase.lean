import Fermat.Core.SophieGermain

/-!
# The first case for exponent 607

The paired `78233`/`94693` proof package supplies the auxiliary prime
`20639 = 34 * 607 + 1`. Every nonzero `607`th power modulo `20639`
is therefore a thirty-fourth root of unity.

The package generator `15695 = 11 ^ 607` has exact order `34`. A complete
kernel evaluation over its thirty-four powers proves that no two subgroup
elements are consecutive. The second Sophie--Germain condition is witnessed
by `607 ^ 34 = 15353 ≠ 1 (mod 20639)`.
-/

namespace Fermat.SixHundredSeven

open Fermat.SophieGermain

set_option maxRecDepth 100000

theorem prime_607 : Nat.Prime 607 := by
  norm_num

theorem prime_20639 : Nat.Prime 20639 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `607`. -/
theorem auxiliaryPrimeRelation : 20639 = 34 * 607 + 1 := by
  norm_num

/-- The package's generator of the subgroup of nonzero `607`th powers. -/
def powerSubgroupGenerator : ZMod 20639 := 15695

/-- The generator is `11 ^ 607` modulo the auxiliary prime. -/
theorem eleven_pow_607_eq_powerSubgroupGenerator :
    (11 : ZMod 20639) ^ 607 = powerSubgroupGenerator := by
  decide

/-- The package residue `15695` has exact multiplicative order `34`. -/
theorem powerSubgroupGenerator_isPrimitive :
    IsPrimitiveRoot powerSubgroupGenerator 34 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · decide
  · intro p hp hdiv
    have hfactor : p ∣ 2 ^ 1 * 17 ^ 1 := by
      norm_num at hdiv ⊢
      exact hdiv
    rcases hp.dvd_mul.mp hfactor with htwo | hseventeen
    · have hp2 : p = 2 :=
        Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two htwo
      subst p
      norm_num
      decide
    · have hp17 : p = 17 :=
        Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hseventeen
      subst p
      norm_num
      decide

/-- Complete adjacency scan over the subgroup of order `34`. -/
private theorem powerSubgroupGenerator_power_sub_one_not_root :
    ∀ i : Fin 34,
      ((powerSubgroupGenerator ^ (i : ℕ) - 1) ^ 34) ≠ 1 := by
  decide

private theorem powerSubgroupGenerator_powers_not_consecutive
    (i j : Fin 34) :
    powerSubgroupGenerator ^ (i : ℕ) ≠
      1 + powerSubgroupGenerator ^ (j : ℕ) := by
  intro h
  apply powerSubgroupGenerator_power_sub_one_not_root i
  rw [h, add_sub_cancel_left]
  calc
    (powerSubgroupGenerator ^ (j : ℕ)) ^ 34 =
        powerSubgroupGenerator ^ ((j : ℕ) * 34) := (pow_mul _ _ _).symm
    _ = (powerSubgroupGenerator ^ 34) ^ (j : ℕ) := by
      rw [Nat.mul_comm, pow_mul]
    _ = 1 := by
      rw [powerSubgroupGenerator_isPrimitive.pow_eq_one, one_pow]

/-- Every nonzero `607`th power belongs to the enumerated subgroup of
order `34`. -/
theorem pow_607_eq_powerSubgroupGenerator_pow
    {x : ZMod 20639} (hx : x ≠ 0) :
    ∃ i : Fin 34,
      x ^ 607 = powerSubgroupGenerator ^ (i : ℕ) := by
  letI : Fact (Nat.Prime 20639) := ⟨prime_20639⟩
  have hroot : (x ^ 607) ^ 34 = 1 := by
    calc
      (x ^ 607) ^ 34 = x ^ (607 * 34) := (pow_mul _ _ _).symm
      _ = x ^ 20638 := by norm_num
      _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx
  obtain ⟨i, hi, hpow⟩ :=
    powerSubgroupGenerator_isPrimitive.eq_pow_of_pow_eq_one hroot
  exact ⟨⟨i, hi⟩, hpow.symm⟩

/-- No two nonzero `607`th powers modulo `20639` differ by one. -/
theorem noConsecutivePowers_607_20639 :
    NoConsecutivePowers 607 20639 := by
  intro x y hx hy hxy
  obtain ⟨i, hi⟩ := pow_607_eq_powerSubgroupGenerator_pow hx
  obtain ⟨j, hj⟩ := pow_607_eq_powerSubgroupGenerator_pow hy
  apply powerSubgroupGenerator_powers_not_consecutive i j
  simpa only [← hi, ← hj] using hxy

/-- The package's numerical obstruction for Sophie Germain's second
residue condition. -/
theorem sixHundredSeven_pow_thirtyFour_mod_20639 :
    (607 : ZMod 20639) ^ 34 = 15353 := by
  decide

/-- The exponent `607` is not itself a `607`th-power residue modulo
`20639`. -/
theorem exponentNotPower_607_20639 :
    ExponentNotPower 607 20639 := by
  intro x hxpow
  letI : Fact (Nat.Prime 20639) := ⟨prime_20639⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 20639) ≠ 607) (by simpa using hxpow)
  have hfermat : x ^ 20638 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 20639 ↦ t ^ 34) hxpow
  have heq : x ^ 20638 = (607 : ZMod 20639) ^ 34 := by
    calc
      x ^ 20638 = x ^ (607 * 34) := by norm_num
      _ = (x ^ 607) ^ 34 := pow_mul x 607 34
      _ = (607 : ZMod 20639) ^ 34 := hraise
  have hbad : (15353 : ZMod 20639) = 1 := by
    rw [← sixHundredSeven_pow_thirtyFour_mod_20639, ← heq, hfermat]
  exact (by decide : (15353 : ZMod 20639) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `607`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 607 + y ^ 607 = z ^ 607) :
    (607 : ℤ) ∣ x ∨ (607 : ℤ) ∣ y ∨ (607 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_607 (by norm_num) prime_20639
    noConsecutivePowers_607_20639 exponentNotPower_607_20639
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 607 + y ^ 607 = z ^ 607)
    (hx : ¬(607 : ℤ) ∣ x) (hy : ¬(607 : ℤ) ∣ y)
    (hz : ¬(607 : ℤ) ∣ z) : False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.SixHundredSeven
