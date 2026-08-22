import Fermat.Core.SophieGermain

/-!
# The first case for exponent 1831

The paired four-digit folding package supplies the auxiliary prime
`358877 = 196 * 1831 + 1`. Every nonzero `1831`st power modulo
`358877` is therefore a 196th root of unity.

Rather than normalize a degree-196 polynomial Bézout identity, this file
uses the package's generator `258926 = 2 ^ 1831`. Its exact order is
certified from the prime divisors `2` and `7` of `196`, after which a
finite scan over `Fin 196` proves that no subgroup element minus one is
another 196th root.

The second Sophie--Germain condition is witnessed by
`1831 ^ 196 = 40046 ≠ 1 (mod 358877)`.
-/

namespace Fermat.OneThousandEightHundredThirtyOne

open Fermat.SophieGermain

theorem prime_1831 : Nat.Prime 1831 := by
  norm_num

theorem prime_358877 : Nat.Prime 358877 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `1831`. -/
theorem auxiliaryPrimeRelation : 358877 = 196 * 1831 + 1 := by
  norm_num

/-- The package's generator of the subgroup of nonzero `1831`st powers. -/
def powerSubgroupGenerator : ZMod 358877 := 258926

/-- The generator is `2 ^ 1831` modulo the auxiliary prime. -/
theorem two_pow_1831_eq_powerSubgroupGenerator :
    (2 : ZMod 358877) ^ 1831 = powerSubgroupGenerator := by
  set_option maxRecDepth 100000 in
    decide

/-- The package residue `258926` has exact multiplicative order `196`. -/
theorem powerSubgroupGenerator_isPrimitive :
    IsPrimitiveRoot powerSubgroupGenerator 196 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · set_option maxRecDepth 100000 in
      decide
  · intro p hp hdiv
    have hfactor : p ∣ 2 ^ 2 * 7 ^ 2 := by
      norm_num at hdiv ⊢
      exact hdiv
    rcases hp.dvd_mul.mp hfactor with htwo | hseven
    · have hp2 : p = 2 :=
        Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two htwo
      subst p
      norm_num
      set_option maxRecDepth 100000 in
        decide
    · have hp7 : p = 7 :=
        Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hseven
      subst p
      norm_num
      set_option maxRecDepth 100000 in
        decide

/-- The complete 196-element adjacency scan, compressed to one test per
subgroup element: `τ ^ i - 1` is never another 196th root. -/
private theorem powerSubgroupGenerator_power_sub_one_not_root :
    ∀ i : Fin 196,
      ((powerSubgroupGenerator ^ (i : ℕ) - 1) ^ 196) ≠ 1 := by
  set_option maxRecDepth 100000 in
    decide

private theorem powerSubgroupGenerator_powers_not_consecutive
    (i j : Fin 196) :
    powerSubgroupGenerator ^ (i : ℕ) ≠
      1 + powerSubgroupGenerator ^ (j : ℕ) := by
  intro h
  apply powerSubgroupGenerator_power_sub_one_not_root i
  rw [h, add_sub_cancel_left]
  calc
    (powerSubgroupGenerator ^ (j : ℕ)) ^ 196 =
        powerSubgroupGenerator ^ ((j : ℕ) * 196) := (pow_mul _ _ _).symm
    _ = (powerSubgroupGenerator ^ 196) ^ (j : ℕ) := by
      rw [Nat.mul_comm, pow_mul]
    _ = 1 := by
      rw [powerSubgroupGenerator_isPrimitive.pow_eq_one, one_pow]

/-- Every nonzero `1831`st power belongs to the enumerated subgroup of
order `196`. -/
theorem pow_1831_eq_powerSubgroupGenerator_pow
    {x : ZMod 358877} (hx : x ≠ 0) :
    ∃ i : Fin 196,
      x ^ 1831 = powerSubgroupGenerator ^ (i : ℕ) := by
  letI : Fact (Nat.Prime 358877) := ⟨prime_358877⟩
  have hroot : (x ^ 1831) ^ 196 = 1 := by
    calc
      (x ^ 1831) ^ 196 = x ^ (1831 * 196) := (pow_mul _ _ _).symm
      _ = x ^ 358876 := by norm_num
      _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx
  obtain ⟨i, hi, hpow⟩ :=
    powerSubgroupGenerator_isPrimitive.eq_pow_of_pow_eq_one hroot
  exact ⟨⟨i, hi⟩, hpow.symm⟩

/-- No two nonzero `1831`st powers modulo `358877` differ by one. -/
theorem noConsecutivePowers_1831_358877 :
    NoConsecutivePowers 1831 358877 := by
  intro x y hx hy hxy
  obtain ⟨i, hi⟩ := pow_1831_eq_powerSubgroupGenerator_pow hx
  obtain ⟨j, hj⟩ := pow_1831_eq_powerSubgroupGenerator_pow hy
  apply powerSubgroupGenerator_powers_not_consecutive i j
  simpa only [← hi, ← hj] using hxy

/-- The package's numerical obstruction for Sophie Germain's second
residue condition. -/
theorem oneThousandEightHundredThirtyOne_pow_oneHundredNinetySix_mod_358877 :
    (1831 : ZMod 358877) ^ 196 = 40046 := by
  set_option maxRecDepth 100000 in
    decide

/-- The exponent `1831` is not itself an `1831`st-power residue modulo
`358877`. -/
theorem exponentNotPower_1831_358877 :
    ExponentNotPower 1831 358877 := by
  intro x hxpow
  letI : Fact (Nat.Prime 358877) := ⟨prime_358877⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 358877) ≠ 1831) (by simpa using hxpow)
  have hfermat : x ^ 358876 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 358877 ↦ t ^ 196) hxpow
  have heq : x ^ 358876 = (1831 : ZMod 358877) ^ 196 := by
    calc
      x ^ 358876 = x ^ (1831 * 196) := by norm_num
      _ = (x ^ 1831) ^ 196 := pow_mul x 1831 196
      _ = (1831 : ZMod 358877) ^ 196 := hraise
  have hbad : (40046 : ZMod 358877) = 1 := by
    rw [← oneThousandEightHundredThirtyOne_pow_oneHundredNinetySix_mod_358877,
      ← heq, hfermat]
  exact (by decide : (40046 : ZMod 358877) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `1831`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 1831 + y ^ 1831 = z ^ 1831) :
    (1831 : ℤ) ∣ x ∨ (1831 : ℤ) ∣ y ∨ (1831 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_1831 (by norm_num) prime_358877
    noConsecutivePowers_1831_358877 exponentNotPower_1831_358877
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 1831 + y ^ 1831 = z ^ 1831)
    (hx : ¬(1831 : ℤ) ∣ x) (hy : ¬(1831 : ℤ) ∣ y)
    (hz : ¬(1831 : ℤ) ∣ z) : False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.OneThousandEightHundredThirtyOne
