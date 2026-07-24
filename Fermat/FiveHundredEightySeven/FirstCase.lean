import Fermat.SophieGermain

/-!
# The first case for exponent 587

The auxiliary prime is `8219 = 14 * 587 + 1`.  Every nonzero `587`th
power modulo `8219` is therefore a fourteenth root of unity.  The explicit
polynomial Bezout identity below proves that two such roots cannot differ by
one.  The second Sophie--Germain condition is witnessed by
`587 ^ 14 = 7867 ≠ 1 (mod 8219)`.

The uploaded package also contains an independent certificate at
`15263 = 26 * 587 + 1`; one auxiliary prime is sufficient for the theorem,
so this file starts with the smaller degree-fourteen certificate.
-/

namespace Fermat.FiveHundredEightySeven

open Fermat.SophieGermain

theorem prime_587 : Nat.Prime 587 := by
  norm_num

theorem prime_8219 : Nat.Prime 8219 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `587`. -/
theorem auxiliaryPrimeRelation : 8219 = 14 * 587 + 1 := by
  norm_num

/-- Left coefficient in the polynomial Bezout certificate for
`T ^ 14 - 1` and `(T + 1) ^ 14 - 1` modulo `8219`. -/
def adjacencyBezoutLeft (T : ZMod 8219) : ZMod 8219 :=
  2820 * T ^ 13 - 3025 * T ^ 12 + 2318 * T ^ 11 - 3057 * T ^ 10 -
    39 * T ^ 9 - 1561 * T ^ 8 + 1479 * T ^ 7 + 2067 * T ^ 6 +
    898 * T ^ 5 - 3625 * T ^ 4 - 1390 * T ^ 3 - 1155 * T ^ 2 +
    2735 * T - 1

/-- Right coefficient in the polynomial Bezout certificate for
`T ^ 14 - 1` and `(T + 1) ^ 14 - 1` modulo `8219`. -/
def adjacencyBezoutRight (T : ZMod 8219) : ZMod 8219 :=
  -2820 * T ^ 13 + 1410 * T ^ 12 - 3789 * T ^ 11 + 869 * T ^ 10 +
    3953 * T ^ 9 - 1507 * T ^ 8 - 4102 * T ^ 7 - 1507 * T ^ 6 +
    3953 * T ^ 5 + 869 * T ^ 4 - 3789 * T ^ 3 + 1410 * T ^ 2 -
    2820 * T - 2740

/-- Exact coprimality certificate for the two adjacent-root polynomials. -/
theorem adjacencyBezoutIdentity (T : ZMod 8219) :
    adjacencyBezoutLeft T * (T ^ 14 - 1) +
        adjacencyBezoutRight T * ((T + 1) ^ 14 - 1) = 1 := by
  simp only [adjacencyBezoutLeft, adjacencyBezoutRight]
  ring_nf
  simp only [show (41095 : ZMod 8219) = 0 by decide,
    show (287665 : ZMod 8219) = 0 by decide,
    show (1232850 : ZMod 8219) = 0 by decide,
    show (3690331 : ZMod 8219) = 0 by decide,
    show (8128591 : ZMod 8219) = 0 by decide,
    show (13709292 : ZMod 8219) = 0 by decide,
    show (18188647 : ZMod 8219) = 0 by decide,
    show (19142051 : ZMod 8219) = 0 by decide,
    show (15739385 : ZMod 8219) = 0 by decide,
    show (9714858 : ZMod 8219) = 0 by decide,
    show (4824553 : ZMod 8219) = 0 by decide,
    show (4051967 : ZMod 8219) = 0 by decide,
    show (6525886 : ZMod 8219) = 0 by decide,
    show (8145029 : ZMod 8219) = 0 by decide,
    show (6484791 : ZMod 8219) = 0 by decide,
    show (3805397 : ZMod 8219) = 0 by decide,
    show (3830054 : ZMod 8219) = 0 by decide,
    show (6977931 : ZMod 8219) = 0 by decide,
    show (10249093 : ZMod 8219) = 0 by decide,
    show (10914832 : ZMod 8219) = 0 by decide,
    show (8786111 : ZMod 8219) = 0 by decide,
    show (5482073 : ZMod 8219) = 0 by decide,
    show (2638299 : ZMod 8219) = 0 by decide,
    show (953404 : ZMod 8219) = 0 by decide,
    show (238351 : ZMod 8219) = 0 by decide,
    mul_zero, sub_zero]

/-- A nonzero `587`th power modulo `8219` is a fourteenth root of unity. -/
theorem pow_587_pow_fourteen_eq_one {x : ZMod 8219} (hx : x ≠ 0) :
    (x ^ 587) ^ 14 = 1 := by
  letI : Fact (Nat.Prime 8219) := ⟨prime_8219⟩
  calc
    (x ^ 587) ^ 14 = x ^ (587 * 14) := (pow_mul x 587 14).symm
    _ = x ^ 8218 := by norm_num
    _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx

/-- No two nonzero `587`th powers modulo `8219` differ by one. -/
theorem noConsecutivePowers_587_8219 : NoConsecutivePowers 587 8219 := by
  intro x y hx hy hxy
  have hxroot := pow_587_pow_fourteen_eq_one hx
  have hyroot := pow_587_pow_fourteen_eq_one hy
  have hnext : (y ^ 587 + 1) ^ 14 = 1 := by
    rw [add_comm, ← hxy]
    exact hxroot
  have hbezout := adjacencyBezoutIdentity (y ^ 587)
  rw [hyroot, hnext] at hbezout
  exact (by decide : (0 : ZMod 8219) ≠ 1) (by simpa using hbezout)

/-- The numerical obstruction for Sophie Germain's second residue
condition. -/
theorem fiveHundredEightySeven_pow_fourteen_mod_8219 :
    (587 : ZMod 8219) ^ 14 = 7867 := by
  decide

/-- The exponent `587` is not itself a `587`th-power residue modulo `8219`. -/
theorem exponentNotPower_587_8219 : ExponentNotPower 587 8219 := by
  intro x hxpow
  letI : Fact (Nat.Prime 8219) := ⟨prime_8219⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 8219) ≠ 587) (by simpa using hxpow)
  have hfermat : x ^ 8218 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 8219 => t ^ 14) hxpow
  have heq : x ^ 8218 = (587 : ZMod 8219) ^ 14 := by
    calc
      x ^ 8218 = x ^ (587 * 14) := by norm_num
      _ = (x ^ 587) ^ 14 := pow_mul x 587 14
      _ = (587 : ZMod 8219) ^ 14 := hraise
  have hbad : (7867 : ZMod 8219) = 1 := by
    rw [← fiveHundredEightySeven_pow_fourteen_mod_8219, ← heq, hfermat]
  exact (by decide : (7867 : ZMod 8219) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `587`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 587 + y ^ 587 = z ^ 587) :
    (587 : ℤ) ∣ x ∨ (587 : ℤ) ∣ y ∨ (587 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_587 (by norm_num) prime_8219
    noConsecutivePowers_587_8219 exponentNotPower_587_8219
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 587 + y ^ 587 = z ^ 587)
    (hx : ¬(587 : ℤ) ∣ x) (hy : ¬(587 : ℤ) ∣ y)
    (hz : ¬(587 : ℤ) ∣ z) : False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.FiveHundredEightySeven
