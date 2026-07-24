import Fermat.SophieGermain

/-!
# The first case for exponent 1381

The paired four-digit folding package supplies the auxiliary prime
`38669 = 28 * 1381 + 1`. Every nonzero `1381`st power modulo `38669`
is therefore a twenty-eighth root of unity. The explicit polynomial
Bézout identity below proves that two such roots cannot differ by one.

The second Sophie--Germain condition is witnessed by
`1381 ^ 28 = 28615 ≠ 1 (mod 38669)`.
-/

namespace Fermat.OneThousandThreeHundredEightyOne

open Fermat.SophieGermain

theorem prime_1381 : Nat.Prime 1381 := by
  norm_num

theorem prime_38669 : Nat.Prime 38669 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `1381`. -/
theorem auxiliaryPrimeRelation : 38669 = 28 * 1381 + 1 := by
  norm_num

/-- Left coefficient in the polynomial Bézout certificate for
`T ^ 28 - 1` and `(T + 1) ^ 28 - 1` modulo `38669`. -/
def adjacencyBezoutLeft (T : ZMod 38669) : ZMod 38669 :=
  -11320 * T ^ 27 - 1948 * T ^ 26 + 5402 * T ^ 25 -
    10953 * T ^ 24 - 8371 * T ^ 23 - 2840 * T ^ 22 +
    12720 * T ^ 21 - 7864 * T ^ 20 - 17482 * T ^ 19 -
    6209 * T ^ 18 + 15993 * T ^ 17 + 14174 * T ^ 16 -
    14275 * T ^ 15 - 2156 * T ^ 14 + 4131 * T ^ 13 -
    16576 * T ^ 12 - 11327 * T ^ 11 + 2250 * T ^ 10 +
    11307 * T ^ 9 + 18501 * T ^ 8 - 14504 * T ^ 7 -
    17333 * T ^ 6 + 9083 * T ^ 5 - 485 * T ^ 4 -
    18195 * T ^ 3 + 7482 * T ^ 2 - 12899 * T - 1

/-- Right coefficient in the polynomial Bézout certificate for
`T ^ 28 - 1` and `(T + 1) ^ 28 - 1` modulo `38669`. -/
def adjacencyBezoutRight (T : ZMod 38669) : ZMod 38669 :=
  11320 * T ^ 27 - 5660 * T ^ 26 + 11701 * T ^ 25 +
    4613 * T ^ 24 + 5197 * T ^ 23 + 10600 * T ^ 22 -
    6206 * T ^ 21 - 2609 * T ^ 20 - 14654 * T ^ 19 -
    814 * T ^ 18 - 8961 * T ^ 17 - 6905 * T ^ 16 -
    19158 * T ^ 15 + 11586 * T ^ 14 - 19158 * T ^ 13 -
    6905 * T ^ 12 - 8961 * T ^ 11 - 814 * T ^ 10 -
    14654 * T ^ 9 - 2609 * T ^ 8 - 6206 * T ^ 7 +
    10600 * T ^ 6 + 5197 * T ^ 5 + 4613 * T ^ 4 +
    11701 * T ^ 3 - 5660 * T ^ 2 + 11320 * T - 12890

/-- Exact coprimality certificate for the two adjacent-root polynomials. -/
theorem adjacencyBezoutIdentity (T : ZMod 38669) :
    adjacencyBezoutLeft T * (T ^ 28 - 1) +
        adjacencyBezoutRight T * ((T + 1) ^ 28 - 1) = 1 := by
  simp only [adjacencyBezoutLeft, adjacencyBezoutRight]
  ring_nf
  simp only [show (348021 : ZMod 38669) = 0 by decide,
    show (4562942 : ZMod 38669) = 0 by decide,
    show (38088965 : ZMod 38669) = 0 by decide,
    show (228649797 : ZMod 38669) = 0 by decide,
    show (1049051301 : ZMod 38669) = 0 by decide,
    show (3819298461 : ZMod 38669) = 0 by decide,
    show (11296877667 : ZMod 38669) = 0 by decide,
    show (27527223692 : ZMod 38669) = 0 by decide,
    show (55547554472 : ZMod 38669) = 0 by decide,
    show (92264234000 : ZMod 38669) = 0 by decide,
    show (122653195706 : ZMod 38669) = 0 by decide,
    show (118735175288 : ZMod 38669) = 0 by decide,
    show (48581102108 : ZMod 38669) = 0 by decide,
    show (105382073546 : ZMod 38669) = 0 by decide,
    show (327815326099 : ZMod 38669) = 0 by decide,
    show (564089567167 : ZMod 38669) = 0 by decide,
    show (733114202314 : ZMod 38669) = 0 by decide,
    show (755796316313 : ZMod 38669) = 0 by decide,
    show (586761781902 : ZMod 38669) = 0 by decide,
    show (234444965354 : ZMod 38669) = 0 by decide,
    show (240702614948 : ZMod 38669) = 0 by decide,
    show (749678068464 : ZMod 38669) = 0 by decide,
    show (1208243028151 : ZMod 38669) = 0 by decide,
    show (1563212808782 : ZMod 38669) = 0 by decide,
    show (1800707752842 : ZMod 38669) = 0 by decide,
    show (1937167328308 : ZMod 38669) = 0 by decide,
    show (2001927810699 : ZMod 38669) = 0 by decide,
    show (2020263490429 : ZMod 38669) = 0 by decide,
    show (2001927462678 : ZMod 38669) = 0 by decide,
    show (1937162456014 : ZMod 38669) = 0 by decide,
    show (1800665526294 : ZMod 38669) = 0 by decide,
    show (1562948892857 : ZMod 38669) = 0 by decide,
    show (1206976193042 : ZMod 38669) = 0 by decide,
    show (744821899437 : ZMod 38669) = 0 by decide,
    show (225440347338 : ZMod 38669) = 0 by decide,
    show (274508446832 : ZMod 38669) = 0 by decide,
    show (675791702073 : ZMod 38669) = 0 by decide,
    show (924953199440 : ZMod 38669) = 0 by decide,
    show (1009916378219 : ZMod 38669) = 0 by decide,
    show (956225979810 : ZMod 38669) = 0 by decide,
    show (810444739197 : ZMod 38669) = 0 by decide,
    show (622485054820 : ZMod 38669) = 0 by decide,
    show (434048310990 : ZMod 38669) = 0 by decide,
    show (273401237355 : ZMod 38669) = 0 by decide,
    show (154148980199 : ZMod 38669) = 0 by decide,
    show (76892649127 : ZMod 38669) = 0 by decide,
    show (33482365699 : ZMod 38669) = 0 by decide,
    show (12536257786 : ZMod 38669) = 0 by decide,
    show (3965389943 : ZMod 38669) = 0 by decide,
    show (1036870566 : ZMod 38669) = 0 by decide,
    show (217783808 : ZMod 38669) = 0 by decide,
    show (35266128 : ZMod 38669) = 0 by decide,
    show (4137583 : ZMod 38669) = 0 by decide,
    show (309352 : ZMod 38669) = 0 by decide,
    mul_zero, sub_zero, add_zero]

/-- A nonzero `1381`st power modulo `38669` is a twenty-eighth root of
unity. -/
theorem pow_1381_pow_twentyEight_eq_one {x : ZMod 38669} (hx : x ≠ 0) :
    (x ^ 1381) ^ 28 = 1 := by
  letI : Fact (Nat.Prime 38669) := ⟨prime_38669⟩
  calc
    (x ^ 1381) ^ 28 = x ^ (1381 * 28) := (pow_mul x 1381 28).symm
    _ = x ^ 38668 := by norm_num
    _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx

/-- No two nonzero `1381`st powers modulo `38669` differ by one. -/
theorem noConsecutivePowers_1381_38669 : NoConsecutivePowers 1381 38669 := by
  intro x y hx hy hxy
  have hxroot := pow_1381_pow_twentyEight_eq_one hx
  have hyroot := pow_1381_pow_twentyEight_eq_one hy
  have hnext : (y ^ 1381 + 1) ^ 28 = 1 := by
    rw [add_comm, ← hxy]
    exact hxroot
  have hbezout := adjacencyBezoutIdentity (y ^ 1381)
  rw [hyroot, hnext] at hbezout
  exact (by decide : (0 : ZMod 38669) ≠ 1) (by simpa using hbezout)

/-- The numerical obstruction for Sophie Germain's second residue
condition. -/
theorem oneThousandThreeHundredEightyOne_pow_twentyEight_mod_38669 :
    (1381 : ZMod 38669) ^ 28 = 28615 := by
  decide

/-- The exponent `1381` is not itself a `1381`st-power residue modulo
`38669`. -/
theorem exponentNotPower_1381_38669 : ExponentNotPower 1381 38669 := by
  intro x hxpow
  letI : Fact (Nat.Prime 38669) := ⟨prime_38669⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 38669) ≠ 1381) (by simpa using hxpow)
  have hfermat : x ^ 38668 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 38669 ↦ t ^ 28) hxpow
  have heq : x ^ 38668 = (1381 : ZMod 38669) ^ 28 := by
    calc
      x ^ 38668 = x ^ (1381 * 28) := by norm_num
      _ = (x ^ 1381) ^ 28 := pow_mul x 1381 28
      _ = (1381 : ZMod 38669) ^ 28 := hraise
  have hbad : (28615 : ZMod 38669) = 1 := by
    rw [← oneThousandThreeHundredEightyOne_pow_twentyEight_mod_38669,
      ← heq, hfermat]
  exact (by decide : (28615 : ZMod 38669) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `1381`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 1381 + y ^ 1381 = z ^ 1381) :
    (1381 : ℤ) ∣ x ∨ (1381 : ℤ) ∣ y ∨ (1381 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_1381 (by norm_num) prime_38669
    noConsecutivePowers_1381_38669 exponentNotPower_1381_38669
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 1381 + y ^ 1381 = z ^ 1381)
    (hx : ¬(1381 : ℤ) ∣ x) (hy : ¬(1381 : ℤ) ∣ y)
    (hz : ¬(1381 : ℤ) ∣ z) : False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.OneThousandThreeHundredEightyOne
