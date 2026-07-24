import Fermat.SophieGermain

/-!
# The first case for exponent 691

The proof package supplies the auxiliary prime
`11057 = 16 * 691 + 1`.  Its verifier enumerates the sixteen nonzero
`691`st-power residues and checks that no two are consecutive.  Here that
finite table is compressed into a polynomial Bézout certificate for
`T ^ 16 - 1` and `(T + 1) ^ 16 - 1` over `ZMod 11057`.

The second Sophie--Germain condition is witnessed by
`691 ^ 16 = 10803 ≠ 1 (mod 11057)`.
-/

namespace Fermat.SixHundredNinetyOne

open Fermat.SophieGermain

theorem prime_691 : Nat.Prime 691 := by
  norm_num

theorem prime_11057 : Nat.Prime 11057 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `691`. -/
theorem auxiliaryPrimeRelation : 11057 = 16 * 691 + 1 := by
  norm_num

/-- Left coefficient in the polynomial Bézout certificate for
`T ^ 16 - 1` and `(T + 1) ^ 16 - 1` modulo `11057`. -/
def adjacencyBezoutLeft (T : ZMod 11057) : ZMod 11057 :=
  -4963 * T ^ 15 - 5056 * T ^ 14 - 5198 * T ^ 13 +
    3707 * T ^ 12 - 5066 * T ^ 11 - 223 * T ^ 10 +
    2002 * T ^ 9 + 4974 * T ^ 8 + 4007 * T ^ 7 -
    3794 * T ^ 6 - 736 * T ^ 5 - 1345 * T ^ 4 -
    4552 * T ^ 3 + 1969 * T ^ 2 - 3691 * T - 1

/-- Right coefficient in the polynomial Bézout certificate for
`T ^ 16 - 1` and `(T + 1) ^ 16 - 1` modulo `11057`. -/
def adjacencyBezoutRight (T : ZMod 11057) : ZMod 11057 :=
  4963 * T ^ 15 + 3047 * T ^ 14 + 2192 * T ^ 13 +
    717 * T ^ 12 + 4346 * T ^ 11 - 2338 * T ^ 10 -
    2451 * T ^ 9 - 3181 * T ^ 8 - 2451 * T ^ 7 -
    2338 * T ^ 6 + 4346 * T ^ 5 + 717 * T ^ 4 +
    2192 * T ^ 3 + 3047 * T ^ 2 + 4963 * T - 3686

/-- Exact coprimality certificate for the two adjacent-root polynomials. -/
theorem adjacencyBezoutIdentity (T : ZMod 11057) :
    adjacencyBezoutLeft T * (T ^ 16 - 1) +
        adjacencyBezoutRight T * ((T + 1) ^ 16 - 1) = 1 := by
  simp only [adjacencyBezoutLeft, adjacencyBezoutRight]
  ring_nf
  simp only [show (55285 : ZMod 11057) = 0 by decide,
    show (364881 : ZMod 11057) = 0 by decide,
    show (1415296 : ZMod 11057) = 0 by decide,
    show (3527183 : ZMod 11057) = 0 by decide,
    show (5086220 : ZMod 11057) = 0 by decide,
    show (906674 : ZMod 11057) = 0 by decide,
    show (15756225 : ZMod 11057) = 0 by decide,
    show (46726882 : ZMod 11057) = 0 by decide,
    show (83502464 : ZMod 11057) = 0 by decide,
    show (110227233 : ZMod 11057) = 0 by decide,
    show (112936198 : ZMod 11057) = 0 by decide,
    show (86587367 : ZMod 11057) = 0 by decide,
    show (36465986 : ZMod 11057) = 0 by decide,
    show (23087016 : ZMod 11057) = 0 by decide,
    show (71726759 : ZMod 11057) = 0 by decide,
    show (90545773 : ZMod 11057) = 0 by decide,
    show (71671474 : ZMod 11057) = 0 by decide,
    show (22644736 : ZMod 11057) = 0 by decide,
    show (38522588 : ZMod 11057) = 0 by decide,
    show (93298966 : ZMod 11057) = 0 by decide,
    show (129035190 : ZMod 11057) = 0 by decide,
    show (139738366 : ZMod 11057) = 0 by decide,
    show (125673862 : ZMod 11057) = 0 by decide,
    show (94172469 : ZMod 11057) = 0 by decide,
    show (57927623 : ZMod 11057) = 0 by decide,
    show (28604459 : ZMod 11057) = 0 by decide,
    show (11012772 : ZMod 11057) = 0 by decide,
    show (3184416 : ZMod 11057) = 0 by decide,
    show (641306 : ZMod 11057) = 0 by decide,
    show (77399 : ZMod 11057) = 0 by decide,
    mul_zero, sub_zero, add_zero]

/-- Every nonzero `691`st power modulo `11057` lies in the subgroup of
sixteenth roots of unity recorded by the source certificate. -/
theorem pow_691_pow_sixteen_eq_one {x : ZMod 11057} (hx : x ≠ 0) :
    (x ^ 691) ^ 16 = 1 := by
  letI : Fact (Nat.Prime 11057) := ⟨prime_11057⟩
  calc
    (x ^ 691) ^ 16 = x ^ (691 * 16) := (pow_mul x 691 16).symm
    _ = x ^ 11056 := by norm_num
    _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx

/-- No two nonzero `691`st powers modulo `11057` differ by one. -/
theorem noConsecutivePowers_691_11057 : NoConsecutivePowers 691 11057 := by
  intro x y hx hy hxy
  have hxroot := pow_691_pow_sixteen_eq_one hx
  have hyroot := pow_691_pow_sixteen_eq_one hy
  have hnext : (y ^ 691 + 1) ^ 16 = 1 := by
    rw [add_comm, ← hxy]
    exact hxroot
  have hbezout := adjacencyBezoutIdentity (y ^ 691)
  rw [hyroot, hnext] at hbezout
  exact (by decide : (0 : ZMod 11057) ≠ 1) (by simpa using hbezout)

/-- The numerical obstruction for Sophie Germain's second residue
condition. -/
theorem sixHundredNinetyOne_pow_sixteen_mod_11057 :
    (691 : ZMod 11057) ^ 16 = 10803 := by
  decide

/-- The exponent `691` is not itself a `691`st-power residue modulo
`11057`. -/
theorem exponentNotPower_691_11057 : ExponentNotPower 691 11057 := by
  intro x hxpow
  letI : Fact (Nat.Prime 11057) := ⟨prime_11057⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 11057) ≠ 691) (by simpa using hxpow)
  have hfermat : x ^ 11056 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 11057 ↦ t ^ 16) hxpow
  have heq : x ^ 11056 = (691 : ZMod 11057) ^ 16 := by
    calc
      x ^ 11056 = x ^ (691 * 16) := by norm_num
      _ = (x ^ 691) ^ 16 := pow_mul x 691 16
      _ = (691 : ZMod 11057) ^ 16 := hraise
  have hbad : (10803 : ZMod 11057) = 1 := by
    rw [← sixHundredNinetyOne_pow_sixteen_mod_11057, ← heq, hfermat]
  exact (by decide : (10803 : ZMod 11057) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `691`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 691 + y ^ 691 = z ^ 691) :
    (691 : ℤ) ∣ x ∨ (691 : ℤ) ∣ y ∨ (691 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_691 (by norm_num) prime_11057
    noConsecutivePowers_691_11057 exponentNotPower_691_11057
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 691 + y ^ 691 = z ^ 691)
    (hx : ¬(691 : ℤ) ∣ x) (hy : ¬(691 : ℤ) ∣ y)
    (hz : ¬(691 : ℤ) ∣ z) : False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.SixHundredNinetyOne
