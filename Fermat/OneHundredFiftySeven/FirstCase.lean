import Fermat.SophieGermain

/-!
# The first case for exponent 157

The auxiliary prime is `1571 = 10 * 157 + 1`.  Rather than enumerate all
1571 residues, this file records a short Bézout certificate for the two
degree-ten image equations.  If two nonzero 157th powers were consecutive,
some `t : ZMod 1571` would satisfy both `t ^ 10 = 1` and
`(t + 1) ^ 10 = 1`; the displayed polynomial identity makes that
impossible.

The second Sophie-Germain condition follows from
`157 ^ 10 = 1221 ≠ 1 (mod 1571)`.
-/

namespace Fermat.OneHundredFiftySeven

open Fermat.SophieGermain

theorem prime_157 : Nat.Prime 157 := by norm_num

theorem prime_1571 : Nat.Prime 1571 := by norm_num

/-- The traditional auxiliary-prime relation for exponent 157. -/
theorem auxiliaryPrimeRelation : 1571 = 10 * 157 + 1 := by norm_num

private def bezoutLeft (t : ZMod 1571) : ZMod 1571 :=
  528 * t ^ 9 + 303 * t ^ 8 + 267 * t ^ 7 - 744 * t ^ 6 -
    151 * t ^ 5 - 120 * t ^ 4 - 737 * t ^ 3 - 582 * t ^ 2 - 527 * t - 1

private def bezoutRight (t : ZMod 1571) : ZMod 1571 :=
  -528 * t ^ 9 + 264 * t ^ 8 + 430 * t ^ 7 - 777 * t ^ 6 +
    218 * t ^ 5 - 777 * t ^ 4 + 430 * t ^ 3 + 264 * t ^ 2 - 528 * t - 524

/-- Bézout identity for `T^10 - 1` and `(T + 1)^10 - 1` over
`ZMod 1571`. -/
private theorem bezout_identity (t : ZMod 1571) :
    bezoutLeft t * (t ^ 10 - 1) +
      bezoutRight t * ((t + 1) ^ 10 - 1) = 1 := by
  simp only [bezoutLeft, bezoutRight]
  ring_nf
  simp only [show (4713 : ZMod 1571) = 0 by decide,
    show (28278 : ZMod 1571) = 0 by decide,
    show (83263 : ZMod 1571) = 0 by decide,
    show (157100 : ZMod 1571) = 0 by decide,
    show (199517 : ZMod 1571) = 0 by decide,
    show (168097 : ZMod 1571) = 0 by decide,
    show (108399 : ZMod 1571) = 0 by decide,
    show (91118 : ZMod 1571) = 0 by decide,
    show (128822 : ZMod 1571) = 0 by decide,
    show (155529 : ZMod 1571) = 0 by decide,
    show (124109 : ZMod 1571) = 0 by decide,
    show (67553 : ZMod 1571) = 0 by decide,
    show (45559 : ZMod 1571) = 0 by decide,
    show (59698 : ZMod 1571) = 0 by decide,
    show (48701 : ZMod 1571) = 0 by decide,
    show (20423 : ZMod 1571) = 0 by decide,
    mul_zero, sub_zero]

/-- No two nonzero 157th powers modulo 1571 differ by one. -/
theorem noConsecutivePowers_157_1571 : NoConsecutivePowers 157 1571 := by
  change ∀ x y : ZMod 1571, x ≠ 0 → y ≠ 0 → x ^ 157 ≠ 1 + y ^ 157
  letI : Fact (Nat.Prime 1571) := ⟨prime_1571⟩
  intro x y hx hy hxy
  have hxfermat : x ^ 1570 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx
  have hyfermat : y ^ 1570 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hy
  have hy10 : (y ^ 157) ^ 10 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hyfermat
  have hxy10 : (1 + y ^ 157) ^ 10 = 1 := by
    rw [← hxy, ← pow_mul]
    norm_num
    exact hxfermat
  have hzero : (0 : ZMod 1571) = 1 := by
    calc
      0 = bezoutLeft (y ^ 157) * ((y ^ 157) ^ 10 - 1) +
          bezoutRight (y ^ 157) * (((y ^ 157) + 1) ^ 10 - 1) := by
            rw [hy10]
            rw [add_comm (y ^ 157) 1, hxy10]
            ring
      _ = 1 := bezout_identity (y ^ 157)
  exact zero_ne_one hzero

/-- The compact numerical witness for Sophie Germain's second residue
condition. -/
theorem oneHundredFiftySeven_pow_ten_mod_1571 :
    (157 : ZMod 1571) ^ 10 = 1221 := by decide

/-- The exponent 157 is not itself a 157th power modulo 1571. -/
theorem exponentNotPower_157_1571 : ExponentNotPower 157 1571 := by
  change ∀ x : ZMod 1571, x ^ 157 ≠ (157 : ZMod 1571)
  letI : Fact (Nat.Prime 1571) := ⟨prime_1571⟩
  intro x hxpow
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 1571) ≠ 157) (by simpa using hxpow)
  have hfermat : x ^ 1570 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise : (x ^ 157) ^ 10 = (157 : ZMod 1571) ^ 10 :=
    congrArg (fun t : ZMod 1571 ↦ t ^ 10) hxpow
  have heq : x ^ 1570 = (157 : ZMod 1571) ^ 10 := by
    calc
      x ^ 1570 = (x ^ 157) ^ 10 := by rw [← pow_mul]
      _ = (157 : ZMod 1571) ^ 10 := hraise
  have hbad : (1221 : ZMod 1571) = 1 := by
    rw [← oneHundredFiftySeven_pow_ten_mod_1571, ← heq, hfermat]
  exact (by decide : (1221 : ZMod 1571) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent 157. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 157 + y ^ 157 = z ^ 157) :
    (157 : ℤ) ∣ x ∨ (157 : ℤ) ∣ y ∨ (157 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_157 (by norm_num) prime_1571
    noConsecutivePowers_157_1571 exponentNotPower_157_1571
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 157 + y ^ 157 = z ^ 157)
    (hx : ¬(157 : ℤ) ∣ x) (hy : ¬(157 : ℤ) ∣ y) (hz : ¬(157 : ℤ) ∣ z) :
    False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.OneHundredFiftySeven
