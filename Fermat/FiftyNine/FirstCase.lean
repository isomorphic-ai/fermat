import Fermat.SophieGermain

/-!
# The first case for exponent 59

The auxiliary prime is `827 = 14 * 59 + 1`.  Every nonzero `59`th power
modulo `827` is a fourteenth root of unity.  The explicit Bezout identity
below certifies that a fourteenth root and its successor cannot both be
fourteenth roots.  The second Sophie--Germain condition is the short
calculation `59 ^ 14 = 255 != 1 (mod 827)`.

Only the finite exponent-specific part is proved here.  The implication from
these two residue conditions to the first-case conclusion is the generic
theorem in `Fermat.SophieGermain`.
-/

namespace Fermat.FiftyNine

open Fermat.SophieGermain

theorem prime_59 : Nat.Prime 59 := by
  norm_num

theorem prime_827 : Nat.Prime 827 := by
  norm_num

/-- The traditional auxiliary-prime relation for exponent `59`. -/
theorem auxiliaryPrimeRelation : 827 = 14 * 59 + 1 := by
  norm_num

/-- Left coefficient in the polynomial Bezout certificate for
`T ^ 14 - 1` and `(T + 1) ^ 14 - 1` modulo `827`. -/
def adjacencyBezoutLeft (T : ZMod 827) : ZMod 827 :=
  60 * T ^ 13 - 17 * T ^ 12 + 156 * T ^ 11 + 252 * T ^ 10 -
    320 * T ^ 9 - 312 * T ^ 8 + 138 * T ^ 7 + 19 * T ^ 6 -
    344 * T ^ 5 - 412 * T ^ 4 + 352 * T ^ 3 - 319 * T ^ 2 +
    271 * T - 1

/-- Right coefficient in the polynomial Bezout certificate for
`T ^ 14 - 1` and `(T + 1) ^ 14 - 1` modulo `827`. -/
def adjacencyBezoutRight (T : ZMod 827) : ZMod 827 :=
  -60 * T ^ 13 + 30 * T ^ 12 - 78 * T ^ 11 + 102 * T ^ 10 -
    279 * T ^ 9 + 119 * T ^ 8 + 234 * T ^ 7 + 119 * T ^ 6 -
    279 * T ^ 5 + 102 * T ^ 4 - 78 * T ^ 3 + 30 * T ^ 2 -
    60 * T - 276

/-- Exact coprimality certificate for the two adjacent-root polynomials.
This is the compact form of the package's complete fourteen-residue check. -/
theorem adjacencyBezoutIdentity : ∀ T : ZMod 827,
    adjacencyBezoutLeft T * (T ^ 14 - 1) +
        adjacencyBezoutRight T * ((T + 1) ^ 14 - 1) = 1 := by
  set_option maxRecDepth 100000 in decide

/-- A nonzero `59`th power modulo `827` is a fourteenth root of unity. -/
theorem pow_59_pow_fourteen_eq_one {x : ZMod 827} (hx : x ≠ 0) :
    (x ^ 59) ^ 14 = 1 := by
  letI : Fact (Nat.Prime 827) := ⟨prime_827⟩
  calc
    (x ^ 59) ^ 14 = x ^ (59 * 14) := (pow_mul x 59 14).symm
    _ = x ^ 826 := by norm_num
    _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx

/-- No two nonzero `59`th powers modulo `827` differ by one. -/
theorem noConsecutivePowers_59_827 : NoConsecutivePowers 59 827 := by
  intro x y hx hy hxy
  have hxroot := pow_59_pow_fourteen_eq_one hx
  have hyroot := pow_59_pow_fourteen_eq_one hy
  have hnext : (y ^ 59 + 1) ^ 14 = 1 := by
    rw [add_comm, ← hxy]
    exact hxroot
  have hbezout := adjacencyBezoutIdentity (y ^ 59)
  rw [hyroot, hnext] at hbezout
  exact (by decide : (0 : ZMod 827) ≠ 1) (by simpa using hbezout)

/-- The numerical obstruction for the second Sophie--Germain residue
condition. -/
theorem fiftyNine_pow_fourteen_mod_827 :
    (59 : ZMod 827) ^ 14 = 255 := by
  decide

/-- The exponent `59` is not itself a `59`th-power residue modulo `827`. -/
theorem exponentNotPower_59_827 : ExponentNotPower 59 827 := by
  intro x hxpow
  letI : Fact (Nat.Prime 827) := ⟨prime_827⟩
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 827) ≠ 59) (by simpa using hxpow)
  have hfermat : x ^ 826 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 827 => t ^ 14) hxpow
  have heq : x ^ 826 = (59 : ZMod 827) ^ 14 := by
    calc
      x ^ 826 = x ^ (59 * 14) := by norm_num
      _ = (x ^ 59) ^ 14 := pow_mul x 59 14
      _ = (59 : ZMod 827) ^ 14 := hraise
  have hbad : (255 : ZMod 827) = 1 := by
    rw [← fiftyNine_pow_fourteen_mod_827, ← heq, hfermat]
  exact (by decide : (255 : ZMod 827) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `59`: every
primitive integral solution has an entry divisible by `59`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 59 + y ^ 59 = z ^ 59) :
    (59 : ℤ) ∣ x ∨ (59 : ℤ) ∣ y ∨ (59 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_59 (by norm_num) prime_827
    noConsecutivePowers_59_827 exponentNotPower_59_827
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 59 + y ^ 59 = z ^ 59)
    (hx : ¬(59 : ℤ) ∣ x) (hy : ¬(59 : ℤ) ∣ y) (hz : ¬(59 : ℤ) ∣ z) :
    False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.FiftyNine
