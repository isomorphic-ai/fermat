import Fermat.SophieGermain

/-!
# The first case for exponent 491

Sophie Germain's auxiliary prime is `983 = 2 * 491 + 1`.  Fermat's
little theorem shows that every nonzero 491st power modulo 983 has square
one, so it is `1` or `-1`.  These two residues cannot be consecutive.

For the second residue condition, raising a hypothetical equality
`x ^ 491 = 491` to the second power would give both `x ^ 982 = 1` and
`491 ^ 2 = 246` modulo 983, a contradiction.
-/

namespace Fermat.FourHundredNinetyOne

open Fermat.SophieGermain

theorem prime_491 : Nat.Prime 491 := by
  norm_num

theorem prime_983 : Nat.Prime 983 := by
  norm_num

/-- The traditional auxiliary-prime relation for the exponent 491. -/
theorem auxiliaryPrimeRelation : 983 = 2 * 491 + 1 := by
  norm_num

/-- The nonzero 491st-power residues modulo 983 are contained in `{1, -1}`.
This is the order-two quotient behind the unusually short first-case
certificate. -/
theorem pow_491_eq_one_or_neg_one {x : ZMod 983} (hx : x ≠ 0) :
    x ^ 491 = 1 ∨ x ^ 491 = -1 := by
  letI : Fact (Nat.Prime 983) := ⟨prime_983⟩
  have hfermat : x ^ 982 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx
  apply (sq_eq_one_iff).mp
  calc
    (x ^ 491) ^ 2 = x ^ (491 * 2) := (pow_mul _ _ _).symm
    _ = x ^ 982 := by norm_num
    _ = 1 := hfermat

/-- No two nonzero 491st powers modulo the auxiliary prime 983 differ by
one.  Only the four pairs of signs supplied by
`pow_491_eq_one_or_neg_one` have to be excluded. -/
theorem noConsecutivePowers_491_983 : NoConsecutivePowers 491 983 := by
  change ∀ x y : ZMod 983, x ≠ 0 → y ≠ 0 → x ^ 491 ≠ 1 + y ^ 491
  intro x y hx hy hxy
  rcases pow_491_eq_one_or_neg_one hx with hxpow | hxpow
  · rcases pow_491_eq_one_or_neg_one hy with hypow | hypow
    · exact (by decide : (1 : ZMod 983) ≠ 1 + 1)
        (by simpa [hxpow, hypow] using hxy)
    · exact (by decide : (1 : ZMod 983) ≠ 1 + -1)
        (by simpa [hxpow, hypow] using hxy)
  · rcases pow_491_eq_one_or_neg_one hy with hypow | hypow
    · exact (by decide : (-1 : ZMod 983) ≠ 1 + 1)
        (by simpa [hxpow, hypow] using hxy)
    · exact (by decide : (-1 : ZMod 983) ≠ 1 + -1)
        (by simpa [hxpow, hypow] using hxy)

/-- The small numerical obstruction used for Sophie Germain's second
residue condition. -/
theorem fourHundredNinetyOne_sq_mod_983 :
    (491 : ZMod 983) ^ 2 = 246 := by
  decide

/-- The exponent 491 is not itself a 491st-power residue modulo 983. -/
theorem exponentNotPower_491_983 : ExponentNotPower 491 983 := by
  change ∀ x : ZMod 983, x ^ 491 ≠ (491 : ZMod 983)
  letI : Fact (Nat.Prime 983) := ⟨prime_983⟩
  intro x hxpow
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 983) ≠ 491) (by simpa using hxpow)
  have hfermat : x ^ 982 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise : (x ^ 491) ^ 2 = (491 : ZMod 983) ^ 2 :=
    congrArg (fun t : ZMod 983 ↦ t ^ 2) hxpow
  have heq : x ^ 982 = (491 : ZMod 983) ^ 2 := by
    calc
      x ^ 982 = (x ^ 491) ^ 2 := by rw [← pow_mul]
      _ = (491 : ZMod 983) ^ 2 := hraise
  have hbad : (246 : ZMod 983) = 1 := by
    rw [← fourHundredNinetyOne_sq_mod_983, ← heq, hfermat]
  exact (by decide : (246 : ZMod 983) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent 491: every
primitive integral solution has an entry divisible by 491. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 491 + y ^ 491 = z ^ 491) :
    (491 : ℤ) ∣ x ∨ (491 : ℤ) ∣ y ∨ (491 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_491 (by norm_num) prime_983
    noConsecutivePowers_491_983 exponentNotPower_491_983
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 491 + y ^ 491 = z ^ 491)
    (hx : ¬(491 : ℤ) ∣ x) (hy : ¬(491 : ℤ) ∣ y) (hz : ¬(491 : ℤ) ∣ z) :
    False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.FourHundredNinetyOne
