import Fermat.SophieGermain

/-!
# The first case for exponent 67

Sophie Germain's auxiliary prime is `269 = 4 * 67 + 1`.  Rather than
enumerating all pairs of residues, we use Fermat's little theorem to put
every nonzero `67`th power among the four fourth roots of unity
`{1, 82, 187, 268}`.  The sixteen possible pairs are then visibly not
consecutive.

For the second residue condition, raising a hypothetical equality
`x ^ 67 = 67` to the fourth power would give both `x ^ 268 = 1` and
`67 ^ 4 = 62` modulo `269`.
-/

namespace Fermat.SixtySeven

open Fermat.SophieGermain

theorem prime_67 : Nat.Prime 67 := by
  norm_num

theorem prime_269 : Nat.Prime 269 := by
  norm_num

/-- The traditional auxiliary-prime relation at exponent `67`. -/
theorem auxiliaryPrimeRelation : 269 = 4 * 67 + 1 := by
  norm_num

/-- The complete set of fourth roots of unity modulo `269`.  This is the
small residual computation left after Fermat's little theorem has compressed
the `67`th-power subgroup to order four. -/
theorem fourthRootsOfUnity_269 (u : ZMod 269) (hu : u ^ 4 = 1) :
    u = 1 ∨ u = 82 ∨ u = 187 ∨ u = 268 := by
  set_option maxRecDepth 100000 in
    revert u
    decide

/-- Every nonzero `67`th power modulo `269` is one of the four residues in
the package certificate. -/
theorem pow_67_eq_fourthRoot {x : ZMod 269} (hx : x ≠ 0) :
    x ^ 67 = 1 ∨ x ^ 67 = 82 ∨ x ^ 67 = 187 ∨ x ^ 67 = 268 := by
  letI : Fact (Nat.Prime 269) := ⟨prime_269⟩
  apply fourthRootsOfUnity_269
  calc
    (x ^ 67) ^ 4 = x ^ (67 * 4) := (pow_mul _ _ _).symm
    _ = x ^ 268 := by norm_num
    _ = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hx

private theorem certifiedRoots_not_consecutive
    {u v : ZMod 269}
    (hu : u = 1 ∨ u = 82 ∨ u = 187 ∨ u = 268)
    (hv : v = 1 ∨ v = 82 ∨ v = 187 ∨ v = 268) :
    u ≠ 1 + v := by
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;> decide

/-- No two nonzero `67`th powers modulo `269` differ by one. -/
theorem noConsecutivePowers_67_269 : NoConsecutivePowers 67 269 := by
  intro x y hx hy
  exact certifiedRoots_not_consecutive
    (pow_67_eq_fourthRoot hx) (pow_67_eq_fourthRoot hy)

/-- The short numerical obstruction in Sophie Germain's second residue
condition. -/
theorem sixtySeven_pow_four_mod_269 :
    (67 : ZMod 269) ^ 4 = 62 := by
  decide

/-- The exponent `67` is not itself a `67`th-power residue modulo `269`. -/
theorem exponentNotPower_67_269 : ExponentNotPower 67 269 := by
  change ∀ x : ZMod 269, x ^ 67 ≠ (67 : ZMod 269)
  letI : Fact (Nat.Prime 269) := ⟨prime_269⟩
  intro x hxpow
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact (by decide : (0 : ZMod 269) ≠ 67) (by simpa using hxpow)
  have hfermat : x ^ 268 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise : (x ^ 67) ^ 4 = (67 : ZMod 269) ^ 4 :=
    congrArg (fun t : ZMod 269 ↦ t ^ 4) hxpow
  have heq : x ^ 268 = (67 : ZMod 269) ^ 4 := by
    calc
      x ^ 268 = (x ^ 67) ^ 4 := by rw [← pow_mul]
      _ = (67 : ZMod 269) ^ 4 := hraise
  have hbad : (62 : ZMod 269) = 1 := by
    rw [← sixtySeven_pow_four_mod_269, ← heq, hfermat]
  exact (by decide : (62 : ZMod 269) ≠ 1) hbad

/-- Sophie Germain's first-case conclusion at exponent `67`: every
primitive integral solution has an entry divisible by `67`. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 67 + y ^ 67 = z ^ 67) :
    (67 : ℤ) ∣ x ∨ (67 : ℤ) ∣ y ∨ (67 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    prime_67 (by norm_num) prime_269
    noConsecutivePowers_67_269 exponentNotPower_67_269
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 67 + y ^ 67 = z ^ 67)
    (hx : ¬(67 : ℤ) ∣ x) (hy : ¬(67 : ℤ) ∣ y) (hz : ¬(67 : ℤ) ∣ z) :
    False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.SixtySeven
