import Fermat.SophieGermain

/-!
# The first case for exponent 37

The auxiliary prime is `149 = 4 * 37 + 1`.  The nonzero 37th-power
residues modulo 149 are exactly `1, 44, 105, 148`; no two differ by one.
The second residue condition is witnessed by `37 ^ 4 = 39` modulo 149.
-/

namespace Fermat.ThirtySeven

open Fermat.SophieGermain

/-- The exact auxiliary-prime residue list supplied by the proof package. -/
theorem powerResidues_149 :
    ∀ x : ZMod 149, x ≠ 0 →
      ((∃ y : ZMod 149, y ^ 37 = x) ↔ x = 1 ∨ x = 44 ∨ x = 105 ∨ x = 148) := by
  set_option maxRecDepth 100000 in decide

/-- No two nonzero 37th powers modulo 149 differ by one. -/
theorem noConsecutivePowers_37_149 : NoConsecutivePowers 37 149 := by
  change ∀ x y : ZMod 149, x ≠ 0 → y ≠ 0 → x ^ 37 ≠ 1 + y ^ 37
  set_option maxRecDepth 100000 in decide

/-- The short numerical witness used to show that 37 is not a 37th power
modulo 149. -/
theorem thirtySeven_pow_four_mod_149 : (37 : ZMod 149) ^ 4 = 39 := by
  decide

/-- The exponent 37 is not a 37th-power residue modulo 149. -/
theorem exponentNotPower_37_149 : ExponentNotPower 37 149 := by
  change ∀ x : ZMod 149, x ^ 37 ≠ (37 : ZMod 149)
  letI : Fact (Nat.Prime 149) := ⟨by norm_num⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    exact (by decide : (0 : ZMod 149) ^ 37 ≠ 37) hx
  have hfermat : x ^ 148 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hx0
  have hraise := congrArg (fun t : ZMod 149 ↦ t ^ 4) hx
  have heq : x ^ 148 = (37 : ZMod 149) ^ 4 := by
    simpa [← pow_mul] using hraise
  have : (39 : ZMod 149) = 1 := by
    rw [← thirtySeven_pow_four_mod_149, ← heq, hfermat]
  exact (by decide : (39 : ZMod 149) ≠ 1) this

/-- Sophie Germain's first-case conclusion at exponent 37.  Any primitive
integral solution must have one of its entries divisible by 37. -/
theorem firstCase_of_pairwise_coprime {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 37 + y ^ 37 = z ^ 37) :
    (37 : ℤ) ∣ x ∨ (37 : ℤ) ∣ y ∨ (37 : ℤ) ∣ z := by
  exact Fermat.SophieGermain.firstCase_of_pairwise_coprime
    (by norm_num) (by norm_num) (by norm_num)
    noConsecutivePowers_37_149 exponentNotPower_37_149
    hxy hyz hxz hfermat

/-- Contradiction form of `firstCase_of_pairwise_coprime`. -/
theorem firstCaseImpossible {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ 37 + y ^ 37 = z ^ 37)
    (hx : ¬(37 : ℤ) ∣ x) (hy : ¬(37 : ℤ) ∣ y) (hz : ¬(37 : ℤ) ∣ z) :
    False := by
  rcases firstCase_of_pairwise_coprime hxy hyz hxz hfermat with hx' | hy' | hz'
  · exact hx hx'
  · exact hy hy'
  · exact hz hz'

end Fermat.ThirtySeven
