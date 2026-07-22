import Fermat.Basic

/-!
# The modulo-25 entry to the historical proof for exponent five

Legendre's 1827 proof starts from the fact that one member of a primitive
solution is divisible by `5` (he cites the stronger `25`-divisibility result
proved earlier using Sophie Germain's auxiliary-prime argument).  Dirichlet's
completed 1828 descent only needs the weaker assertion.  For exponent five it
is the following finite calculation modulo `25`.
-/

namespace Fermat.Five

private theorem zmod_twentyFive_entry :
    ∀ a b c : ZMod 25, a ^ 5 + b ^ 5 + c ^ 5 = 0 →
      ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) a = 0 ∨
      ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) b = 0 ∨
      ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) c = 0 := by
  decide

/-- In any integral relation among three fifth powers, one of the three
bases is divisible by `5`.  This is the precise part of the historical
preliminary result used by Dirichlet's final reduction. -/
theorem five_dvd_one_of_sum_fifth {a b c : ℤ}
    (h : a ^ 5 + b ^ 5 + c ^ 5 = 0) :
    (5 : ℤ) ∣ a ∨ (5 : ℤ) ∣ b ∨ (5 : ℤ) ∣ c := by
  have h25 : (a : ZMod 25) ^ 5 + (b : ZMod 25) ^ 5 + (c : ZMod 25) ^ 5 = 0 := by
    have := congrArg (fun z : ℤ ↦ (z : ZMod 25)) h
    simpa using this
  rcases zmod_twentyFive_entry (a : ZMod 25) (b : ZMod 25) (c : ZMod 25) h25 with
    ha | hb | hc
  · left
    rw [ZMod.castHom_apply] at ha
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp (by simpa using ha)
  · right; left
    rw [ZMod.castHom_apply] at hb
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp (by simpa using hb)
  · right; right
    rw [ZMod.castHom_apply] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp (by simpa using hc)

/-- The two-variable form used when a Fermat equation is written with one
term on the other side. -/
theorem five_dvd_one_of_fifth_add_fifth {a b c : ℤ}
    (h : a ^ 5 + b ^ 5 = c ^ 5) :
    (5 : ℤ) ∣ a ∨ (5 : ℤ) ∣ b ∨ (5 : ℤ) ∣ c := by
  have hsum : a ^ 5 + b ^ 5 + (-c) ^ 5 = 0 := by
    rw [(show Odd 5 by norm_num).neg_pow c]
    omega
  rcases five_dvd_one_of_sum_fifth hsum with ha | hb | hc
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr (dvd_neg.mp hc))

end Fermat.Five
