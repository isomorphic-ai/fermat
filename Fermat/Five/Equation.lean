import Fermat.Five.Modular

/-!
# The generalized fifth-power equation used by Dirichlet

After the historical modulo-`25` preliminary, whichever member is divisible
by `5` is moved to the right.  This produces

`x^5 + y^5 = 5^5 z^5`,

where one of `x,y` may be negative.  Dirichlet's completed memoir proves that
this equation has no primitive nonzero solution by two parity descents.
-/

namespace Fermat.Five.Dirichlet

/-- The specialization `A = 1`, `n = 5` of Dirichlet's generalized equation. -/
def FifthEquation (x y z : ℤ) : Prop :=
  x * y * z ≠ 0 ∧ IsCoprime x y ∧ x ^ 5 + y ^ 5 = 5 ^ 5 * z ^ 5

theorem FifthEquation.ne_zero {x y z : ℤ} (h : FifthEquation x y z) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  rcases h.1 with hxyz
  exact ⟨fun hx ↦ hxyz (by simp [hx]), fun hy ↦ hxyz (by simp [hy]),
    fun hz ↦ hxyz (by simp [hz])⟩

/-- A primitive Fermat equation yields Dirichlet's generalized equation,
regardless of which of its three entries is divisible by `5`. -/
theorem exists_fifthEquation_of_pairwise
    {a b c : ℤ} (hnonzero : a * b * c ≠ 0)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (heq : a ^ 5 + b ^ 5 = c ^ 5) :
    ∃ x y z : ℤ, FifthEquation x y z := by
  have ha0 : a ≠ 0 := fun ha ↦ hnonzero (by simp [ha])
  have hb0 : b ≠ 0 := fun hb ↦ hnonzero (by simp [hb])
  have hc0 : c ≠ 0 := fun hc ↦ hnonzero (by simp [hc])
  rcases Fermat.Five.five_dvd_one_of_fifth_add_fifth heq with ha | hb | hc
  · obtain ⟨z, rfl⟩ := ha
    have hz0 : z ≠ 0 := by
      intro hz
      apply ha0
      simp [hz]
    refine ⟨c, -b, z, ?_, hbc.symm.neg_right, ?_⟩
    · exact mul_ne_zero (mul_ne_zero hc0 (neg_ne_zero.mpr hb0)) hz0
    · rw [(show Odd 5 by norm_num).neg_pow b]
      calc
        c ^ 5 - b ^ 5 = (5 * z) ^ 5 := by omega
        _ = 5 ^ 5 * z ^ 5 := by ring
  · obtain ⟨z, rfl⟩ := hb
    have hz0 : z ≠ 0 := by
      intro hz
      apply hb0
      simp [hz]
    refine ⟨c, -a, z, ?_, hac.symm.neg_right, ?_⟩
    · exact mul_ne_zero (mul_ne_zero hc0 (neg_ne_zero.mpr ha0)) hz0
    · rw [(show Odd 5 by norm_num).neg_pow a]
      calc
        c ^ 5 - a ^ 5 = (5 * z) ^ 5 := by omega
        _ = 5 ^ 5 * z ^ 5 := by ring
  · obtain ⟨z, rfl⟩ := hc
    have hz0 : z ≠ 0 := by
      intro hz
      apply hc0
      simp [hz]
    refine ⟨a, b, z, ?_, hab, ?_⟩
    · exact mul_ne_zero (mul_ne_zero ha0 hb0) hz0
    · calc
        a ^ 5 + b ^ 5 = (5 * z) ^ 5 := heq
        _ = 5 ^ 5 * z ^ 5 := by ring

end Fermat.Five.Dirichlet
