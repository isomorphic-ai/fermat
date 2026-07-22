import Fermat.Seven.Lebesgue.Symmetric

/-!
# Nonvanishing in Lebesgue's final substitution

The power-allocation step writes Lebesgue's product `v` as
`7 ^ 6 * p ^ 7`.  The final substitution also needs `p ≠ 0`.  This follows
directly from the nonzero ternary equation: if `p = 0`, one of the pairwise
sums in `v = (x + y)(x + z)(y + z)` vanishes, and the Fermat equation then
forces the remaining variable to vanish.
-/

namespace Fermat.Seven.Lebesgue

/-- The parameter `p` extracted from Lebesgue's factor `v` is nonzero for a
nonzero ternary solution. -/
theorem p_ne_zero_of_ternary_v_data
    {x y z p : ℤ}
    (hxyz : x * y * z ≠ 0)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0)
    (hvp : v x y z = 7 ^ 6 * p ^ 7) :
    p ≠ 0 := by
  intro hp
  have hv0 : v x y z = 0 := by
    calc
      v x y z = 7 ^ 6 * p ^ 7 := hvp
      _ = 0 := by rw [hp]; norm_num
  have hfactor : (x + y) * (x + z) = 0 ∨ y + z = 0 := by
    apply mul_eq_zero.mp
    simpa only [v] using hv0
  rcases hfactor with hleft | hyz
  · rcases mul_eq_zero.mp hleft with hxy | hxz
    · have hy : y = -x := by omega
      have hzPow : z ^ 7 = 0 := by
        rw [hy] at heq
        nlinarith
      have hz : z = 0 := eq_zero_of_pow_eq_zero hzPow
      exact hxyz (by simp [hz])
    · have hz : z = -x := by omega
      have hyPow : y ^ 7 = 0 := by
        rw [hz] at heq
        nlinarith
      have hy : y = 0 := eq_zero_of_pow_eq_zero hyPow
      exact hxyz (by simp [hy])
  · have hz : z = -y := by omega
    have hxPow : x ^ 7 = 0 := by
      rw [hz] at heq
      nlinarith
    have hx : x = 0 := eq_zero_of_pow_eq_zero hxPow
    exact hxyz (by simp [hx])

end Fermat.Seven.Lebesgue
