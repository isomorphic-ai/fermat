import Fermat.Seven.Lebesgue.FinalCoprimality
import Fermat.Seven.Lebesgue.FinalSubstitution
import Fermat.Seven.Lebesgue.PowerAllocation
import Fermat.Seven.Lebesgue.Primitive
import Fermat.Seven.Lebesgue.Reduction

/-!
# Lebesgue's Theorem II for exponent seven

This file joins the pieces of Lebesgue's 1840 proof.  A primitive ternary
solution gives the coprime product equation `s ^ 7 = 7 * v * t`.  The power
allocation produces the four equations on p. 279, the final substitution
turns them into the family of Theorem I, and the corrected descent rules out
that family.
-/

namespace Fermat.Seven.Lebesgue

private theorem even_v_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) : Even (v x y z) := by
  rcases exactly_one_even_of_ternary hxy hxz hyz heq with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hyzEven : Even (y + z) := hy.add_odd hz
    simpa only [v] using hyzEven.mul_left ((x + y) * (x + z))
  · have hxzEven : Even (x + z) := hx.add_odd hz
    exact (hxzEven.mul_left (x + y)).mul_right (y + z)
  · have hxyEven : Even (x + y) := hx.add_odd hy
    exact (hxyEven.mul_right (x + z)).mul_right (y + z)

/-- Lebesgue's Theorem II: every primitive signed solution has a zero entry. -/
theorem ternaryOnlyTrivial_lebesgue : TernaryOnlyTrivial := by
  intro x y z hxy hxz hyz heq
  by_contra hxyz
  have hpow := s_pow_seven_eq_seven_mul_v_t_of_ternary heq
  have htxyz := isCoprime_t_xyz_of_ternary hxy hxz hyz heq
  have htv := isCoprime_t_v_of_ternary hxy hxz hyz heq
  have htmod := t_modEq_one_mod_four_of_ternary hxy hxz hyz heq
  have hveven := even_v_of_ternary hxy hxz hyz heq
  obtain ⟨p, q, r, htq, hur, hvp, hspq, hpEven, hpq, hpr, hqr⟩ :=
    exists_pairwise_power_data_of_symmetric hxy hxz hpow htxyz htv htmod hveven
  have huOdd := odd_u_of_ternary hxy hxz hyz heq
  rw [hur] at huOdd
  have hqOdd : Odd q := (Int.odd_mul.mp huOdd).1
  have hrOdd : Odd r := (Int.odd_mul.mp huOdd).2
  have hp0 : p ≠ 0 := p_ne_zero_of_ternary_v_data hxyz heq hvp
  obtain ⟨a, P, Q, R, ha, hPodd, hQodd, hRodd, hPQ, hPR, hQR, hdesc⟩ :=
    exists_descentEquation_of_power_data htq hur hvp hspq hpEven hp0
      hqOdd hrOdd hpq hpr hqr
  exact descentEquation_impossible ha hPodd hQodd hRodd hPQ hPR hQR hdesc

/-- Fermat's Last Theorem for exponent seven, by Lebesgue's corrected 1840
proof. -/
theorem holdsAt_seven_lebesgue : Fermat.HoldsAt 7 :=
  holdsAt_seven_of_ternaryOnlyTrivial ternaryOnlyTrivial_lebesgue

end Fermat.Seven.Lebesgue
