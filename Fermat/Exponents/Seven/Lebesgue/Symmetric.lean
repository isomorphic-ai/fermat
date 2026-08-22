import Mathlib

/-!
# Symmetric identities in Lebesgue's proof for exponent seven

This file records the algebraic starting point of Lebesgue's ternary proof.
The principal identity is the one displayed on p. 278 of the 1840 memoir.
No divisibility, valuation, or descent argument is included here.
-/

namespace Fermat.Seven.Lebesgue

/-- Lebesgue's sum `s = x + y + z`. -/
def s (x y z : ℤ) : ℤ := x + y + z

/-- Lebesgue's symmetric quadratic quantity. -/
def u (x y z : ℤ) : ℤ :=
  x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z

/-- Lebesgue's product of the three pairwise sums. -/
def v (x y z : ℤ) : ℤ := (x + y) * (x + z) * (y + z)

/-- The second factor in Lebesgue's seventh-power identity. -/
def t (x y z : ℤ) : ℤ := u x y z ^ 2 + x * y * z * s x y z

/-- The source relation expressing `u` through `s` and the second elementary
symmetric polynomial. -/
theorem u_eq_s_sq_sub (x y z : ℤ) :
    u x y z = s x y z ^ 2 - (x * y + x * z + y * z) := by
  simp only [u, s]
  ring

/-- The source relation expressing the product of pairwise sums through the
elementary symmetric polynomials. -/
theorem v_eq_s_mul_sub_xyz (x y z : ℤ) :
    v x y z = s x y z * (x * y + x * z + y * z) - x * y * z := by
  simp only [v, s]
  ring

/-- Lebesgue's exact symmetric identity from p. 278. -/
theorem seventh_power_identity (x y z : ℤ) :
    s x y z ^ 7 =
      x ^ 7 + y ^ 7 + z ^ 7 + 7 * v x y z * t x y z := by
  simp only [s, u, v, t]
  ring

/-- Under the ternary Fermat equation, Lebesgue's identity reduces to the
product equation that starts the arithmetic part of the proof. -/
theorem s_pow_seven_eq_seven_mul_v_t_of_ternary {x y z : ℤ}
    (h : x ^ 7 + y ^ 7 + z ^ 7 = 0) :
    s x y z ^ 7 = 7 * v x y z * t x y z := by
  rw [seventh_power_identity, h, zero_add]

end Fermat.Seven.Lebesgue
