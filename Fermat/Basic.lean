import Mathlib

/-!
# Fixed-exponent cases of Fermat's Last Theorem

This file fixes the common statement used by the classical proofs.  The
variables are integers, all three are required to be nonzero, and the exponent
is a natural number.
-/

namespace Fermat

/-- Fermat's Last Theorem for one fixed natural-number exponent. -/
def HoldsAt (n : ℕ) : Prop :=
  ∀ x y z : ℤ, x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem HoldsAt.mono_of_dvd {m n : ℕ} (hm : HoldsAt m) (hdiv : m ∣ n) : HoldsAt n := by
  obtain ⟨k, rfl⟩ := hdiv
  intro x y z hxyz hEq
  have hx : x ≠ 0 := by
    intro hx
    simp [hx] at hxyz
  have hy : y ≠ 0 := by
    intro hy
    simp [hy] at hxyz
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at hxyz
  apply hm (x ^ k) (y ^ k) (z ^ k)
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero k hx) (pow_ne_zero k hy)) (pow_ne_zero k hz)
  · have commute_pow (a : ℤ) : (a ^ k) ^ m = a ^ (m * k) := by
      rw [← pow_mul]
      rw [Nat.mul_comm]
    rw [commute_pow, commute_pow, commute_pow]
    exact hEq

end Fermat
