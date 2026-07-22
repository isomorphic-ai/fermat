import Fermat.Basic

/-!
# Splitting fifth powers between coprime integer factors

The two descents in Dirichlet's memoir repeatedly use unique factorization in
`ℤ`.  Because the relevant exponent is odd, the possible unit `-1` can be
absorbed into the base of a fifth power.
-/

namespace Fermat.Five

/-- An integer associated to an odd power is itself an odd power. -/
theorem exists_pow_eq_of_associated_pow {a d : ℤ} {k : ℕ}
    (hk : Odd k) (h : Associated a (d ^ k)) : ∃ e : ℤ, a = e ^ k := by
  obtain ⟨u, hu⟩ := h
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨d, by simpa using hu⟩
  · refine ⟨-d, ?_⟩
    rw [hk.neg_pow]
    have : a = -(d ^ k) := by simpa using congrArg Neg.neg hu
    exact this

/-- A factor coprime to its complement in a product which is an odd power is
an odd power itself. -/
theorem exists_pow_eq_of_mul_eq_pow_left {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Odd k) (heq : a * b = c ^ k) :
    ∃ d : ℤ, a = d ^ k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab heq
  exact exists_pow_eq_of_associated_pow hk hd.symm

theorem exists_pow_eq_of_mul_eq_pow_right {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Odd k) (heq : a * b = c ^ k) :
    ∃ d : ℤ, b = d ^ k := by
  rw [mul_comm] at heq
  exact exists_pow_eq_of_mul_eq_pow_left hab.symm hk heq

/-- Both members of a coprime two-factor product are odd powers when their
product is. -/
theorem exists_two_pow_eq_of_mul_eq_pow {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Odd k) (heq : a * b = c ^ k) :
    ∃ d e : ℤ, a = d ^ k ∧ b = e ^ k := by
  obtain ⟨d, hd⟩ := exists_pow_eq_of_mul_eq_pow_left hab hk heq
  obtain ⟨e, he⟩ := exists_pow_eq_of_mul_eq_pow_right hab hk heq
  exact ⟨d, e, hd, he⟩

end Fermat.Five
