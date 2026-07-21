import Fermat.Fourteen.Dirichlet

/-!
# Splitting even powers between coprime integer factors

Dirichlet repeatedly uses unique factorization in `ℤ`.  The lemmas here keep
the unavoidable sign of an even power visible by stating the result with an
absolute value.
-/

namespace Fermat.Fourteen.Dirichlet

/-- A factor of a `k`-th power which is coprime to the complementary factor
is, up to sign, a `k`-th power.  For even `k` the sign is exactly removed by
absolute value. -/
theorem exists_pow_eq_abs_of_mul_eq_pow_left {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Even k) (heq : a * b = c ^ k) :
    ∃ d : ℤ, |a| = d ^ k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab heq
  obtain ⟨u, hu⟩ := hd
  refine ⟨d, ?_⟩
  rw [← hu]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hk.pow_abs d
  · simpa using hk.pow_abs d

theorem exists_pow_eq_abs_of_mul_eq_pow_right {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Even k) (heq : a * b = c ^ k) :
    ∃ d : ℤ, |b| = d ^ k := by
  rw [mul_comm] at heq
  exact exists_pow_eq_abs_of_mul_eq_pow_left hab.symm hk heq

/-- Associated powers are the convenient sign-insensitive form used after
one distinguished prime-power factor has been cancelled. -/
theorem exists_pow_eq_abs_of_associated_pow_mul_left {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Even k) (heq : Associated (c ^ k) (a * b)) :
    ∃ d : ℤ, |a| = d ^ k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_associated_pow_mul hab heq
  obtain ⟨u, hu⟩ := hd
  refine ⟨d, ?_⟩
  rw [← hu]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hk.pow_abs d
  · simpa using hk.pow_abs d

theorem exists_pow_eq_abs_of_associated_pow_mul_right {a b c : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hk : Even k) (heq : Associated (c ^ k) (a * b)) :
    ∃ d : ℤ, |b| = d ^ k := by
  apply exists_pow_eq_abs_of_associated_pow_mul_left hab.symm hk
  simpa only [mul_comm] using heq

/-- Two selected factors in a product of three pairwise-coprime integers are
absolute `k`-th powers, provided the whole product is associated to one. -/
theorem exists_two_pow_eq_abs_of_associated_pow_three
    {a b c w : ℤ} {k : ℕ}
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c)
    (hk : Even k) (heq : Associated (w ^ k) (a * b * c)) :
    ∃ x y : ℤ, |b| = x ^ k ∧ |c| = y ^ k := by
  have hb_ac : IsCoprime b (a * c) := hab.symm.mul_right hbc
  have hc_ab : IsCoprime c (a * b) := hac.symm.mul_right hbc.symm
  obtain ⟨x, hx⟩ := exists_pow_eq_abs_of_associated_pow_mul_left hb_ac hk <| by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using heq
  obtain ⟨y, hy⟩ := exists_pow_eq_abs_of_associated_pow_mul_left hc_ab hk <| by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using heq
  exact ⟨x, y, hx, hy⟩

end Fermat.Fourteen.Dirichlet
