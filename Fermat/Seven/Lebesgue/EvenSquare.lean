import Mathlib

/-!
# The odd part of an even square

Lebesgue's final substitution writes the square of an even integer as a
positive power of two times an odd square.  This file isolates that elementary
normalization from the descent itself.
-/

namespace Fermat.Seven.Lebesgue

/-- Natural-number form of the even-square normalization. -/
theorem exists_even_square_decomposition_nat {p : ℕ} (hp : Even p) (hp0 : p ≠ 0) :
    ∃ a R : ℕ, 0 < a ∧ Odd R ∧ p ^ 2 = 2 ^ (a + 1) * R := by
  obtain ⟨e, m, hm, hpm⟩ := Nat.exists_eq_two_pow_mul_odd hp0
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    subst e
    simp only [pow_zero, one_mul] at hpm
    rw [hpm] at hp
    exact (Nat.not_even_iff_odd.mpr hm) hp
  refine ⟨2 * e - 1, m ^ 2, by omega, hm.pow, ?_⟩
  calc
    p ^ 2 = (2 ^ e * m) ^ 2 := by rw [hpm]
    _ = 2 ^ (2 * e) * m ^ 2 := by
      rw [show 2 * e = e * 2 by omega, pow_mul]
      ring
    _ = 2 ^ (2 * e - 1 + 1) * m ^ 2 := by
      congr 2
      omega

/-- Every nonzero even integer square is `2^(a+1)` times an odd integer,
with `a>0`.  The odd factor returned here is itself a square.
-/
theorem exists_even_square_decomposition {p : ℤ} (hp : Even p) (hp0 : p ≠ 0) :
    ∃ a : ℕ, ∃ R : ℤ, 0 < a ∧ Odd R ∧ p ^ 2 = 2 ^ (a + 1) * R := by
  have hnat0 : p.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hp0
  have hnatEven : Even p.natAbs := Int.natAbs_even.mpr hp
  obtain ⟨a, R, ha, hRodd, hsq⟩ :=
    exists_even_square_decomposition_nat hnatEven hnat0
  refine ⟨a, (R : ℤ), ha, by exact_mod_cast hRodd, ?_⟩
  calc
    p ^ 2 = |p| ^ 2 := (show Even 2 by norm_num).pow_abs p |>.symm
    _ = (p.natAbs : ℤ) ^ 2 := by rw [Int.natCast_natAbs]
    _ = (2 : ℤ) ^ (a + 1) * R := by exact_mod_cast hsq

/-- The odd factor can be chosen coprime to every integer already coprime to
the original even integer. -/
theorem exists_even_square_decomposition_coprime {p q : ℤ} (hp : Even p)
    (hp0 : p ≠ 0) (hpq : IsCoprime p q) :
    ∃ a : ℕ, ∃ R : ℤ,
      0 < a ∧ Odd R ∧ p ^ 2 = 2 ^ (a + 1) * R ∧ IsCoprime R q := by
  have hnat0 : p.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hp0
  have hnatEven : Even p.natAbs := Int.natAbs_even.mpr hp
  obtain ⟨e, m, hm, hpm⟩ := Nat.exists_eq_two_pow_mul_odd hnat0
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    subst e
    simp only [pow_zero, one_mul] at hpm
    rw [hpm] at hnatEven
    exact (Nat.not_even_iff_odd.mpr hm) hnatEven
  have hmDvd : m ∣ p.natAbs := ⟨2 ^ e, by rw [hpm]; ring⟩
  have hpqNat : p.natAbs.Coprime q.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hpq
  have hmCoprime : (m ^ 2).Coprime q.natAbs :=
    (Nat.Coprime.of_dvd_left hmDvd hpqNat).pow_left 2
  have hsq : p.natAbs ^ 2 = 2 ^ (2 * e - 1 + 1) * m ^ 2 := by
    calc
      p.natAbs ^ 2 = (2 ^ e * m) ^ 2 := by rw [hpm]
      _ = 2 ^ (2 * e) * m ^ 2 := by
        rw [show 2 * e = e * 2 by omega, pow_mul]
        ring
      _ = 2 ^ (2 * e - 1 + 1) * m ^ 2 := by
        congr 2
        omega
  refine ⟨2 * e - 1, (m ^ 2 : ℕ), by omega, by exact_mod_cast hm.pow, ?_, ?_⟩
  · calc
      p ^ 2 = |p| ^ 2 := (show Even 2 by norm_num).pow_abs p |>.symm
      _ = (p.natAbs : ℤ) ^ 2 := by rw [Int.natCast_natAbs]
      _ = (2 : ℤ) ^ (2 * e - 1 + 1) * (m ^ 2 : ℕ) := by exact_mod_cast hsq
  · apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hmCoprime

end Fermat.Seven.Lebesgue
