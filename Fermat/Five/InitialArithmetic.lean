import Fermat.Five.Descent

/-!
# Arithmetic at the entrance to Dirichlet's two fifth-power descents

After putting the factor divisible by `5` on the right and writing the sum
or difference in half-sum coordinates, both parity branches reach

`r * H(q,r) = 2^4 * 5^3 * z^5`,

where `H(q,r) = q^4 + 50q^2r^2 + 125r^4`.  This file performs the coprime
factor allocation exactly as in the 1828 memoir.
-/

namespace Fermat.Five.Dirichlet

/-- Dirichlet's auxiliary quartic before the `√5` representation step. -/
def H (q r : ℕ) : ℕ := q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4

theorem H_pos {q r : ℕ} (hq : 0 < q) : 0 < H q r := by
  simp only [H]
  positivity

theorem r_coprime_H {q r : ℕ} (hqr : q.Coprime r) : r.Coprime (H q r) := by
  have hrq4 : r.Coprime (q ^ 4) := hqr.symm.pow_right 4
  rw [show H q r = q ^ 4 + (50 * q ^ 2 * r + 125 * r ^ 3) * r by
    simp only [H]
    ring]
  exact (Nat.coprime_add_mul_right_right r (q ^ 4)
    (50 * q ^ 2 * r + 125 * r ^ 3)).mpr hrq4

theorem five_coprime_H {q r : ℕ} (hq : ¬5 ∣ q) : Nat.Coprime 5 (H q r) := by
  have h5q : Nat.Coprime 5 q := Nat.prime_five.coprime_iff_not_dvd.mpr hq
  have h5q4 : Nat.Coprime 5 (q ^ 4) := h5q.pow_right 4
  rw [show H q r = q ^ 4 + (10 * q ^ 2 * r ^ 2 + 25 * r ^ 4) * 5 by
    simp only [H]
    ring]
  exact (Nat.coprime_add_mul_right_right 5 (q ^ 4)
    (10 * q ^ 2 * r ^ 2 + 25 * r ^ 4)).mpr h5q4

private theorem zmod_sixteen_H_odd :
    ∀ a b : ZMod 16,
      (2 * a + 1) ^ 4 + 50 * (2 * a + 1) ^ 2 * (2 * b + 1) ^ 2 +
          125 * (2 * b + 1) ^ 4 = 0 := by
  decide

theorem sixteen_dvd_H_of_odd {q r : ℕ} (hq : Odd q) (hr : Odd r) : 16 ∣ H q r := by
  obtain ⟨a, rfl⟩ := hq
  obtain ⟨b, rfl⟩ := hr
  rw [← ZMod.natCast_eq_zero_iff]
  simpa only [H, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one] using
    zmod_sixteen_H_odd (a : ZMod 16) (b : ZMod 16)

theorem odd_H_of_odd_even {q r : ℕ} (hq : Odd q) (hr : Even r) : Odd (H q r) := by
  rcases hq with ⟨a, rfl⟩
  rcases hr with ⟨b, rfl⟩
  refine ⟨8 * a ^ 4 + 16 * a ^ 3 + 12 * a ^ 2 + 4 * a +
      400 * a ^ 2 * b ^ 2 + 400 * a * b ^ 2 + 100 * b ^ 2 + 1000 * b ^ 4, ?_⟩
  simp only [H]
  ring

private theorem coefficient_coprime_H {q r : ℕ} (hqr : q.Coprime r)
    (hq5 : ¬5 ∣ q) : (25 * r).Coprime (H q r) := by
  exact ((five_coprime_H hq5).pow_left 2).mul_left (r_coprime_H hqr)

/-- Coprime allocation in the odd-coordinate branch.  This is the source of
the initial descent exponent `h = 4`. -/
theorem split_odd_core {q r z : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q.Coprime r) (hqodd : Odd q) (hrodd : Odd r) (hq5 : ¬5 ∣ q)
    (hcore : r * H q r = 16 * 5 ^ 3 * z ^ 5) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 25 * r = a ^ 5 ∧ H q r = 16 * b ^ 5 := by
  obtain ⟨K, hK⟩ := sixteen_dvd_H_of_odd hqodd hrodd
  have hcancel : r * K = 5 ^ 3 * z ^ 5 := by
    apply mul_left_cancel₀ (by norm_num : (16 : ℕ) ≠ 0)
    exact calc
      16 * (r * K) = r * H q r := by rw [hK]; ring
      _ = 16 * (5 ^ 3 * z ^ 5) := by rw [hcore]; ring
  have hpow : (25 * r) * K = (5 * z) ^ 5 := by
    calc
      (25 * r) * K = 25 * (r * K) := by ring
      _ = 25 * (5 ^ 3 * z ^ 5) := by rw [hcancel]
      _ = (5 * z) ^ 5 := by ring
  have hcop : (25 * r).Coprime K := by
    have h : (25 * r).Coprime (16 * K) := by
      simpa only [← hK] using coefficient_coprime_H hqr hq5
    exact Nat.Coprime.of_dvd_right (dvd_mul_left K 16) h
  have hpowInt : ((25 * r : ℕ) : ℤ) * K = ((5 * z : ℕ) : ℤ) ^ 5 := by
    exact_mod_cast hpow
  obtain ⟨a, b, ha, hb⟩ := Fermat.Five.exists_two_pow_eq_of_mul_eq_pow
    hcop.isCoprime (by norm_num : Odd 5) hpowInt
  let A := a.natAbs
  let B := b.natAbs
  have haNat : 25 * r = A ^ 5 := by
    have := congrArg Int.natAbs ha
    simpa only [Int.natAbs_natCast, Int.natAbs_pow, A] using this
  have hbNat : K = B ^ 5 := by
    have := congrArg Int.natAbs hb
    simpa only [Int.natAbs_natCast, Int.natAbs_pow, B] using this
  have hA : 0 < A := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at haNat
    simp at haNat
    omega
  have hB : 0 < B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at hbNat
    simp at hbNat
    have hH := H_pos (r := r) hq
    rw [hK, hbNat] at hH
    simp at hH
  exact ⟨A, B, hA, hB, haNat, by rw [hK, hbNat]⟩

/-- Coprime allocation in the opposite-parity branch.  This is the source of
the initial coefficient pair `(g,h) = (1,4)`. -/
theorem split_even_core {q r z : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q.Coprime r) (hqodd : Odd q) (hreven : Even r) (hq5 : ¬5 ∣ q)
    (hcore : r * H q r = 16 * 5 ^ 3 * z ^ 5) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2 * 25 * r = a ^ 5 ∧ H q r = b ^ 5 := by
  have h2H : Nat.Coprime 2 (H q r) := (odd_H_of_odd_even hqodd hreven).coprime_two_left
  have hcop : (2 * 25 * r).Coprime (H q r) :=
    by simpa only [mul_assoc] using h2H.mul_left (coefficient_coprime_H hqr hq5)
  have hpow : (2 * 25 * r) * H q r = (10 * z) ^ 5 := by
    calc
      (2 * 25 * r) * H q r = 2 * 25 * (r * H q r) := by ring
      _ = 2 * 25 * (16 * 5 ^ 3 * z ^ 5) := by rw [hcore]
      _ = (10 * z) ^ 5 := by ring
  have hpowInt : ((2 * 25 * r : ℕ) : ℤ) * H q r = ((10 * z : ℕ) : ℤ) ^ 5 := by
    exact_mod_cast hpow
  obtain ⟨a, b, ha, hb⟩ := Fermat.Five.exists_two_pow_eq_of_mul_eq_pow
    hcop.isCoprime (by norm_num : Odd 5) hpowInt
  let A := a.natAbs
  let B := b.natAbs
  have haNat : 2 * 25 * r = A ^ 5 := by
    have := congrArg Int.natAbs ha
    simpa only [Int.natAbs_natCast, Int.natAbs_pow, A] using this
  have hbNat : H q r = B ^ 5 := by
    have := congrArg Int.natAbs hb
    simpa only [Int.natAbs_natCast, Int.natAbs_pow, B] using this
  have hA : 0 < A := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at haNat
    simp at haNat
    omega
  have hB : 0 < B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at hbNat
    simp at hbNat
    have hH := H_pos (r := r) hq
    omega
  exact ⟨A, B, hA, hB, haNat, hbNat⟩

end Fermat.Five.Dirichlet
