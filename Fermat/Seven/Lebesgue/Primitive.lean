import Fermat.Seven.Lebesgue.Symmetric

/-!
# Primitive arithmetic in Lebesgue's proof for exponent seven

This file develops the parity and coprimality consequences of a primitive
ternary solution used on p. 278 of Lebesgue's 1840 memoir.  The arguments are
entirely over the integers.
-/

namespace Fermat.Seven.Lebesgue

/-- In a pairwise-coprime ternary solution, exactly one entry is even. -/
theorem exactly_one_even_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) :
    (Even x ∧ Odd y ∧ Odd z) ∨
      (Odd x ∧ Even y ∧ Odd z) ∨
      (Odd x ∧ Odd y ∧ Even z) := by
  rcases Int.even_or_odd x with hx | hx <;>
    rcases Int.even_or_odd y with hy | hy <;>
      rcases Int.even_or_odd z with hz | hz
  · have hunit : IsUnit (2 : ℤ) :=
      hxy.isUnit_of_dvd' (even_iff_two_dvd.mp hx) (even_iff_two_dvd.mp hy)
    norm_num [Int.isUnit_iff] at hunit
  · have hunit : IsUnit (2 : ℤ) :=
      hxy.isUnit_of_dvd' (even_iff_two_dvd.mp hx) (even_iff_two_dvd.mp hy)
    norm_num [Int.isUnit_iff] at hunit
  · have hunit : IsUnit (2 : ℤ) :=
      hxz.isUnit_of_dvd' (even_iff_two_dvd.mp hx) (even_iff_two_dvd.mp hz)
    norm_num [Int.isUnit_iff] at hunit
  · exact Or.inl ⟨hx, hy, hz⟩
  · have hunit : IsUnit (2 : ℤ) :=
      hyz.isUnit_of_dvd' (even_iff_two_dvd.mp hy) (even_iff_two_dvd.mp hz)
    norm_num [Int.isUnit_iff] at hunit
  · exact Or.inr (Or.inl ⟨hx, hy, hz⟩)
  · exact Or.inr (Or.inr ⟨hx, hy, hz⟩)
  · have hodd : Odd (x ^ 7 + y ^ 7 + z ^ 7) := by
      exact hx.pow.add_odd hy.pow |>.add_odd hz.pow
    rw [heq] at hodd
    simp at hodd

/-- Lebesgue's sum `s = x + y + z` is even in a primitive ternary solution. -/
theorem even_s_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) : Even (s x y z) := by
  rcases exactly_one_even_of_ternary hxy hxz hyz heq with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact hx.add_odd hy |>.add_odd hz
  · exact hx.add_even hy |>.add_odd hz
  · exact hx.add_odd hy |>.add hz

/-- Lebesgue's quadratic quantity `u` is odd in a primitive ternary solution. -/
theorem odd_u_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) : Odd (u x y z) := by
  rcases exactly_one_even_of_ternary hxy hxz hyz heq with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact
      (((((hx.pow_of_ne_zero (by norm_num)).add_odd hy.pow).add_odd hz.pow).add
          (hx.mul_right y)).add (hx.mul_right z)).add_odd (hy.mul hz)
  · exact
      (((((hx.pow.add_even (hy.pow_of_ne_zero (by norm_num))).add_odd hz.pow).add
          (hy.mul_left x)).add_odd (hx.mul hz)).add_even (hy.mul_right z))
  · exact
      (((((hx.pow.add_odd hy.pow).add (hz.pow_of_ne_zero (by norm_num))).add_odd
          (hx.mul hy)).add_even (hz.mul_left x)).add_even (hz.mul_left y))

/-- Lebesgue's factor `t` is congruent to one modulo four. -/
theorem t_modEq_one_mod_four_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) :
    t x y z ≡ 1 [ZMOD 4] := by
  have huOdd := odd_u_of_ternary hxy hxz hyz heq
  have huSq : (4 : ℤ) ∣ u x y z ^ 2 - 1 :=
    dvd_trans (by norm_num : (4 : ℤ) ∣ 8) (Int.eight_dvd_sq_sub_one_of_odd huOdd)
  have hsEven := even_s_of_ternary hxy hxz hyz heq
  have hxyzEven : Even (x * y * z) := by
    rcases exactly_one_even_of_ternary hxy hxz hyz heq with
      ⟨hx, -, -⟩ | ⟨-, hy, -⟩ | ⟨-, -, hz⟩
    · exact (hx.mul_right y).mul_right z
    · exact (hy.mul_left x).mul_right z
    · exact hz.mul_left (x * y)
  have hprod : (4 : ℤ) ∣ x * y * z * s x y z := by
    obtain ⟨a, ha⟩ := hxyzEven
    obtain ⟨b, hb⟩ := hsEven
    refine ⟨a * b, ?_⟩
    rw [ha, hb]
    ring
  rw [Int.modEq_iff_dvd]
  rw [show 1 - t x y z =
    -((u x y z ^ 2 - 1) + x * y * z * s x y z) by simp only [t]; ring]
  exact dvd_neg.mpr (huSq.add hprod)

private theorem not_prime_dvd_t_of_dvd_first {a b c p : ℤ}
    (hac : IsCoprime a c) (heq : a ^ 7 + b ^ 7 + c ^ 7 = 0)
    (hp : Prime p) (hpa : p ∣ a) : ¬p ∣ t a b c := by
  intro hpt
  have hpProd : p ∣ a * b * c * s a b c := by
    rw [show a * b * c * s a b c = a * (b * c * s a b c) by ring]
    exact dvd_mul_of_dvd_left hpa _
  have huSq : p ∣ u a b c ^ 2 := by
    rw [show u a b c ^ 2 = t a b c - a * b * c * s a b c by simp only [t]; ring]
    exact dvd_sub hpt hpProd
  have hu : p ∣ u a b c := hp.dvd_of_dvd_pow huSq
  let A : ℤ := b ^ 2 + b * c + c ^ 2
  have hA : p ∣ A := by
    rw [show A = u a b c - a * s a b c by simp only [A, u, s]; ring]
    exact dvd_sub hu (dvd_mul_of_dvd_left hpa _)
  have hbcSeven : p ∣ b ^ 7 + c ^ 7 := by
    rw [show b ^ 7 + c ^ 7 = -(a ^ 7) by omega]
    exact dvd_neg.mpr (dvd_pow hpa (by norm_num))
  let Q : ℤ := b ^ 5 - b ^ 4 * c + b ^ 2 * c ^ 3 - b * c ^ 4
  have hrem : p ∣ c ^ 6 * (b + c) := by
    rw [show c ^ 6 * (b + c) = (b ^ 7 + c ^ 7) - A * Q by
      simp only [A, Q]
      ring]
    exact dvd_sub hbcSeven (dvd_mul_of_dvd_left hA _)
  have hpc : ¬p ∣ c := by
    intro hpc
    exact hp.not_unit (hac.isUnit_of_dvd' hpa hpc)
  have hpcPow : ¬p ∣ c ^ 6 := by
    intro h
    exact hpc (hp.dvd_of_dvd_pow h)
  have hsum : p ∣ b + c := (hp.dvd_mul.mp hrem).resolve_left hpcPow
  have hcSq : p ∣ c ^ 2 := by
    rw [show c ^ 2 = A - b * (b + c) by simp only [A]; ring]
    exact dvd_sub hA (dvd_mul_of_dvd_right hsum _)
  exact hpc (hp.dvd_of_dvd_pow hcSq)

/-- Lebesgue's factor `t` is coprime to the product `xyz`. -/
theorem isCoprime_t_xyz_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) :
    IsCoprime (t x y z) (x * y * z) := by
  have htMod := t_modEq_one_mod_four_of_ternary hxy hxz hyz heq
  have ht0 : t x y z ≠ 0 := by
    intro ht
    rw [ht] at htMod
    norm_num [Int.ModEq] at htMod
  refine isCoprime_of_prime_dvd (by simp [ht0]) ?_
  intro p hp hpt hpProd
  rcases hp.dvd_mul.mp hpProd with hpxy | hpz
  · rcases hp.dvd_mul.mp hpxy with hpx | hpy
    · exact (not_prime_dvd_t_of_dvd_first hxz heq hp hpx) hpt
    · apply not_prime_dvd_t_of_dvd_first hyz (a := y) (b := x) (c := z)
        (by omega) hp hpy
      rw [show t y x z = t x y z by simp only [t, u, s]; ring]
      exact hpt
  · apply not_prime_dvd_t_of_dvd_first hyz.symm (a := z) (b := x) (c := y)
      (by omega) hp hpz
    rw [show t z x y = t x y z by simp only [t, u, s]; ring]
    exact hpt

/-- Lebesgue's two factors `t` and `v` are coprime. -/
theorem isCoprime_t_v_of_ternary {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (heq : x ^ 7 + y ^ 7 + z ^ 7 = 0) :
    IsCoprime (t x y z) (v x y z) := by
  have htxyz := isCoprime_t_xyz_of_ternary hxy hxz hyz heq
  have htMod := t_modEq_one_mod_four_of_ternary hxy hxz hyz heq
  have ht0 : t x y z ≠ 0 := by
    intro ht
    rw [ht] at htMod
    norm_num [Int.ModEq] at htMod
  refine isCoprime_of_prime_dvd (by simp [ht0]) ?_
  intro p hp hpt hpv
  have hsPow : p ∣ s x y z ^ 7 := by
    rw [s_pow_seven_eq_seven_mul_v_t_of_ternary heq]
    rw [show 7 * v x y z * t x y z = (7 * v x y z) * t x y z by ring]
    exact dvd_mul_of_dvd_right hpt _
  have hs : p ∣ s x y z := hp.dvd_of_dvd_pow hsPow
  have hxyz : p ∣ x * y * z := by
    rw [show x * y * z =
      s x y z * (x * y + x * z + y * z) - v x y z by
        rw [v_eq_s_mul_sub_xyz]
        ring]
    exact dvd_sub (dvd_mul_of_dvd_left hs _) hpv
  exact hp.not_unit (htxyz.isUnit_of_dvd' hpt hxyz)

end Fermat.Seven.Lebesgue
