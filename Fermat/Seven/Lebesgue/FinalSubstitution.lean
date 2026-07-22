import Fermat.Seven.Lebesgue.Descent
import Fermat.Seven.Lebesgue.EvenSquare
import Fermat.Seven.Lebesgue.Symmetric

/-!
# Lebesgue's final substitution for exponent seven

After the seventh-power allocation on p. 278, Lebesgue substitutes

`t = q ^ 14`, `u = q * r`, `v = 7 ^ 6 * p ^ 7`,
`s = 7 * p * q ^ 2`

back into his two symmetric identities.  Writing the square of the even
integer `p` as `2 ^ (a + 1) * R` then gives exactly the quartic family in
Théorème I.  This file carries out that substitution and transfers the
result to natural numbers for the descent.
-/

namespace Fermat.Seven.Lebesgue

/-- Lebesgue's four allocated powers produce an odd, pairwise-coprime member
of the family in Théorème I.  The coprimalities of `p,q,r` are supplied by
the power-allocation stage; the oddness of `q,r` comes from the primitive
parity calculation for `u`.
-/
theorem exists_descentEquation_of_power_data
    {x y z p q r : ℤ}
    (htq : t x y z = q ^ 14)
    (hur : u x y z = q * r)
    (hvp : v x y z = 7 ^ 6 * p ^ 7)
    (hspq : s x y z = 7 * p * q ^ 2)
    (hpEven : Even p) (hp0 : p ≠ 0)
    (hqOdd : Odd q) (hrOdd : Odd r)
    (hpq : IsCoprime p q) (hpr : IsCoprime p r)
    (hqr : IsCoprime q r) :
    ∃ a P Q R : ℕ,
      0 < a ∧ Odd P ∧ Odd Q ∧ Odd R ∧
        P.Coprime Q ∧ P.Coprime R ∧ Q.Coprime R ∧
        DescentEquation a P Q R := by
  obtain ⟨a, R, ha, hRodd, hpSq, hRqr⟩ :=
    exists_even_square_decomposition_coprime hpEven hp0 (hpq.mul_right hpr)
  let P : ℤ := r - 7 ^ 2 * 2 ^ a * R * q ^ 3
  let Q : ℤ := q ^ 3
  have he₂ : x * y + x * z + y * z =
      q * (7 ^ 2 * p ^ 2 * q ^ 3 - r) := by
    calc
      x * y + x * z + y * z = s x y z ^ 2 - u x y z := by
        rw [u_eq_s_sq_sub]
        ring
      _ = q * (7 ^ 2 * p ^ 2 * q ^ 3 - r) := by
        rw [hspq, hur]
        ring
  have hxyz : x * y * z =
      7 * p * q ^ 3 * (7 ^ 2 * p ^ 2 * q ^ 3 - r) - 7 ^ 6 * p ^ 7 := by
    calc
      x * y * z =
          s x y z * (x * y + x * z + y * z) - v x y z := by
        rw [v_eq_s_mul_sub_xyz]
        ring
      _ = 7 * p * q ^ 3 * (7 ^ 2 * p ^ 2 * q ^ 3 - r) -
          7 ^ 6 * p ^ 7 := by
        rw [hspq, he₂, hvp]
        ring
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    norm_num at hqOdd
  have hcore : q ^ 12 =
      r ^ 2 + 7 ^ 2 * p ^ 2 * q ^ 3 *
        (7 ^ 2 * p ^ 2 * q ^ 3 - r) - 7 ^ 7 * p ^ 8 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hq0)
    calc
      q ^ 2 * q ^ 12 = q ^ 14 := by ring
      _ = t x y z := htq.symm
      _ = u x y z ^ 2 + x * y * z * s x y z := rfl
      _ = q ^ 2 * (r ^ 2 + 7 ^ 2 * p ^ 2 * q ^ 3 *
          (7 ^ 2 * p ^ 2 * q ^ 3 - r) - 7 ^ 7 * p ^ 8) := by
        rw [hur, hxyz, hspq]
        ring
  have hcomplete :
      P ^ 2 + (2 : ℤ) ^ (2 * a) * 3 * 7 ^ 4 * Q ^ 2 * R ^ 2 =
        Q ^ 4 + (2 : ℤ) ^ (4 * a + 4) * 7 ^ 7 * R ^ 4 := by
    have hleft :
        P ^ 2 + (2 : ℤ) ^ (2 * a) * 3 * 7 ^ 4 * Q ^ 2 * R ^ 2 =
          r ^ 2 + 7 ^ 2 * p ^ 2 * q ^ 3 *
            (7 ^ 2 * p ^ 2 * q ^ 3 - r) := by
      simp only [P, Q]
      rw [hpSq]
      ring_nf
    have hright :
        q ^ 12 + 7 ^ 7 * p ^ 8 =
          Q ^ 4 + (2 : ℤ) ^ (4 * a + 4) * 7 ^ 7 * R ^ 4 := by
      have hpEight :
          p ^ 8 = (2 : ℤ) ^ (4 * a + 4) * R ^ 4 := by
        calc
          p ^ 8 = (p ^ 2) ^ 4 := by ring
          _ = ((2 : ℤ) ^ (a + 1) * R) ^ 4 := by rw [hpSq]
          _ = (2 : ℤ) ^ (4 * a + 4) * R ^ 4 := by ring_nf
      simp only [Q]
      rw [hpEight]
      ring
    rw [hleft, ← hright]
    linarith
  have hPodd : Odd P := by
    have htwoPowEven : Even ((2 : ℤ) ^ a) := by
      rw [even_iff_two_dvd]
      exact dvd_pow (dvd_refl 2) (Nat.ne_zero_of_lt ha)
    exact hrOdd.sub_even
      (((htwoPowEven.mul_left (7 ^ 2)).mul_right R).mul_right (q ^ 3))
  have hQodd : Odd Q := by
    exact hqOdd.pow
  have hRq : IsCoprime R q := hRqr.of_mul_right_left
  have hRr : IsCoprime R r := hRqr.of_mul_right_right
  have hPQ : IsCoprime P Q := by
    have hrQ : IsCoprime r Q := by
      exact hqr.symm.pow_right
    rw [show P = r - Q * (7 ^ 2 * 2 ^ a * R) by simp only [P, Q]; ring]
    simpa only [IsCoprime.sub_mul_left_left_iff] using hrQ
  have hPR : IsCoprime P R := by
    rw [show P = r - R * (7 ^ 2 * 2 ^ a * q ^ 3) by simp only [P]; ring]
    simpa only [IsCoprime.sub_mul_left_left_iff] using hRr.symm
  have hQR : IsCoprime Q R := by
    exact hRq.symm.pow_left
  refine ⟨a, P.natAbs, Q.natAbs, R.natAbs, ha,
    hPodd.natAbs, hQodd.natAbs, hRodd.natAbs, ?_, ?_, ?_, ?_⟩
  · exact Int.isCoprime_iff_nat_coprime.mp hPQ
  · exact Int.isCoprime_iff_nat_coprime.mp hPR
  · exact Int.isCoprime_iff_nat_coprime.mp hQR
  · simp only [DescentEquation]
    have habs :
        |P| ^ 2 + (2 : ℤ) ^ (2 * a) * 3 * 7 ^ 4 * |Q| ^ 2 * |R| ^ 2 =
          |Q| ^ 4 + (2 : ℤ) ^ (4 * a + 4) * 7 ^ 7 * |R| ^ 4 := by
      rw [(show Even 2 by norm_num).pow_abs P,
        (show Even 2 by norm_num).pow_abs Q,
        (show Even 2 by norm_num).pow_abs R,
        (show Even 4 by norm_num).pow_abs Q,
        (show Even 4 by norm_num).pow_abs R]
      exact hcomplete
    rw [← Int.natCast_natAbs P, ← Int.natCast_natAbs Q,
      ← Int.natCast_natAbs R] at habs
    exact_mod_cast habs

end Fermat.Seven.Lebesgue
