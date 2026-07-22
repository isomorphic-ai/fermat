import Fermat.Five.Equation
import Fermat.Five.InitialArithmetic

/-!
# Half-sum coordinates in Dirichlet's exponent-five proof

This file follows the substitutions at the beginning of Theorems V and VIII
of the 1828 memoir.  A normalized solution of `x^5+y^5=5^5z^5` enters one
of two copies of the same core equation, according to the parity of `x,y`.
-/

namespace Fermat.Five.Dirichlet

/-- The quartic in the half-sum factorization, over the integers. -/
private def Fz (p q : ℤ) : ℤ := p ^ 4 + 10 * p ^ 2 * q ^ 2 + 5 * q ^ 4

private theorem five_dvd_left_of_dvd_mul_Fz {p q : ℤ}
    (h : (5 : ℤ) ∣ p * Fz p q) : (5 : ℤ) ∣ p := by
  rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h with hp | hF
  · exact hp
  · have hp4 : (5 : ℤ) ∣ p ^ 4 := by
      have hterm : (5 : ℤ) ∣ 5 * (2 * p ^ 2 * q ^ 2 + q ^ 4) := dvd_mul_right 5 _
      convert dvd_sub hF hterm using 1
      simp only [Fz]
      ring
    exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hp4

private theorem coordinate_coprime {x y p q : ℤ} (hxy : IsCoprime x y)
    (hx : x = p + q) (hy : y = p - q) : IsCoprime p q := by
  refine isCoprime_of_prime_dvd ?_ (fun l hl hlp hlq ↦ ?_)
  · rintro ⟨rfl, rfl⟩
    simp at hx hy
    subst x
    subst y
    norm_num [Int.isCoprime_iff_gcd_eq_one] at hxy
  · have hlx : l ∣ x := by
      rw [hx]
      exact dvd_add hlp hlq
    have hly : l ∣ y := by
      rw [hy]
      exact dvd_sub hlp hlq
    exact hl.not_unit (hxy.isUnit_of_dvd' hlx hly)

private theorem add_sub_coprime_of_odd {x y : ℤ} (hxy : IsCoprime x y)
    (hpodd : Odd (x + y)) : IsCoprime (x + y) (x - y) := by
  refine isCoprime_of_prime_dvd ?_ (fun l hl hlp hlq ↦ ?_)
  · rintro ⟨hadd, hsub⟩
    have : x = 0 ∧ y = 0 := by omega
    rcases this with ⟨rfl, rfl⟩
    norm_num [Int.isCoprime_iff_gcd_eq_one] at hxy
  · have hl2x : l ∣ 2 * x := by
      convert dvd_add hlp hlq using 1
      ring
    have hl2y : l ∣ 2 * y := by
      convert dvd_sub hlp hlq using 1
      ring
    rcases hl.dvd_mul.mp hl2x with hl2 | hlx
    · have hp2 : IsCoprime (x + y) (2 : ℤ) := Int.isCoprime_two_right.mpr hpodd
      exact hl.not_unit (hp2.isUnit_of_dvd' hlp hl2)
    · rcases hl.dvd_mul.mp hl2y with hl2 | hly
      · have hp2 : IsCoprime (x + y) (2 : ℤ) := Int.isCoprime_two_right.mpr hpodd
        exact hl.not_unit (hp2.isUnit_of_dvd' hlp hl2)
      · exact hl.not_unit (hxy.isUnit_of_dvd' hlx hly)

/-- The core reached when the half-sum coordinates are both odd. -/
structure OddCore (q r z : ℕ) : Prop where
  equation : r * H q r = 16 * 5 ^ 3 * z ^ 5
  q_pos : 0 < q
  r_pos : 0 < r
  z_pos : 0 < z
  coprime : q.Coprime r
  q_odd : Odd q
  r_odd : Odd r
  q_not_five : ¬5 ∣ q

/-- The core reached when the half-sum coordinates have opposite parity. -/
structure EvenCore (q r z : ℕ) : Prop where
  equation : r * H q r = 16 * 5 ^ 3 * z ^ 5
  q_pos : 0 < q
  r_pos : 0 < r
  z_pos : 0 < z
  coprime : q.Coprime r
  q_odd : Odd q
  r_even : Even r
  q_not_five : ¬5 ∣ q

private theorem core_nat_equation {q r z : ℤ} (hr : 0 < r) (hz : 0 < z)
    (h : r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) =
      16 * 5 ^ 3 * z ^ 5) :
    r.natAbs * H q.natAbs r.natAbs = 16 * 5 ^ 3 * z.natAbs ^ 5 := by
  apply Int.ofNat_inj.mp
  push_cast
  simp only [H, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [Int.natCast_natAbs]
  rw [abs_of_pos hr, abs_of_pos hz, (show Even 4 by norm_num).pow_abs q,
    (show Even 2 by norm_num).pow_abs q]
  exact h

private theorem nat_not_five_of_int_not_five {q : ℤ} (h : ¬(5 : ℤ) ∣ q) :
    ¬5 ∣ q.natAbs := by
  intro hq
  apply h
  rw [← Int.dvd_natAbs]
  exact Int.natCast_dvd_natCast.mpr hq

/-- Opposite parity of `x,y` is Dirichlet's odd-coordinate branch. -/
theorem FifthEquation.oddCore_of_oppositeParity {x y z : ℤ}
    (d : FifthEquation x y z) (hz : 0 < z)
    (hparity : (Even x ∧ Odd y) ∨ (Odd x ∧ Even y)) :
    ∃ q r z₀ : ℕ, OddCore q r z₀ := by
  let p : ℤ := x + y
  let q : ℤ := x - y
  have hpodd : Odd p := by
    rcases hparity with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · simpa [p, parity_simps] using hx.add_odd hy
    · simpa [p, parity_simps] using hx.add_even hy
  have hqodd : Odd q := by
    rcases hparity with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · simpa [q, parity_simps] using hx.sub_odd hy
    · simpa [q, parity_simps] using hx.sub_even hy
  have hpq : IsCoprime p q := by
    simpa only [p, q] using add_sub_coprime_of_odd d.2.1 hpodd
  have hfactor : p * Fz p q = 16 * (x ^ 5 + y ^ 5) := by
    simp only [p, q, Fz]
    ring
  have hpF : p * Fz p q = 16 * 5 ^ 5 * z ^ 5 := by
    rw [hfactor, d.2.2]
    ring
  have hpFpos : 0 < p * Fz p q := by rw [hpF]; positivity
  have hFnonneg : 0 ≤ Fz p q := by
    simp only [Fz]
    positivity
  have hp : 0 < p := by
    by_contra hpn
    have : p ≤ 0 := le_of_not_gt hpn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg this hFnonneg)) hpFpos
  have hfiveProduct : (5 : ℤ) ∣ p * Fz p q := by
    rw [hpF]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by norm_num : (5 : ℤ) ∣ 5 ^ 5) 16) _
  have hfiveP : (5 : ℤ) ∣ p := five_dvd_left_of_dvd_mul_Fz hfiveProduct
  obtain ⟨r, hpr⟩ := hfiveP
  have hr : 0 < r := by rw [hpr] at hp; omega
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq] at hqodd
    norm_num at hqodd
  have hrq : IsCoprime r q := by
    apply hpq.of_isCoprime_of_dvd_left
    exact ⟨5, by rw [hpr]; ring⟩
  have hq5 : ¬(5 : ℤ) ∣ q := by
    intro h5q
    have hunit := hpq.isUnit_of_dvd' (show (5 : ℤ) ∣ p from ⟨r, hpr⟩) h5q
    norm_num [Int.isUnit_iff] at hunit
  have hcoreInt :
      r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) =
        16 * 5 ^ 3 * z ^ 5 := by
    rw [hpr] at hpF
    simp only [Fz] at hpF
    apply mul_left_cancel₀ (by norm_num : (25 : ℤ) ≠ 0)
    calc
      25 * (r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4)) =
          5 * r * ((5 * r) ^ 4 + 10 * (5 * r) ^ 2 * q ^ 2 + 5 * q ^ 4) := by ring
      _ = 25 * (16 * 5 ^ 3 * z ^ 5) := by rw [hpF]; ring
  let Q := q.natAbs
  let R := r.natAbs
  let Z := z.natAbs
  have hQR : Q.Coprime R := by
    exact (Int.isCoprime_iff_nat_coprime.mp hrq).symm
  have hQodd : Odd Q := Int.natAbs_odd.mpr hqodd
  have hRodd : Odd R := by
    have : Odd r := by
      have hpOdd : Odd (5 * r) := by simpa [hpr] using hpodd
      exact (Int.odd_mul.mp hpOdd).2
    exact Int.natAbs_odd.mpr this
  refine ⟨Q, R, Z, core_nat_equation hr hz hcoreInt, ?_, ?_, ?_, hQR, hQodd, hRodd,
    nat_not_five_of_int_not_five hq5⟩
  · exact Int.natAbs_pos.mpr hq0
  · exact Int.natAbs_pos.mpr hr.ne'
  · exact Int.natAbs_pos.mpr hz.ne'

/-- When `x,y` are both odd, their half-sum coordinates have opposite
parity and enter Dirichlet's other descent. -/
theorem FifthEquation.evenCore_of_odd {x y z : ℤ}
    (d : FifthEquation x y z) (hz : 0 < z) (hxodd : Odd x) (hyodd : Odd y) :
    ∃ q r z₀ : ℕ, EvenCore q r z₀ := by
  obtain ⟨a, ha⟩ := hxodd
  obtain ⟨b, hb⟩ := hyodd
  let p : ℤ := a + b + 1
  let q : ℤ := a - b
  have hxp : x = p + q := by rw [ha]; simp only [p, q]; ring
  have hyp : y = p - q := by rw [hb]; simp only [p, q]; ring
  have hpq : IsCoprime p q := coordinate_coprime d.2.1 hxp hyp
  have hfactor : x ^ 5 + y ^ 5 = 2 * p * Fz p q := by
    rw [hxp, hyp]
    simp only [Fz]
    ring
  have hpF : 2 * p * Fz p q = 5 ^ 5 * z ^ 5 := by
    rw [← hfactor, d.2.2]
  have hpFpos : 0 < 2 * p * Fz p q := by rw [hpF]; positivity
  have hFnonneg : 0 ≤ Fz p q := by
    simp only [Fz]
    positivity
  have hp : 0 < p := by
    by_contra hpn
    have hpnonpos : p ≤ 0 := le_of_not_gt hpn
    have : 2 * p * Fz p q ≤ 0 := by
      have : p * Fz p q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpnonpos hFnonneg
      nlinarith
    exact (not_lt_of_ge this) hpFpos
  have hzEven : Even z := by
    have htwo : (2 : ℤ) ∣ 5 ^ 5 * z ^ 5 := by
      rw [← hpF]
      exact ⟨p * Fz p q, by ring⟩
    have hz5 : (2 : ℤ) ∣ z ^ 5 := by
      rcases (show Prime (2 : ℤ) by norm_num).dvd_mul.mp htwo with h25 | hz5
      · have : ¬(2 : ℤ) ∣ 5 ^ 5 := by norm_num
        exact (this h25).elim
      · exact hz5
    exact even_iff_two_dvd.mpr ((show Prime (2 : ℤ) by norm_num).dvd_of_dvd_pow hz5)
  obtain ⟨z₁, hz₁⟩ := hzEven
  have hz₁pos : 0 < z₁ := by rw [hz₁] at hz; omega
  have hfiveProduct : (5 : ℤ) ∣ p * Fz p q := by
    have hfive : (5 : ℤ) ∣ 2 * (p * Fz p q) := by
      rw [show 2 * (p * Fz p q) = 2 * p * Fz p q by ring, hpF]
      exact dvd_mul_of_dvd_left (by norm_num : (5 : ℤ) ∣ 5 ^ 5) _
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hfive with h52 | hrest
    · norm_num at h52
    · exact hrest
  have hfiveP : (5 : ℤ) ∣ p := five_dvd_left_of_dvd_mul_Fz hfiveProduct
  obtain ⟨r, hpr⟩ := hfiveP
  have hr : 0 < r := by rw [hpr] at hp; omega
  have hq0 : q ≠ 0 := by
    intro hq
    have hunit := hpq.isUnit_of_dvd' (show (5 : ℤ) ∣ p from ⟨r, hpr⟩)
      (by simp [hq])
    norm_num [Int.isUnit_iff] at hunit
  have hrq : IsCoprime r q := by
    apply hpq.of_isCoprime_of_dvd_left
    exact ⟨5, by rw [hpr]; ring⟩
  have hq5 : ¬(5 : ℤ) ∣ q := by
    intro h5q
    have hunit := hpq.isUnit_of_dvd' (show (5 : ℤ) ∣ p from ⟨r, hpr⟩) h5q
    norm_num [Int.isUnit_iff] at hunit
  have hcoreInt :
      r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) =
        16 * 5 ^ 3 * z₁ ^ 5 := by
    rw [hpr, hz₁] at hpF
    simp only [Fz] at hpF
    apply mul_left_cancel₀ (by norm_num : (50 : ℤ) ≠ 0)
    calc
      50 * (r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4)) =
          2 * (5 * r) * ((5 * r) ^ 4 + 10 * (5 * r) ^ 2 * q ^ 2 + 5 * q ^ 4) := by
            ring
      _ = 50 * (16 * 5 ^ 3 * z₁ ^ 5) := by rw [hpF]; ring
  have hxcoordOdd : Odd (p + q) := by rw [← hxp]; exact ⟨a, ha⟩
  have hrEven : Even r := by
    rcases Int.even_or_odd r with hrEven | hrOdd
    · exact hrEven
    · have hpOdd : Odd p := by
        rw [hpr]
        exact (show Odd (5 : ℤ) by norm_num).mul hrOdd
      have hqEven : Even q := by
        rcases Int.even_or_odd q with hqEven | hqOdd
        · exact hqEven
        · have : Even (p + q) := hpOdd.add_odd hqOdd
          exact (Int.not_even_iff_odd.mpr hxcoordOdd this).elim
      have hHOdd : Odd (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4) := by
        have hfirst : Even (q ^ 4) := hqEven.pow_of_ne_zero (by norm_num)
        have hmiddle : Even (50 * q ^ 2 * r ^ 2) := by
          simpa only [mul_assoc] using
            (show Even (50 : ℤ) by norm_num).mul_right (q ^ 2 * r ^ 2)
        have hlast : Odd (125 * r ^ 4) :=
          (show Odd (125 : ℤ) by norm_num).mul hrOdd.pow
        exact (hfirst.add hmiddle).add_odd hlast
      have hlhsOdd := hrOdd.mul hHOdd
      have hrhsEven : Even (16 * 5 ^ 3 * z₁ ^ 5 : ℤ) := by
        exact ⟨8 * 5 ^ 3 * z₁ ^ 5, by ring⟩
      have hlhsEven : Even
          (r * (q ^ 4 + 50 * q ^ 2 * r ^ 2 + 125 * r ^ 4)) := by
        rw [hcoreInt]
        exact hrhsEven
      exact (Int.not_even_iff_odd.mpr hlhsOdd hlhsEven).elim
  have hqOdd : Odd q := by
    have hpEven : Even p := by
      rw [hpr]
      exact hrEven.mul_left 5
    rcases Int.even_or_odd q with hqEven | hqOdd
    · have : Even (p + q) := hpEven.add hqEven
      exact (Int.not_even_iff_odd.mpr hxcoordOdd this).elim
    · exact hqOdd
  let Q := q.natAbs
  let R := r.natAbs
  let Z := z₁.natAbs
  have hQR : Q.Coprime R := (Int.isCoprime_iff_nat_coprime.mp hrq).symm
  refine ⟨Q, R, Z, core_nat_equation hr hz₁pos hcoreInt,
    Int.natAbs_pos.mpr hq0, Int.natAbs_pos.mpr hr.ne', Int.natAbs_pos.mpr hz₁pos.ne',
    hQR, Int.natAbs_odd.mpr hqOdd, Int.natAbs_even.mpr hrEven,
    nat_not_five_of_int_not_five hq5⟩

theorem FifthEquation.exists_core {x y z : ℤ} (d : FifthEquation x y z) :
    (∃ q r z₀ : ℕ, OddCore q r z₀) ∨ (∃ q r z₀ : ℕ, EvenCore q r z₀) := by
  obtain ⟨x, y, z, d, hz⟩ := d.exists_positive_right
  rcases Int.even_or_odd x with hx | hx <;> rcases Int.even_or_odd y with hy | hy
  · have hunit : IsUnit (2 : ℤ) :=
      d.2.1.isUnit_of_dvd' (even_iff_two_dvd.mp hx) (even_iff_two_dvd.mp hy)
    norm_num [Int.isUnit_iff] at hunit
  · left
    exact d.oddCore_of_oppositeParity hz (Or.inl ⟨hx, hy⟩)
  · left
    exact d.oddCore_of_oppositeParity hz (Or.inr ⟨hx, hy⟩)
  · right
    exact d.evenCore_of_odd hz hx hy

end Fermat.Five.Dirichlet
