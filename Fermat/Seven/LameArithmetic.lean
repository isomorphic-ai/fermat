import Mathlib

/-!
# Lamé's arithmetic entry for exponent seven

In § II of his 1840 memoir, Lamé rewrites a primitive equation

`x ^ 7 + y ^ 7 = z ^ 7`

as `x ^ 7 = (z - y) * X`, where `X` is the binomial cofactor below.  He
then observes that the two displayed factors have no common prime divisor
other than `7`.  In his second case (§ VI), when `7 ∣ z - y`, he also uses
that `X` contains exactly one factor of `7`.

This file formalizes just that source-faithful arithmetic entrance.  It is
independent of the substantially longer descent which follows in the memoir.
-/

namespace Fermat.Seven.Lame

/-- Lamé's cofactor `X` after putting `d = z - y` in
`z ^ 7 - y ^ 7 = d * X`. -/
def X (d y : ℕ) : ℕ :=
  d ^ 6 + 7 * y * d ^ 5 + 3 * 7 * y ^ 2 * d ^ 4 +
    5 * 7 * y ^ 3 * d ^ 3 + 5 * 7 * y ^ 4 * d ^ 2 +
    3 * 7 * y ^ 5 * d + 7 * y ^ 6

/-- The part of `X` left after separating its leading sixth power. -/
private def tail (d y : ℕ) : ℕ :=
  y * d ^ 5 + 3 * y ^ 2 * d ^ 4 + 5 * y ^ 3 * d ^ 3 +
    5 * y ^ 4 * d ^ 2 + 3 * y ^ 5 * d + y ^ 6

theorem X_eq_pow_add_seven_mul_tail (d y : ℕ) :
    X d y = d ^ 6 + 7 * tail d y := by
  simp only [X, tail]
  ring

/-- The binomial identity underlying Lamé's first displayed factorization. -/
theorem add_seventhPower_factorization (d y : ℕ) :
    (d + y) ^ 7 = y ^ 7 + d * X d y := by
  simp only [X]
  ring

/-- Lamé's factorization in the form in which it is applied to a Fermat
equation. -/
theorem factor_equation {x y z : ℕ} (hyz : y ≤ z)
    (h : x ^ 7 + y ^ 7 = z ^ 7) :
    x ^ 7 = (z - y) * X (z - y) y := by
  have hfactor := add_seventhPower_factorization (z - y) y
  rw [Nat.sub_add_cancel hyz] at hfactor
  omega

/-- Modulo `7`, Lamé's cofactor is just `d ^ 6`. -/
theorem seven_dvd_X_iff {d y : ℕ} : 7 ∣ X d y ↔ 7 ∣ d := by
  rw [X_eq_pow_add_seven_mul_tail]
  constructor
  · intro hX
    have htail : 7 ∣ 7 * tail d y := dvd_mul_right 7 _
    have hd6 : 7 ∣ d ^ 6 := (Nat.dvd_add_iff_left htail).mpr hX
    exact Nat.prime_seven.dvd_of_dvd_pow hd6
  · intro hd
    exact dvd_add (dvd_pow hd (by norm_num)) (dvd_mul_right 7 _)

/-- If `d` and `y` are coprime, the gcd of Lamé's two factors divides `7`.
This is the precise elementary content of his assertion that no other prime
can divide both factors. -/
theorem gcd_dvd_seven {d y : ℕ} (hdy : d.Coprime y) :
    d.gcd (X d y) ∣ 7 := by
  let g := d.gcd (X d y)
  let linearTail :=
    d ^ 5 + 7 * y * d ^ 4 + 3 * 7 * y ^ 2 * d ^ 3 +
      5 * 7 * y ^ 3 * d ^ 2 + 5 * 7 * y ^ 4 * d +
      3 * 7 * y ^ 5
  have hlinear : X d y = d * linearTail + 7 * y ^ 6 := by
    simp only [X, linearTail]
    ring
  have hgd : g ∣ d := Nat.gcd_dvd_left d (X d y)
  have hgX : g ∣ X d y := Nat.gcd_dvd_right d (X d y)
  have hgFirst : g ∣ d * linearTail := hgd.trans (dvd_mul_right d linearTail)
  rw [hlinear] at hgX
  have hgRemainder : g ∣ 7 * y ^ 6 :=
    (Nat.dvd_add_iff_right hgFirst).mpr hgX
  have hgy : g.Coprime y := Nat.Coprime.of_dvd hgd (dvd_refl y) hdy
  exact (hgy.pow_right 6).dvd_of_dvd_mul_left (by
    simpa only [mul_comm] using hgRemainder)

/-- Away from Lamé's exceptional prime `7`, the two factors are coprime. -/
theorem coprime_X_of_not_seven_dvd {d y : ℕ} (hdy : d.Coprime y)
    (hseven : ¬7 ∣ d) : d.Coprime (X d y) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases (Nat.dvd_prime Nat.prime_seven).mp (gcd_dvd_seven hdy) with h | h
  · exact h
  · exfalso
    apply hseven
    rw [← h]
    exact Nat.gcd_dvd_left d (X d y)

/-- In the exceptional branch, the gcd of the two factors is exactly `7`. -/
theorem gcd_eq_seven_of_seven_dvd {d y : ℕ} (hdy : d.Coprime y)
    (hseven : 7 ∣ d) : d.gcd (X d y) = 7 := by
  apply Nat.dvd_antisymm (gcd_dvd_seven hdy)
  exact Nat.dvd_gcd hseven (seven_dvd_X_iff.mpr hseven)

/-- If `7 ∣ d` but `7 ∤ y`, Lamé's cofactor contains exactly one factor
of `7`: it is divisible by `7`, but not by `7 ^ 2 = 49`. -/
theorem X_has_exactly_one_factor_seven {d y : ℕ} (hd : 7 ∣ d)
    (hy : ¬7 ∣ y) : 7 ∣ X d y ∧ ¬49 ∣ X d y := by
  refine ⟨seven_dvd_X_iff.mpr hd, ?_⟩
  obtain ⟨k, rfl⟩ := hd
  let q :=
    7 ^ 4 * k ^ 6 + 7 ^ 4 * y * k ^ 5 +
      3 * 7 ^ 3 * y ^ 2 * k ^ 4 + 5 * 7 ^ 2 * y ^ 3 * k ^ 3 +
      5 * 7 * y ^ 4 * k ^ 2 + 3 * y ^ 5 * k
  have hdecomp : X (7 * k) y = 49 * q + 7 * y ^ 6 := by
    simp only [X, q]
    ring
  intro h49
  have hmultiple : 49 ∣ 49 * q := dvd_mul_right 49 q
  have hsum : 49 ∣ 7 * y ^ 6 + 49 * q := by
    simpa only [hdecomp, add_comm] using h49
  have hrem : 49 ∣ 7 * y ^ 6 :=
    (Nat.dvd_add_iff_left hmultiple).mpr hsum
  have hcancel : 7 * 7 ∣ 7 * y ^ 6 := by
    norm_num at hrem ⊢
    exact hrem
  have hy6 : 7 ∣ y ^ 6 :=
    (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < (7 : ℕ))).mp hcancel
  exact hy (Nat.prime_seven.dvd_of_dvd_pow hy6)

/-- The gap `d` is divisible by `7` exactly when the seventh-power factor
`x` is.  This packages the case split Lamé makes after the factorization. -/
theorem seven_dvd_gap_iff {x d y : ℕ} (h : x ^ 7 = d * X d y) :
    7 ∣ d ↔ 7 ∣ x := by
  constructor
  · intro hd
    have hx7 : 7 ∣ x ^ 7 := by
      rw [h]
      exact hd.trans (dvd_mul_right d (X d y))
    exact Nat.prime_seven.dvd_of_dvd_pow hx7
  · intro hx
    have hx7 : 7 ∣ x ^ 7 := dvd_pow hx (by norm_num)
    rw [h] at hx7
    rcases Nat.prime_seven.dvd_mul.mp hx7 with hd | hX
    · exact hd
    · exact seven_dvd_X_iff.mp hX

/-- A primitive Fermat equation reaches Lamé's two-factor arithmetic with
gcd dividing `7`. -/
theorem primitive_entry {x y z : ℕ} (hyz : y ≤ z) (hcop : y.Coprime z)
    (h : x ^ 7 + y ^ 7 = z ^ 7) :
    x ^ 7 = (z - y) * X (z - y) y ∧
      (z - y).gcd (X (z - y) y) ∣ 7 := by
  have hgap : (z - y).Coprime y :=
    (Nat.coprime_sub_self_left hyz).mpr hcop.symm
  exact ⟨factor_equation hyz h, gcd_dvd_seven hgap⟩

end Fermat.Seven.Lame
