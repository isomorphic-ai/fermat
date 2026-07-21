import Fermat.Basic
import Fermat.Quadratic.NegSeven

/-!
# The power-extraction step in Dirichlet's proof

This file isolates the algebra used to pass from a primitive representation

`P ^ 2 + 7 * Q ^ 2 = A ^ 14`

to a signed fourteenth power in the maximal order of `ℚ(√-7)`.  There are
two logically separate ingredients:

* primitive integers of opposite parity give coprime conjugate algebraic
  integers;
* in a principal ideal domain, coprime factors of a power are themselves
  powers up to a unit.

Keeping these statements separate makes the historically omitted unit visible:
for an even exponent it contributes the unavoidable sign `±1`.
-/

namespace Fermat.Fourteen.PowerExtraction

open Fermat.Quadratic.NegSeven

/-- If the only units of a principal ideal domain are `±1`, a coprime factor
of a `k`-th power is a signed `k`-th power. -/
theorem exists_signed_pow_of_mul_eq_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (units_eq_one_or_neg_one : ∀ u : Rˣ, (u : R) = 1 ∨ (u : R) = -1)
    {a b c : R} {k : ℕ} (hab : IsCoprime a b) (hpow : a * b = c ^ k) :
    ∃ d : R, a = d ^ k ∨ a = -(d ^ k) := by
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hab hpow
  refine ⟨d, ?_⟩
  rcases units_eq_one_or_neg_one u with hu_one | hu_neg_one
  · left
    simpa [hu_one] using hu.symm
  · right
    simpa [hu_neg_one] using hu.symm

/-- A useful explicit Bezout identity: if the product and sum of two elements
are coprime, then the elements themselves are coprime. -/
theorem isCoprime_of_mul_add {R : Type*} [CommRing R] {x y : R}
    (h : IsCoprime (x * y) (x + y)) : IsCoprime x y := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * y + b, b, ?_⟩
  calc
    (a * y + b) * x + b * y = a * (x * y) + b * (x + y) := by ring
    _ = 1 := hab

/-- An integral coprimality statement can be transported to conjugates in any
commutative ring once their product and sum have the expected values. -/
theorem conjugates_isCoprime_of_int {R : Type*} [CommRing R]
    {z zbar : R} {P N : ℤ} (hNP : IsCoprime N (2 * P))
    (hprod : z * zbar = (N : R)) (hsum : z + zbar = (2 * P : ℤ)) :
    IsCoprime z zbar := by
  apply isCoprime_of_mul_add
  simpa only [hprod, hsum] using hNP.intCast (R := R)

/-- Dirichlet's primitive and parity hypotheses imply
`gcd(P² + 7Q², 2P) = 1`. The exclusion `7 ∤ P` is exactly what removes the
ramified prime above `7`. -/
theorem norm_isCoprime_two_mul (P Q : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q)) (hseven : ¬(7 : ℤ) ∣ P) :
    IsCoprime (P ^ 2 + 7 * Q ^ 2) (2 * P) := by
  have hPseven : IsCoprime P (7 : ℤ) := by
    exact ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hseven).symm
  have hPnorm : IsCoprime P (P ^ 2 + 7 * Q ^ 2) := by
    have hPsevenQ : IsCoprime P (7 * Q ^ 2) :=
      hPseven.mul_right (hPQ.pow_right (n := 2))
    convert hPsevenQ.add_mul_right_right P using 1
    ring
  have hnormOdd : Odd (P ^ 2 + 7 * Q ^ 2) := by
    rcases hopposite with ⟨hPodd, hQeven⟩ | ⟨hPeven, hQodd⟩
    · rcases hPodd with ⟨p, rfl⟩
      rcases hQeven with ⟨q, rfl⟩
      refine ⟨2 * p ^ 2 + 2 * p + 14 * q ^ 2, ?_⟩
      ring
    · rcases hPeven with ⟨p, rfl⟩
      rcases hQodd with ⟨q, rfl⟩
      refine ⟨2 * p ^ 2 + 14 * q ^ 2 + 14 * q + 3, ?_⟩
      ring
  exact (Int.isCoprime_two_right.mpr hnormOdd).mul_right hPnorm.symm

/-- Ring-independent form of the coprime-conjugates lemma used in the
quadratic order. -/
theorem primitive_conjugates_isCoprime {R : Type*} [CommRing R]
    {z zbar : R} {P Q : ℤ} (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q)) (hseven : ¬(7 : ℤ) ∣ P)
    (hprod : z * zbar = (P ^ 2 + 7 * Q ^ 2 : ℤ))
    (hsum : z + zbar = (2 * P : ℤ)) : IsCoprime z zbar :=
  conjugates_isCoprime_of_int (norm_isCoprime_two_mul P Q hPQ hopposite hseven) hprod hsum

/-- The maximal order of `ℚ(√-7)` has only the two units `±1`. -/
theorem negSeven_unit_eq_one_or_neg_one (u : MaximalOrderˣ) :
    (u : MaximalOrder) = 1 ∨ (u : MaximalOrder) = -1 :=
  MaximalOrder.eq_one_or_neg_one_of_isUnit u.isUnit

/-- The two embedded conjugates attached to a primitive representation are
coprime in the maximal order. -/
theorem embedded_conjugates_isCoprime (P Q : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q)) (hseven : ¬(7 : ℤ) ∣ P) :
    IsCoprime
      (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7)))
      (star (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7)))) := by
  apply primitive_conjugates_isCoprime hPQ hopposite hseven
  · calc
      MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7)) *
          star (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7))) =
          (MaximalOrder.norm (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7))) : MaximalOrder) :=
        (MaximalOrder.norm_eq_mul_star _).symm
      _ = (P ^ 2 + 7 * Q ^ 2 : ℤ) := by rw [MaximalOrder.norm_embed]
  · ext
    · simp
      ring
    · simp

/-! The quotient of the maximal order by `2` is the Boolean ring
`F₂ × F₂`. The following small coordinate calculation records the only
consequence needed here: every positive power of an element is congruent to
the element itself modulo `2`. -/

private theorem int_sq_modEq_self (a : ℤ) : a ^ 2 ≡ a [ZMOD 2] := by
  rcases Int.even_or_odd' a with ⟨k, rfl | rfl⟩
  · rw [Int.modEq_iff_dvd]
    refine ⟨k - 2 * k ^ 2, ?_⟩
    ring
  · rw [Int.modEq_iff_dvd]
    refine ⟨-(2 * k ^ 2 + k), ?_⟩
    ring

private def ModEqTwo (x y : MaximalOrder) : Prop :=
  x.re ≡ y.re [ZMOD 2] ∧ x.im ≡ y.im [ZMOD 2]

private theorem modEqTwo_refl (x : MaximalOrder) : ModEqTwo x x :=
  ⟨Int.ModEq.rfl, Int.ModEq.rfl⟩

private theorem modEqTwo_trans {x y z : MaximalOrder}
    (hxy : ModEqTwo x y) (hyz : ModEqTwo y z) : ModEqTwo x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

private theorem modEqTwo_mul {a b c d : MaximalOrder}
    (hac : ModEqTwo a c) (hbd : ModEqTwo b d) : ModEqTwo (a * b) (c * d) := by
  constructor
  · simp only [MaximalOrder.re_mul]
    simpa only [mul_assoc] using
      (hac.1.mul hbd.1).sub ((hac.2.mul hbd.2).mul_left 2)
  · simp only [MaximalOrder.im_mul]
    exact ((hac.1.mul hbd.2).add (hac.2.mul hbd.1)).add (hac.2.mul hbd.2)

private theorem modEqTwo_sq_self (q : MaximalOrder) : ModEqTwo (q ^ 2) q := by
  constructor
  · simp only [pow_two, MaximalOrder.re_mul]
    have hz : 2 * (q.im * q.im) ≡ 0 [ZMOD 2] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-(q.im * q.im), by ring⟩
    simpa only [sq, mul_assoc, sub_zero] using (int_sq_modEq_self q.re).sub hz
  · simp only [pow_two, MaximalOrder.im_mul]
    have hz : q.re * q.im + q.im * q.re ≡ 0 [ZMOD 2] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-(q.re * q.im), by ring⟩
    simpa only [sq, zero_add] using hz.add (int_sq_modEq_self q.im)

private theorem modEqTwo_pow_self (q : MaximalOrder) :
    ∀ n : ℕ, n ≠ 0 → ModEqTwo (q ^ n) q := by
  intro n hn
  induction n with
  | zero => contradiction
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simpa using modEqTwo_refl q
      · rw [pow_succ]
        exact modEqTwo_trans (modEqTwo_mul (ih hn0) (modEqTwo_refl q))
          (by simpa [pow_two] using modEqTwo_sq_self q)

/-- A fourteenth power belongs to the suborder `ℤ[√-7]` exactly when its
root does. -/
theorem even_im_pow_fourteen_iff (q : MaximalOrder) :
    Even ((q ^ 14).im) ↔ Even q.im := by
  have hmod : (q ^ 14).im ≡ q.im [ZMOD 2] :=
    (modEqTwo_pow_self q 14 (by norm_num)).2
  constructor
  · intro h
    rw [even_iff_two_dvd] at h ⊢
    exact Int.modEq_zero_iff_dvd.mp
      (hmod.symm.trans (Int.modEq_zero_iff_dvd.mpr h))
  · intro h
    rw [even_iff_two_dvd] at h ⊢
    exact Int.modEq_zero_iff_dvd.mp
      (hmod.trans (Int.modEq_zero_iff_dvd.mpr h))

/-- Elements with even `ω`-coordinate are precisely those coming from the
suborder `ℤ[√-7]`. -/
theorem exists_eq_embed_of_even_im {q : MaximalOrder} (hq : Even q.im) :
    ∃ r s : ℤ, q = MaximalOrder.embed (⟨r, s⟩ : Zsqrtd (-7)) := by
  obtain ⟨s, hs⟩ := hq
  refine ⟨q.re + s, s, ?_⟩
  ext
  · simp
  · simp [hs, two_mul]

/-- Specialized signed power extraction in the maximal order. This is the
exact algebraic-number-theory conclusion needed by Dirichlet before proving
that the extracted root lies in the suborder `ℤ[√-7]`. -/
theorem exists_signed_fourteenthPower (P Q A : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q)) (hseven : ¬(7 : ℤ) ∣ P)
    (hnorm : P ^ 2 + 7 * Q ^ 2 = A ^ 14) :
    ∃ q : MaximalOrder,
      MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7)) = q ^ 14 ∨
        MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7)) = -(q ^ 14) := by
  apply exists_signed_pow_of_mul_eq_pow negSeven_unit_eq_one_or_neg_one
    (embedded_conjugates_isCoprime P Q hPQ hopposite hseven)
  calc
    MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7)) *
        star (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd (-7))) =
        (P ^ 2 + 7 * Q ^ 2 : ℤ) := by
      rw [← MaximalOrder.norm_eq_mul_star, MaximalOrder.norm_embed]
    _ = (A ^ 14 : ℤ) := by rw [hnorm]
    _ = (A : MaximalOrder) ^ 14 := by norm_cast

/-- Dirichlet's signed power extraction in its final historical form. Although
the factorization is performed in the maximal order, reduction modulo `2`
forces the extracted root back into `ℤ[√-7]`. -/
theorem exists_signed_fourteenthPower_in_suborder (P Q A : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q)) (hseven : ¬(7 : ℤ) ∣ P)
    (hnorm : P ^ 2 + 7 * Q ^ 2 = A ^ 14) :
    ∃ r s : ℤ,
      (⟨P, Q⟩ : Zsqrtd (-7)) = (⟨r, s⟩ : Zsqrtd (-7)) ^ 14 ∨
        (⟨P, Q⟩ : Zsqrtd (-7)) = -((⟨r, s⟩ : Zsqrtd (-7)) ^ 14) := by
  obtain ⟨q, hq | hq⟩ :=
    exists_signed_fourteenthPower P Q A hPQ hopposite hseven hnorm
  · have him := congrArg MaximalOrder.im hq
    simp only [MaximalOrder.embed_im] at him
    have hpowEven : Even ((q ^ 14).im) := by
      rw [even_iff_two_dvd]
      refine ⟨Q, ?_⟩
      omega
    obtain ⟨r, s, hrs⟩ :=
      exists_eq_embed_of_even_im ((even_im_pow_fourteen_iff q).mp hpowEven)
    refine ⟨r, s, Or.inl ?_⟩
    apply MaximalOrder.embed_injective
    simpa only [map_pow, ← hrs] using hq
  · have him := congrArg MaximalOrder.im hq
    simp only [MaximalOrder.embed_im, MaximalOrder.im_neg] at him
    have hpowEven : Even ((q ^ 14).im) := by
      rw [even_iff_two_dvd]
      refine ⟨-Q, ?_⟩
      omega
    obtain ⟨r, s, hrs⟩ :=
      exists_eq_embed_of_even_im ((even_im_pow_fourteen_iff q).mp hpowEven)
    refine ⟨r, s, Or.inr ?_⟩
    apply MaximalOrder.embed_injective
    simpa only [map_neg, map_pow, ← hrs] using hq

end Fermat.Fourteen.PowerExtraction
