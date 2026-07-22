import Fermat.Basic
import Fermat.Quadratic.GoldenUnits

/-!
# Fifth-power extraction in the golden quadratic order

This file formalizes the algebraic-number-theory step in Dirichlet's proof
for exponent five.  We factor in the maximal order `ℤ[φ]`, where
`φ = (1 + √5) / 2`.  The two parity cases differ only in whether
`P + Q√5` itself, or its half, is the algebraic integer whose norm is a
fifth power.
-/

namespace Fermat.Five.PowerExtraction

open Fermat.Quadratic.Golden

abbrev O5 := MaximalOrder

/-- The quartic factor in the `√5`-coordinate of a fifth power. -/
def quartic (g w : ℤ) : ℤ :=
  g ^ 4 + 10 * g ^ 2 * w ^ 2 + 5 * w ^ 4

/-- Natural-number version of `quartic`, used by the descent layer. -/
def quarticNat (g w : ℕ) : ℕ :=
  g ^ 4 + 10 * g ^ 2 * w ^ 2 + 5 * w ^ 4

@[simp, norm_cast] theorem intCast_quarticNat (g w : ℕ) :
    (quarticNat g w : ℤ) = quartic (g : ℤ) (w : ℤ) := by
  simp only [quarticNat, quartic]
  push_cast
  rfl

theorem quartic_pos_of_ne_zero_left (g w : ℤ) (hg : g ≠ 0) :
    0 < quartic g w := by
  have hg4 : 0 < g ^ 4 := by positivity
  have hcross : 0 ≤ g ^ 2 * w ^ 2 :=
    mul_nonneg (sq_nonneg g) (sq_nonneg w)
  have hw4 : 0 ≤ w ^ 4 := by positivity
  simp only [quartic]
  nlinarith

theorem quartic_natAbs (g w : ℤ) :
    quartic (g.natAbs : ℤ) (w.natAbs : ℤ) = quartic g w := by
  rw [Int.natCast_natAbs, Int.natCast_natAbs]
  have hg2 : |g| ^ 2 = g ^ 2 := sq_abs g
  have hw2 : |w| ^ 2 = w ^ 2 := sq_abs w
  have hg4 : |g| ^ 4 = g ^ 4 := by
    rw [show |g| ^ 4 = (|g| ^ 2) ^ 2 by ring, hg2]
    ring
  have hw4 : |w| ^ 4 = w ^ 4 := by
    rw [show |w| ^ 4 = (|w| ^ 2) ^ 2 by ring, hw2]
    ring
  simp only [quartic, hg2, hw2, hg4, hw4]

theorem zsqrtd_fifth_re (g w : ℤ) :
    ((⟨g, w⟩ : Zsqrtd 5) ^ 5).re =
      g ^ 5 + 50 * g ^ 3 * w ^ 2 + 125 * g * w ^ 4 := by
  norm_num [pow_succ]
  ring

theorem zsqrtd_fifth_im (g w : ℤ) :
    ((⟨g, w⟩ : Zsqrtd 5) ^ 5).im = 5 * w * quartic g w := by
  norm_num [quartic, pow_succ]
  ring

/-! ## Coprime conjugates -/

/-- If the product and sum of two elements are coprime, so are the elements. -/
theorem isCoprime_of_mul_add {R : Type*} [CommRing R] {x y : R}
    (h : IsCoprime (x * y) (x + y)) : IsCoprime x y := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * y + b, b, ?_⟩
  calc
    (a * y + b) * x + b * y = a * (x * y) + b * (x + y) := by ring
    _ = 1 := hab

/-- Transport an integer Bezout identity to two elements with the indicated
product and sum. -/
theorem conjugates_isCoprime_of_int {R : Type*} [CommRing R]
    {z zbar : R} {P N : ℤ} (hNP : IsCoprime N P)
    (hprod : z * zbar = (N : R)) (hsum : z + zbar = (P : R)) :
    IsCoprime z zbar := by
  apply isCoprime_of_mul_add
  simpa only [hprod, hsum] using hNP.intCast (R := R)

/-- Primitivity and `5 ∤ P` imply that `P` is coprime to
`P² - 5Q²`. -/
theorem norm_isCoprime_left (P Q : ℤ) (hPQ : IsCoprime P Q)
    (hfive : ¬(5 : ℤ) ∣ P) : IsCoprime (P ^ 2 - 5 * Q ^ 2) P := by
  have hPfive : IsCoprime P (5 : ℤ) :=
    ((show Prime (5 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hfive).symm
  have hPterm : IsCoprime P (5 * Q ^ 2) :=
    hPfive.mul_right (hPQ.pow_right (n := 2))
  have hPnorm : IsCoprime P (P ^ 2 - 5 * Q ^ 2) := by
    convert hPterm.neg_right.add_mul_right_right P using 1
    all_goals ring
  exact hPnorm.symm

/-- The embedded conjugates in the opposite-parity case are coprime. -/
theorem embedded_conjugates_isCoprime (P Q : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q))
    (hfive : ¬(5 : ℤ) ∣ P) :
    IsCoprime (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5))
      (star (MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5))) := by
  have hnormOdd : Odd (P ^ 2 - 5 * Q ^ 2) := by
    rcases hopposite with ⟨hPodd, hQeven⟩ | ⟨hPeven, hQodd⟩
    · rcases hPodd with ⟨p, rfl⟩
      rcases hQeven with ⟨q, rfl⟩
      refine ⟨2 * p ^ 2 + 2 * p - 10 * q ^ 2, ?_⟩
      ring
    · rcases hPeven with ⟨p, rfl⟩
      rcases hQodd with ⟨q, rfl⟩
      refine ⟨2 * p ^ 2 - 10 * q ^ 2 - 10 * q - 3, ?_⟩
      ring
  have hnormP := norm_isCoprime_left P Q hPQ hfive
  have hnormTwoP : IsCoprime (P ^ 2 - 5 * Q ^ 2) (2 * P) :=
    (Int.isCoprime_two_right.mpr hnormOdd).mul_right hnormP
  apply conjugates_isCoprime_of_int hnormTwoP
  · rw [← MaximalOrder.norm_eq_mul_star, MaximalOrder.norm_embed]
  · ext
    · simp
      ring
    · simp

/-- Coprime conjugates for the half-integral algebraic integer
`(P + Q√5) / 2 = a + Qφ`, where `P = 2a + Q`. -/
theorem half_conjugates_isCoprime (P Q c a : ℤ) (hPQ : IsCoprime P Q)
    (hfive : ¬(5 : ℤ) ∣ P) (ha : P = 2 * a + Q)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * c ^ 5) :
    IsCoprime (⟨a, Q⟩ : O5) (star (⟨a, Q⟩ : O5)) := by
  have hnormP : IsCoprime (P ^ 2 - 5 * Q ^ 2) P :=
    norm_isCoprime_left P Q hPQ hfive
  have hfour : IsCoprime (4 * c ^ 5) P := by simpa [hnorm] using hnormP
  have hcP : IsCoprime (c ^ 5) P := hfour.of_mul_left_right
  have hfourNorm : 4 * MaximalOrder.norm (⟨a, Q⟩ : O5) =
      P ^ 2 - 5 * Q ^ 2 := by
    rw [ha]
    simp only [MaximalOrder.norm]
    ring
  have hnormHalf : MaximalOrder.norm (⟨a, Q⟩ : O5) = c ^ 5 := by
    nlinarith
  apply conjugates_isCoprime_of_int hcP
  · rw [← MaximalOrder.norm_eq_mul_star, hnormHalf]
  · ext <;> simp
    omega

/-! ## Reduction modulo two -/

private theorem int_sq_modEq_self (a : ℤ) : a ^ 2 ≡ a [ZMOD 2] := by
  rcases Int.even_or_odd' a with ⟨k, rfl | rfl⟩
  · rw [Int.modEq_iff_dvd]
    refine ⟨k - 2 * k ^ 2, ?_⟩
    ring
  · rw [Int.modEq_iff_dvd]
    refine ⟨-(2 * k ^ 2 + k), ?_⟩
    ring

private def ModEqTwo (x y : O5) : Prop :=
  x.re ≡ y.re [ZMOD 2] ∧ x.im ≡ y.im [ZMOD 2]

private theorem modEqTwo_refl (x : O5) : ModEqTwo x x :=
  ⟨Int.ModEq.rfl, Int.ModEq.rfl⟩

private theorem modEqTwo_trans {x y z : O5}
    (hxy : ModEqTwo x y) (hyz : ModEqTwo y z) : ModEqTwo x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

private theorem modEqTwo_mul {a b c d : O5}
    (hac : ModEqTwo a c) (hbd : ModEqTwo b d) : ModEqTwo (a * b) (c * d) := by
  constructor
  · simp only [MaximalOrder.re_mul]
    exact (hac.1.mul hbd.1).add (hac.2.mul hbd.2)
  · simp only [MaximalOrder.im_mul]
    exact ((hac.1.mul hbd.2).add (hac.2.mul hbd.1)).add (hac.2.mul hbd.2)

private def frobTwo (q : O5) : O5 := ⟨q.re + q.im, q.im⟩

private theorem modEqTwo_sq_frob (q : O5) : ModEqTwo (q ^ 2) (frobTwo q) := by
  constructor
  · simp only [pow_two, MaximalOrder.re_mul, frobTwo]
    simpa only [sq] using (int_sq_modEq_self q.re).add (int_sq_modEq_self q.im)
  · simp only [pow_two, MaximalOrder.im_mul, frobTwo]
    have hz : q.re * q.im + q.im * q.re ≡ 0 [ZMOD 2] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-(q.re * q.im), by ring⟩
    simpa only [sq, zero_add] using hz.add (int_sq_modEq_self q.im)

private theorem modEqTwo_frob_frob (q : O5) : ModEqTwo (frobTwo (frobTwo q)) q := by
  constructor
  · simp only [frobTwo]
    rw [Int.modEq_iff_dvd]
    exact ⟨-q.im, by ring⟩
  · exact Int.ModEq.rfl

private theorem modEqTwo_fourth_self (q : O5) : ModEqTwo (q ^ 4) q := by
  have hsq : ModEqTwo (q ^ 2) (frobTwo q) := modEqTwo_sq_frob q
  have hfour_sq : ModEqTwo ((q ^ 2) ^ 2) ((frobTwo q) ^ 2) :=
    by simpa only [pow_two] using modEqTwo_mul hsq hsq
  have hfrob := modEqTwo_sq_frob (frobTwo q)
  have h : ModEqTwo ((q ^ 2) ^ 2) (frobTwo (frobTwo q)) :=
    modEqTwo_trans hfour_sq hfrob
  simpa [show q ^ 4 = (q ^ 2) ^ 2 by ring] using
    modEqTwo_trans h (modEqTwo_frob_frob q)

/-- The `φ`-coordinate of a fifth power has the same parity as that of its
base. -/
theorem odd_im_fifth_iff (q : O5) : Odd ((q ^ 5).im) ↔ Odd q.im := by
  have hfive : ModEqTwo (q ^ 5) (q ^ 2) := by
    rw [show q ^ 5 = q ^ 4 * q by ring, pow_two]
    exact modEqTwo_mul (modEqTwo_fourth_self q) (modEqTwo_refl q)
  have him : (q ^ 5).im ≡ q.im [ZMOD 2] :=
    hfive.2.trans (modEqTwo_sq_frob q).2
  constructor
  · intro h
    rw [← Int.not_even_iff_odd, even_iff_two_dvd] at h ⊢
    intro hq
    exact h (Int.modEq_zero_iff_dvd.mp
      (him.trans (Int.modEq_zero_iff_dvd.mpr hq)))
  · intro h
    rw [← Int.not_even_iff_odd, even_iff_two_dvd] at h ⊢
    intro hpow
    exact h (Int.modEq_zero_iff_dvd.mp
      (him.symm.trans (Int.modEq_zero_iff_dvd.mpr hpow)))

theorem even_im_fifth_iff (q : O5) : Even ((q ^ 5).im) ↔ Even q.im := by
  rw [← Int.not_odd_iff_even, ← Int.not_odd_iff_even, not_congr (odd_im_fifth_iff q)]

/-! ## The ramified prime above five -/

/-- In characteristic five, the fifth power of an element of the golden
order is rational: its `φ`-coordinate is divisible by five. -/
theorem five_dvd_im_fifth (q : O5) : (5 : ℤ) ∣ (q ^ 5).im := by
  refine ⟨q.re ^ 4 * q.im + 2 * q.re ^ 3 * q.im ^ 2 +
    4 * q.re ^ 2 * q.im ^ 3 + 3 * q.re * q.im ^ 4 + q.im ^ 5, ?_⟩
  norm_num [pow_succ]
  ring

/-- Among `1, φ, …, φ⁴`, only `1` can carry a fifth power to an element
whose `φ`-coordinate is divisible by five but whose rational coordinate is
not.  This is the finite congruence which removes the unit ambiguity. -/
theorem phi_remainder_eq_zero {q : O5} {r : ℕ} (hr : r < 5)
    (him : (5 : ℤ) ∣ ((MaximalOrder.phi ^ r) * q ^ 5).im)
    (hre : ¬(5 : ℤ) ∣ ((MaximalOrder.phi ^ r) * q ^ 5).re) : r = 0 := by
  let y : O5 := q ^ 5
  have hyim : (5 : ℤ) ∣ y.im := five_dvd_im_fifth q
  change (5 : ℤ) ∣ ((MaximalOrder.phi ^ r) * y).im at him
  change ¬(5 : ℤ) ∣ ((MaximalOrder.phi ^ r) * y).re at hre
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr_cases with rfl | rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    apply hre
    simpa [MaximalOrder.phi] using hyim
  · exfalso
    obtain ⟨a, ha⟩ := hyim
    obtain ⟨b, hb⟩ := him
    apply hre
    rw [MaximalOrder.phi_sq] at hb ⊢
    simp at hb ⊢
    rw [dvd_iff_exists_eq_mul_left]
    exact ⟨b - a, by omega⟩
  · exfalso
    obtain ⟨a, ha⟩ := hyim
    obtain ⟨b, hb⟩ := him
    apply hre
    rw [show MaximalOrder.phi ^ 3 = MaximalOrder.phi ^ 2 * MaximalOrder.phi by ring,
      MaximalOrder.phi_sq] at hb ⊢
    simp at hb ⊢
    rw [dvd_iff_exists_eq_mul_left]
    exact ⟨3 * b - y.re - 7 * a, by omega⟩
  · exfalso
    obtain ⟨a, ha⟩ := hyim
    obtain ⟨b, hb⟩ := him
    apply hre
    rw [show MaximalOrder.phi ^ 4 = MaximalOrder.phi ^ 2 * MaximalOrder.phi ^ 2 by ring,
      MaximalOrder.phi_sq] at hb ⊢
    simp at hb ⊢
    rw [dvd_iff_exists_eq_mul_left]
    exact ⟨4 * b - 2 * y.re - 17 * a, by omega⟩

/-- UFD extraction plus the finite modulo-five calculation.  The first
hypothesis is the unit classification modulo fifth powers; it is separated
out so that the algebraic extraction does not depend on how the unit theorem
is proved. -/
theorem exists_fifthPower_of_mul_eq_fifth
    (unit_decomposition : ∀ u : O5ˣ, ∃ v : O5ˣ, ∃ r : ℕ, r < 5 ∧
      (u : O5) = (v : O5) ^ 5 * MaximalOrder.phi ^ r)
    {alpha alphabar c : O5} (hcop : IsCoprime alpha alphabar)
    (hprod : alpha * alphabar = c ^ 5)
    (him : (5 : ℤ) ∣ alpha.im) (hre : ¬(5 : ℤ) ∣ alpha.re) :
    ∃ q : O5, alpha = q ^ 5 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨u, hu⟩ := hd
  obtain ⟨v, r, hr, huv⟩ := unit_decomposition u
  let q : O5 := (v : O5) * d
  have hform : alpha = MaximalOrder.phi ^ r * q ^ 5 := by
    calc
      alpha = d ^ 5 * (u : O5) := hu.symm
      _ = d ^ 5 * ((v : O5) ^ 5 * MaximalOrder.phi ^ r) := by rw [huv]
      _ = MaximalOrder.phi ^ r * q ^ 5 := by dsimp only [q]; ring
  have hrzero : r = 0 := by
    apply phi_remainder_eq_zero (q := q) hr
    · rw [← hform]
      exact him
    · rw [← hform]
      exact hre
  subst r
  exact ⟨q, by simpa using hform⟩

/-- Fifth-power extraction in the golden order, with the unit ambiguity
removed by the congruence at the ramified prime above five. -/
theorem exists_fifthPower_of_coprime_conjugates {alpha alphabar c : O5}
    (hcop : IsCoprime alpha alphabar) (hprod : alpha * alphabar = c ^ 5)
    (him : (5 : ℤ) ∣ alpha.im) (hre : ¬(5 : ℤ) ∣ alpha.re) :
    ∃ q : O5, alpha = q ^ 5 := by
  apply exists_fifthPower_of_mul_eq_fifth (alpha := alpha) (alphabar := alphabar)
    (c := c) ?_ hcop hprod him hre
  intro u
  obtain ⟨v, r, hr, huv⟩ := MaximalOrder.unit_eq_fifth_mul_phiUnit_pow_mod_five u
  refine ⟨v, r, hr, ?_⟩
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, MaximalOrder.coe_phiUnit] using
    congrArg Units.val huv

/-- An element of `ℤ[φ]` has even `φ`-coordinate exactly when it comes from
the suborder `ℤ[√5]`. -/
theorem exists_eq_embed_of_even_im {q : O5} (hq : Even q.im) :
    ∃ g w : ℤ, q = MaximalOrder.embed (⟨g, w⟩ : Zsqrtd 5) := by
  obtain ⟨w, hw⟩ := hq
  refine ⟨q.re + w, w, ?_⟩
  ext
  · simp
  · simp [hw, two_mul]

/-! ## Coordinate coprimality of an extracted root -/

/-- Coprime conjugates of an embedded element force its two suborder
coordinates to be coprime integers. -/
theorem suborder_coordinates_isCoprime (g w : ℤ)
    (h : IsCoprime (MaximalOrder.embed (⟨g, w⟩ : Zsqrtd 5))
      (star (MaximalOrder.embed (⟨g, w⟩ : Zsqrtd 5)))) :
    IsCoprime g w := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a.re + b.re, -a.re + 2 * a.im + b.re - 2 * b.im, ?_⟩
  have hre := congrArg MaximalOrder.re hab
  simp only [MaximalOrder.re_add, MaximalOrder.re_mul, MaximalOrder.re_one,
    MaximalOrder.embed_re, MaximalOrder.embed_im, MaximalOrder.re_star,
    MaximalOrder.im_star] at hre
  linarith

/-- In the half-integral case, coprime conjugates and odd rational
coordinate force the odd numerator coordinates to be coprime. -/
theorem half_coordinates_isCoprime (q : O5) (hqOdd : Odd (2 * q.re + q.im))
    (h : IsCoprime q (star q)) : IsCoprime (2 * q.re + q.im) q.im := by
  obtain ⟨k, hk⟩ := hqOdd
  obtain ⟨a, b, hab⟩ := h
  let X : ℤ := a.re + b.re
  let Y : ℤ := -a.re + b.re + 2 * a.im - 2 * b.im
  have hre := congrArg MaximalOrder.re hab
  simp only [MaximalOrder.re_add, MaximalOrder.re_mul, MaximalOrder.re_one,
    MaximalOrder.re_star, MaximalOrder.im_star] at hre
  have htwo : X * (2 * q.re + q.im) + Y * q.im = 2 := by
    dsimp [X, Y]
    linarith
  refine ⟨1 - k * X, -k * Y, ?_⟩
  calc
    (1 - k * X) * (2 * q.re + q.im) + -k * Y * q.im =
        (2 * q.re + q.im) - k *
          (X * (2 * q.re + q.im) + Y * q.im) := by ring
    _ = (2 * q.re + q.im) - k * 2 := by rw [htwo]
    _ = 1 := by omega

/-- Oddness of `g² - 5w²` is exactly the opposite-parity condition on
`g,w`. -/
theorem oppositeParity_of_odd_norm (g w : ℤ) (h : Odd (g ^ 2 - 5 * w ^ 2)) :
    (Odd g ∧ Even w) ∨ (Even g ∧ Odd w) := by
  rcases Int.even_or_odd g with hg | hg
  · right
    refine ⟨hg, ?_⟩
    rcases Int.even_or_odd w with hw | hw
    · exfalso
      apply (Int.not_even_iff_odd.mpr h)
      obtain ⟨a, rfl⟩ := hg
      obtain ⟨b, rfl⟩ := hw
      exact ⟨2 * a ^ 2 - 10 * b ^ 2, by ring⟩
    · exact hw
  · left
    refine ⟨hg, ?_⟩
    rcases Int.even_or_odd w with hw | hw
    · exact hw
    · exfalso
      apply (Int.not_even_iff_odd.mpr h)
      obtain ⟨a, rfl⟩ := hg
      obtain ⟨b, rfl⟩ := hw
      exact ⟨2 * a ^ 2 + 2 * a - 10 * b ^ 2 - 10 * b - 2, by ring⟩

/-- Expanding `embed(P,Q) = 2q⁵` in the odd/half-integral case gives the
historical denominator `16`. -/
theorem half_fifth_coordinate_formulas (P Q : ℤ) (q : O5)
    (h : MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5) = 2 * q ^ 5) :
    let g := 2 * q.re + q.im
    let w := q.im
    16 * P = g ^ 5 + 50 * g ^ 3 * w ^ 2 + 125 * g * w ^ 4 ∧
      16 * Q = 5 * w * quartic g w := by
  dsimp only
  have hre := congrArg MaximalOrder.re h
  have him := congrArg MaximalOrder.im h
  simp only [MaximalOrder.embed_re, MaximalOrder.embed_im, MaximalOrder.re_mul,
    MaximalOrder.im_mul, MaximalOrder.re_ofNat, MaximalOrder.im_ofNat] at hre him
  constructor
  · norm_num [pow_succ] at hre him ⊢
    ring_nf at hre him ⊢
    omega
  · norm_num [quartic, pow_succ] at hre him ⊢
    ring_nf at hre him ⊢
    omega

/-! ## The two historical extraction theorems -/

/-- In the opposite-parity case, `P + Q√5` is itself a fifth power in the
suborder `ℤ[√5]`. -/
theorem exists_oppositeParity_fifthPower (P Q c : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q))
    (hfiveQ : (5 : ℤ) ∣ Q) (hfiveP : ¬(5 : ℤ) ∣ P)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = c ^ 5) :
    ∃ g w : ℤ, IsCoprime g w ∧
      ((Odd g ∧ Even w) ∨ (Even g ∧ Odd w)) ∧
      (⟨P, Q⟩ : Zsqrtd 5) = (⟨g, w⟩ : Zsqrtd 5) ^ 5 := by
  let alpha : O5 := MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5)
  have hcop : IsCoprime alpha (star alpha) :=
    embedded_conjugates_isCoprime P Q hPQ hopposite hfiveP
  have hprod : alpha * star alpha = (c : O5) ^ 5 := by
    calc
      alpha * star alpha = (MaximalOrder.norm alpha : O5) :=
        (MaximalOrder.norm_eq_mul_star alpha).symm
      _ = (P ^ 2 - 5 * Q ^ 2 : ℤ) := by
        rw [MaximalOrder.norm_embed]
      _ = (c ^ 5 : ℤ) := by rw [hnorm]
      _ = (c : O5) ^ 5 := by norm_cast
  have him : (5 : ℤ) ∣ alpha.im := by
    obtain ⟨k, hk⟩ := hfiveQ
    refine ⟨2 * k, ?_⟩
    simp only [alpha, MaximalOrder.embed_im]
    omega
  have hre : ¬(5 : ℤ) ∣ alpha.re := by
    intro h
    apply hfiveP
    have hQ : (5 : ℤ) ∣ (⟨P, Q⟩ : Zsqrtd 5).im := hfiveQ
    have hdiff : (5 : ℤ) ∣ P - Q := by simpa only [alpha, MaximalOrder.embed_re] using h
    convert hdiff.add hQ using 1
    all_goals ring
  obtain ⟨q, hq⟩ :=
    exists_fifthPower_of_coprime_conjugates hcop hprod him hre
  have hqEven : Even q.im := by
    apply (even_im_fifth_iff q).mp
    rw [← hq]
    refine ⟨Q, ?_⟩
    simp only [alpha, MaximalOrder.embed_im]
    ring
  obtain ⟨g, w, hqw⟩ := exists_eq_embed_of_even_im hqEven
  have hz : (⟨P, Q⟩ : Zsqrtd 5) = (⟨g, w⟩ : Zsqrtd 5) ^ 5 := by
    apply MaximalOrder.embed_injective
    calc
      MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5) = alpha := rfl
      _ = q ^ 5 := hq
      _ = (MaximalOrder.embed (⟨g, w⟩ : Zsqrtd 5)) ^ 5 := by rw [← hqw]
      _ = MaximalOrder.embed ((⟨g, w⟩ : Zsqrtd 5) ^ 5) :=
        (map_pow MaximalOrder.embed _ _).symm
  have hqcop : IsCoprime q (star q) := by
    have hstar : star alpha = (star q) ^ 5 := by
      calc
        star alpha = star (q ^ 5) := congrArg star hq
        _ = (star q) ^ 5 := star_pow q 5
    rw [← IsCoprime.pow_iff (m := 5) (n := 5) (by norm_num) (by norm_num)]
    rw [← hq, ← hstar]
    exact hcop
  have hgw : IsCoprime g w := by
    apply suborder_coordinates_isCoprime g w
    simpa only [← hqw] using hqcop
  have hnormOdd : Odd (P ^ 2 - 5 * Q ^ 2) := by
    rcases hopposite with ⟨hPodd, hQeven⟩ | ⟨hPeven, hQodd⟩
    · obtain ⟨p, rfl⟩ := hPodd
      obtain ⟨q, rfl⟩ := hQeven
      exact ⟨2 * p ^ 2 + 2 * p - 10 * q ^ 2, by ring⟩
    · obtain ⟨p, rfl⟩ := hPeven
      obtain ⟨q, rfl⟩ := hQodd
      exact ⟨2 * p ^ 2 - 10 * q ^ 2 - 10 * q - 3, by ring⟩
  have hnormEq : P ^ 2 - 5 * Q ^ 2 = (g ^ 2 - 5 * w ^ 2) ^ 5 := by
    have h := congrArg MaximalOrder.norm hq
    rw [hqw, MaximalOrder.norm_pow, MaximalOrder.norm_embed] at h
    simpa only [alpha, MaximalOrder.norm_embed] using h
  have hrootOdd : Odd (g ^ 2 - 5 * w ^ 2) := by
    have hpowOdd : Odd ((g ^ 2 - 5 * w ^ 2) ^ 5) := by
      rwa [← hnormEq]
    exact (Int.odd_pow.mp hpowOdd).resolve_right (by norm_num)
  exact ⟨g, w, hgw, oppositeParity_of_odd_norm g w hrootOdd, hz⟩

/-- The explicit second-coordinate equation used in the opposite-parity
descent. -/
theorem exists_oppositeParity_coordinates (P Q c : ℤ) (hPQ : IsCoprime P Q)
    (hopposite : (Odd P ∧ Even Q) ∨ (Even P ∧ Odd Q))
    (hfiveQ : (5 : ℤ) ∣ Q) (hfiveP : ¬(5 : ℤ) ∣ P)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = c ^ 5) :
    ∃ g w : ℤ, IsCoprime g w ∧
      ((Odd g ∧ Even w) ∨ (Even g ∧ Odd w)) ∧
      P = g ^ 5 + 50 * g ^ 3 * w ^ 2 + 125 * g * w ^ 4 ∧
      Q = 5 * w * quartic g w := by
  obtain ⟨g, w, hgw, hparity, hpow⟩ :=
    exists_oppositeParity_fifthPower P Q c hPQ hopposite hfiveQ hfiveP hnorm
  refine ⟨g, w, hgw, hparity, ?_, ?_⟩
  · have := congrArg Zsqrtd.re hpow
    simpa only [Zsqrtd.re, zsqrtd_fifth_re] using this
  · have := congrArg Zsqrtd.im hpow
    simpa only [Zsqrtd.im, zsqrtd_fifth_im] using this

/-- In the odd-odd case, the half-integral algebraic integer
`(P + Q√5)/2` is a fifth power.  Clearing the denominator gives the exact
factor `16` in both integer coordinates. -/
theorem exists_odd_half_fifthPower (P Q c : ℤ) (hPQ : IsCoprime P Q)
    (hPodd : Odd P) (hQodd : Odd Q) (hfiveQ : (5 : ℤ) ∣ Q)
    (hfiveP : ¬(5 : ℤ) ∣ P)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * c ^ 5) :
    ∃ g w : ℤ, IsCoprime g w ∧ Odd g ∧ Odd w ∧
      MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5) =
        2 * (⟨(g - w) / 2, w⟩ : O5) ^ 5 ∧
      16 * P = g ^ 5 + 50 * g ^ 3 * w ^ 2 + 125 * g * w ^ 4 ∧
      16 * Q = 5 * w * quartic g w := by
  obtain ⟨p, hp⟩ := hPodd
  obtain ⟨s, hs⟩ := hQodd
  let a : ℤ := p - s
  have ha : P = 2 * a + Q := by
    dsimp only [a]
    omega
  let alpha : O5 := ⟨a, Q⟩
  have hcop : IsCoprime alpha (star alpha) :=
    half_conjugates_isCoprime P Q c a hPQ hfiveP ha hnorm
  have hfourNorm : 4 * MaximalOrder.norm alpha = P ^ 2 - 5 * Q ^ 2 := by
    rw [ha]
    simp only [alpha, MaximalOrder.norm]
    ring
  have hnormAlpha : MaximalOrder.norm alpha = c ^ 5 := by nlinarith
  have hprod : alpha * star alpha = (c : O5) ^ 5 := by
    rw [← MaximalOrder.norm_eq_mul_star, hnormAlpha]
    norm_cast
  have him : (5 : ℤ) ∣ alpha.im := by simpa only [alpha] using hfiveQ
  have hre : ¬(5 : ℤ) ∣ alpha.re := by
    intro hd
    apply hfiveP
    have htwo : (5 : ℤ) ∣ 2 * a := dvd_mul_of_dvd_right hd 2
    convert htwo.add hfiveQ using 1
  obtain ⟨q, hq⟩ :=
    exists_fifthPower_of_coprime_conjugates hcop hprod him hre
  have hqOdd : Odd q.im := by
    apply (odd_im_fifth_iff q).mp
    rw [← hq]
    simpa only [alpha] using (show Odd Q from ⟨s, hs⟩)
  let g : ℤ := 2 * q.re + q.im
  let w : ℤ := q.im
  have hgOdd : Odd g := by
    obtain ⟨k, hk⟩ := hqOdd
    refine ⟨q.re + k, ?_⟩
    dsimp only [g]
    omega
  have hwOdd : Odd w := by simpa only [w] using hqOdd
  have hqcop : IsCoprime q (star q) := by
    have hstar : star alpha = (star q) ^ 5 := by
      calc
        star alpha = star (q ^ 5) := congrArg star hq
        _ = (star q) ^ 5 := star_pow q 5
    rw [← IsCoprime.pow_iff (m := 5) (n := 5) (by norm_num) (by norm_num)]
    rw [← hq, ← hstar]
    exact hcop
  have hgw : IsCoprime g w := by
    simpa only [g, w] using half_coordinates_isCoprime q hgOdd hqcop
  have hembed : MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5) = 2 * q ^ 5 := by
    calc
      MaximalOrder.embed (⟨P, Q⟩ : Zsqrtd 5) = 2 * alpha := by
        ext <;> simp only [MaximalOrder.embed_re, MaximalOrder.embed_im,
          MaximalOrder.re_mul, MaximalOrder.im_mul, MaximalOrder.re_ofNat,
          MaximalOrder.im_ofNat, alpha]
        · omega
        · ring
      _ = 2 * q ^ 5 := by rw [hq]
  have hhalf : (⟨(g - w) / 2, w⟩ : O5) = q := by
    ext
    · dsimp only [g, w]
      omega
    · rfl
  have hcoords := half_fifth_coordinate_formulas P Q q hembed
  dsimp only [g, w] at hcoords
  exact ⟨g, w, hgw, hgOdd, hwOdd, by simpa only [hhalf] using hembed,
    hcoords.1, hcoords.2⟩

/-- Coordinate-only form of the odd/half-integral extraction. -/
theorem exists_odd_half_coordinates (P Q c : ℤ) (hPQ : IsCoprime P Q)
    (hPodd : Odd P) (hQodd : Odd Q) (hfiveQ : (5 : ℤ) ∣ Q)
    (hfiveP : ¬(5 : ℤ) ∣ P)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * c ^ 5) :
    ∃ g w : ℤ, IsCoprime g w ∧ Odd g ∧ Odd w ∧
      16 * P = g ^ 5 + 50 * g ^ 3 * w ^ 2 + 125 * g * w ^ 4 ∧
      16 * Q = 5 * w * quartic g w := by
  obtain ⟨g, w, hgw, hg, hw, -, hP, hQ⟩ :=
    exists_odd_half_fifthPower P Q c hPQ hPodd hQodd hfiveQ hfiveP hnorm
  exact ⟨g, w, hgw, hg, hw, hP, hQ⟩

/-! ## Natural-number interfaces for the descent -/

/-- Natural-number form of the odd/half-integral coordinate extraction. -/
theorem exists_odd_coordinates_nat (P Q c : ℕ) (_hPpos : 0 < P) (hQpos : 0 < Q)
    (hPQ : P.Coprime Q) (hPodd : Odd P) (hQodd : Odd Q)
    (hfiveQ : 5 ∣ Q) (hfiveP : ¬5 ∣ P)
    (hnorm : P ^ 2 = 5 * Q ^ 2 + 4 * c ^ 5) :
    ∃ g w : ℕ, 0 < g ∧ 0 < w ∧ g.Coprime w ∧ Odd g ∧ Odd w ∧
      ¬5 ∣ g ∧ 16 * Q = 5 * w * quarticNat g w := by
  have hPQz : IsCoprime (P : ℤ) (Q : ℤ) := hPQ.isCoprime
  have hPoddz : Odd (P : ℤ) := by exact_mod_cast hPodd
  have hQoddz : Odd (Q : ℤ) := by exact_mod_cast hQodd
  have hfiveQz : (5 : ℤ) ∣ (Q : ℤ) := by exact_mod_cast hfiveQ
  have hfivePz : ¬(5 : ℤ) ∣ (P : ℤ) := by
    intro h
    exact hfiveP (by exact_mod_cast h)
  have hnormCast : (P : ℤ) ^ 2 = 5 * (Q : ℤ) ^ 2 + 4 * (c : ℤ) ^ 5 := by
    exact_mod_cast hnorm
  have hnormz : (P : ℤ) ^ 2 - 5 * (Q : ℤ) ^ 2 = 4 * (c : ℤ) ^ 5 := by
    linarith
  obtain ⟨g, w, hgw, hg, hw, hPcoord, hQcoord⟩ :=
    exists_odd_half_coordinates (P : ℤ) (Q : ℤ) (c : ℤ) hPQz hPoddz hQoddz
      hfiveQz hfivePz hnormz
  have hgne : g ≠ 0 := by
    intro h
    subst g
    norm_num at hg
  have hquarticPos : 0 < quartic g w := quartic_pos_of_ne_zero_left g w hgne
  have hQcastPos : 0 < (Q : ℤ) := by exact_mod_cast hQpos
  have hwpos : 0 < w := by
    have hprodPos : 0 < w * quartic g w := by
      have hscaled : 0 < (16 : ℤ) * (Q : ℤ) := by positivity
      rw [hQcoord] at hscaled
      nlinarith
    rcases (mul_pos_iff.mp hprodPos) with h | h
    · exact h.1
    · exact (not_lt_of_ge (le_of_lt hquarticPos) h.2).elim
  have hnotg : ¬(5 : ℤ) ∣ g := by
    intro hfiveg
    apply hfivePz
    have hpoly : (5 : ℤ) ∣
        g ^ 5 + 50 * g ^ 3 * w ^ 2 + 125 * g * w ^ 4 := by
      convert hfiveg.mul_right (g ^ 4 + 50 * g ^ 2 * w ^ 2 + 125 * w ^ 4) using 1
      ring
    have h16P : (5 : ℤ) ∣ 16 * (P : ℤ) := by rwa [hPcoord]
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h16P with h16 | hP
    · norm_num at h16
    · exact hP
  have hEqZ : (16 : ℤ) * (Q : ℤ) =
      5 * (w.natAbs : ℤ) * (quarticNat g.natAbs w.natAbs : ℤ) := by
    rw [intCast_quarticNat, quartic_natAbs, Int.natCast_natAbs, abs_of_pos hwpos]
    exact hQcoord
  refine ⟨g.natAbs, w.natAbs, Int.natAbs_pos.mpr hgne,
    Int.natAbs_pos.mpr (ne_of_gt hwpos), Int.isCoprime_iff_nat_coprime.mp hgw,
    hg.natAbs, hw.natAbs, ?_, ?_⟩
  · intro h
    exact hnotg ((@Int.natCast_dvd g 5).mpr h)
  · exact_mod_cast hEqZ

/-- Natural-number form of the opposite-parity coordinate extraction.  The
parity orientation is forced by the second-coordinate equation. -/
theorem exists_oppositeParity_coordinates_nat (P Q c : ℕ)
    (_hPpos : 0 < P) (hQpos : 0 < Q) (hPQ : P.Coprime Q)
    (hPodd : Odd P) (hQeven : Even Q) (hfiveQ : 5 ∣ Q)
    (hfiveP : ¬5 ∣ P) (hnorm : P ^ 2 = 5 * Q ^ 2 + c ^ 5) :
    ∃ g w : ℕ, 0 < g ∧ 0 < w ∧ g.Coprime w ∧ Odd g ∧ Even w ∧
      ¬5 ∣ g ∧ Q = 5 * w * quarticNat g w := by
  have hPQz : IsCoprime (P : ℤ) (Q : ℤ) := hPQ.isCoprime
  have hPoddz : Odd (P : ℤ) := by exact_mod_cast hPodd
  have hQevenz : Even (Q : ℤ) := by exact_mod_cast hQeven
  have hfiveQz : (5 : ℤ) ∣ (Q : ℤ) := by exact_mod_cast hfiveQ
  have hfivePz : ¬(5 : ℤ) ∣ (P : ℤ) := by
    intro h
    exact hfiveP (by exact_mod_cast h)
  have hnormCast : (P : ℤ) ^ 2 = 5 * (Q : ℤ) ^ 2 + (c : ℤ) ^ 5 := by
    exact_mod_cast hnorm
  have hnormz : (P : ℤ) ^ 2 - 5 * (Q : ℤ) ^ 2 = (c : ℤ) ^ 5 := by
    linarith
  obtain ⟨g, w, hgw, hparity, hPcoord, hQcoord⟩ :=
    exists_oppositeParity_coordinates (P : ℤ) (Q : ℤ) (c : ℤ) hPQz
      (Or.inl ⟨hPoddz, hQevenz⟩) hfiveQz hfivePz hnormz
  have hrootParity : Odd g ∧ Even w := by
    rcases hparity with h | h
    · exact h
    · exfalso
      have hng : ¬Odd g := Int.not_odd_iff_even.mpr h.1
      have hnw : ¬Even w := Int.not_even_iff_odd.mpr h.2
      have hquarticOdd : Odd (quartic g w) := by
        norm_num [quartic, parity_simps, h.1, h.2, hng, hnw]
      have hQoddz : Odd (Q : ℤ) := by
        rw [hQcoord]
        exact Int.odd_mul.mpr
          ⟨Int.odd_mul.mpr ⟨by norm_num, h.2⟩, hquarticOdd⟩
      exact (Int.not_even_iff_odd.mpr hQoddz) hQevenz
  have hgne : g ≠ 0 := by
    intro hz
    subst g
    norm_num at hrootParity
  have hquarticPos : 0 < quartic g w := quartic_pos_of_ne_zero_left g w hgne
  have hQcastPos : 0 < (Q : ℤ) := by exact_mod_cast hQpos
  have hwpos : 0 < w := by
    have hprodPos : 0 < w * quartic g w := by
      rw [hQcoord] at hQcastPos
      nlinarith
    rcases (mul_pos_iff.mp hprodPos) with h | h
    · exact h.1
    · exact (not_lt_of_ge (le_of_lt hquarticPos) h.2).elim
  have hnotg : ¬(5 : ℤ) ∣ g := by
    intro hfiveg
    apply hfivePz
    rw [hPcoord]
    convert hfiveg.mul_right (g ^ 4 + 50 * g ^ 2 * w ^ 2 + 125 * w ^ 4) using 1
    ring
  have hEqZ : (Q : ℤ) =
      5 * (w.natAbs : ℤ) * (quarticNat g.natAbs w.natAbs : ℤ) := by
    rw [intCast_quarticNat, quartic_natAbs, Int.natCast_natAbs, abs_of_pos hwpos]
    exact hQcoord
  refine ⟨g.natAbs, w.natAbs, Int.natAbs_pos.mpr hgne,
    Int.natAbs_pos.mpr (ne_of_gt hwpos), Int.isCoprime_iff_nat_coprime.mp hgw,
    hrootParity.1.natAbs, hrootParity.2.natAbs, ?_, ?_⟩
  · intro h
    exact hnotg ((@Int.natCast_dvd g 5).mpr h)
  · exact_mod_cast hEqZ

end Fermat.Five.PowerExtraction
