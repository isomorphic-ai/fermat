import Fermat.Descent.Irregular.KummerTheorem

/-!
# Sun's depth-two Bernoulli interpolation

This module formalizes the positive-even, depth-two specialization of
Zhi-Hong Sun's equation (1.1) from *Congruences concerning Bernoulli numbers
and Bernoulli polynomials* (Discrete Applied Mathematics 105, 2000).
For a prime `p ≥ 5`, an even `b ≥ 4` with `(p - 1) ∤ b`, and `k ≥ 1`,
it proves

`B_(k(p-1)+b)/(k(p-1)+b) ≡
  k B_(p-1+b)/(p-1+b) - (k-1)(1-p^(b-1)) B_b/b (mod p²)`.

The proof is internal to the repository's Voronoi development. At one
common prime-power depth, both the Voronoi coefficient and its integer
quotient sum are affine in the progression parameter modulo `p²`.
Ordinary Kummer congruence makes the resulting cross-term vanish; a
primitive residue then cancels the remaining coefficient.
-/

namespace Fermat.Irregular.SunCongruence

theorem pow_eq_natCast_mul_sub_of_sub_one_sq_eq_zero
    {R : Type*} [CommRing R] (z : R) :
    ∀ {k : ℕ}, 1 ≤ k → (z - 1) ^ 2 = 0 →
      z ^ k = (k : R) * z - ((k - 1 : ℕ) : R) := by
  intro k hk hsq
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      rw [pow_succ, ih]
      push_cast
      have hcast : (((k - 1 : ℕ) : R) + 1) = (k : R) := by
        rw [Nat.cast_sub hk, Nat.cast_one]
        ring
      linear_combination (k : R) * hsq - z * hcast

theorem sub_one_sq_eq_zero_of_castHom_eq_one
    {p : ℕ} [Fact p.Prime] (z : ZMod (p ^ 2))
    (hz : ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p) z = 1) :
    (z - 1) ^ 2 = 0 := by
  have hzval : (z.val : ZMod p) = 1 := by
    rw [← ZMod.natCast_zmod_val z]
    simpa using hz
  have hdvd : (p : ℤ) ∣ (z.val : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr (by exact_mod_cast hzval)
  have hdvd2 : (p : ℤ) ^ 2 ∣ ((z.val : ℤ) - 1) ^ 2 :=
    pow_dvd_pow_of_dvd hdvd 2
  have hzero : ((((z.val : ℤ) - 1) ^ 2 : ℤ) : ZMod (p ^ 2)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
    norm_cast at hdvd2 ⊢
  calc
    (z - 1) ^ 2 = ((((z.val : ℤ) - 1) ^ 2 : ℤ) : ZMod (p ^ 2)) := by
      push_cast
      rw [ZMod.natCast_zmod_val z]
    _ = 0 := hzero

theorem pow_stride_affine_zmod_sq_of_not_dvd
    {p x b k : ℕ} [Fact p.Prime] (hx : ¬p ∣ x) (hk : 1 ≤ k) :
    (x : ZMod (p ^ 2)) ^ (b + k * (p - 1)) =
      (k : ZMod (p ^ 2)) * (x : ZMod (p ^ 2)) ^ (b + (p - 1)) -
        ((k - 1 : ℕ) : ZMod (p ^ 2)) * (x : ZMod (p ^ 2)) ^ b := by
  let y : ZMod (p ^ 2) := x
  let z : ZMod (p ^ 2) := y ^ (p - 1)
  have hxmod : (x : ZMod p) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff x p).mp hx
  have hzred :
      ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p) z = 1 := by
    simp only [z, y, map_pow, map_natCast]
    exact ZMod.pow_card_sub_one_eq_one hxmod
  have hzsq : (z - 1) ^ 2 = 0 :=
    sub_one_sq_eq_zero_of_castHom_eq_one z hzred
  have hzk : z ^ k = (k : ZMod (p ^ 2)) * z - (k - 1 : ℕ) :=
    pow_eq_natCast_mul_sub_of_sub_one_sq_eq_zero z hk hzsq
  simp only [z, y] at hzk ⊢
  have hpow : (x : ZMod (p ^ 2)) ^ (k * (p - 1)) =
      ((x : ZMod (p ^ 2)) ^ (p - 1)) ^ k := by
    rw [mul_comm, pow_mul]
  rw [pow_add, pow_add, hpow, hzk]
  ring

theorem natCast_pow_eq_zero_zmod_sq_of_dvd
    {p x e : ℕ} [Fact p.Prime] (hx : p ∣ x) (he : 2 ≤ e) :
    (x : ZMod (p ^ 2)) ^ e = 0 := by
  obtain ⟨q, rfl⟩ := hx
  rw [Nat.cast_mul, mul_pow]
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have heq : e = 2 + (e - 2) := by omega
  rw [heq, pow_add, hp2, zero_mul, zero_mul]

theorem pow_stride_affine_zmod_sq
    {p x b k : ℕ} [Fact p.Prime] (hb : 2 ≤ b) (hk : 1 ≤ k) :
    (x : ZMod (p ^ 2)) ^ (b + k * (p - 1)) =
      (k : ZMod (p ^ 2)) * (x : ZMod (p ^ 2)) ^ (b + (p - 1)) -
        ((k - 1 : ℕ) : ZMod (p ^ 2)) * (x : ZMod (p ^ 2)) ^ b := by
  by_cases hx : p ∣ x
  · rw [natCast_pow_eq_zero_zmod_sq_of_dvd hx (by omega : 2 ≤ b + k * (p - 1)),
      natCast_pow_eq_zero_zmod_sq_of_dvd hx (by omega : 2 ≤ b + (p - 1)),
      natCast_pow_eq_zero_zmod_sq_of_dvd hx hb]
    ring
  · exact pow_stride_affine_zmod_sq_of_not_dvd hx hk

open Fermat.Irregular.Voronoi
open Fermat.Irregular
open Finset

def sunIndex (p b j : ℕ) : ℕ := b + j * (p - 1)

theorem quotientPowerSum_sunIndex_affine_zmod_sq
    {p t a b k : ℕ} [Fact p.Prime] (hb : 3 ≤ b) (hk : 1 ≤ k) :
    (quotientPowerSum p t a (sunIndex p b k) : ZMod (p ^ 2)) =
      (k : ZMod (p ^ 2)) *
          (quotientPowerSum p t a (sunIndex p b 1) : ZMod (p ^ 2)) -
        ((k - 1 : ℕ) : ZMod (p ^ 2)) *
          (quotientPowerSum p t a (sunIndex p b 0) : ZMod (p ^ 2)) := by
  simp only [quotientPowerSum, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Int.cast_pow]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hpow := pow_stride_affine_zmod_sq
    (p := p) (x := a * m) (b := b - 1) (k := k) (by omega) hk
  have hidx0 : sunIndex p b 0 - 1 = b - 1 := by simp [sunIndex]
  have hidx1 : sunIndex p b 1 - 1 = (b - 1) + (p - 1) := by
    simp [sunIndex]
    omega
  have hidxk : sunIndex p b k - 1 = (b - 1) + k * (p - 1) := by
    simp [sunIndex]
    omega
  rw [hidx0, hidx1, hidxk]
  linear_combination (((a * m) / (p ^ t) : ℕ) : ZMod (p ^ 2)) * hpow

theorem coefficient_sunIndex_affine_zmod_sq
    {p a b k : ℕ} [Fact p.Prime] (hb : 2 ≤ b) (hk : 1 ≤ k) :
    (a : ZMod (p ^ 2)) ^ sunIndex p b k - 1 =
      (k : ZMod (p ^ 2)) *
          ((a : ZMod (p ^ 2)) ^ sunIndex p b 1 - 1) -
        ((k - 1 : ℕ) : ZMod (p ^ 2)) *
          ((a : ZMod (p ^ 2)) ^ sunIndex p b 0 - 1) := by
  have hpow := pow_stride_affine_zmod_sq
    (p := p) (x := a) (b := b) (k := k) hb hk
  have hidx0 : sunIndex p b 0 = b := by simp [sunIndex]
  have hidx1 : sunIndex p b 1 = b + (p - 1) := by simp [sunIndex]
  have hidxk : sunIndex p b k = b + k * (p - 1) := by rfl
  rw [hidx0, hidx1, hidxk]
  have hcast : (((k - 1 : ℕ) : ZMod (p ^ 2)) + 1) = k := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  linear_combination hpow - hcast

theorem sunIndex_modEq (p b j : ℕ) :
    sunIndex p b j ≡ b [MOD p - 1] := by
  rw [show sunIndex p b j = b + (p - 1) * j by
    simp [sunIndex, mul_comm]]
  simpa only [add_comm] using
    (Nat.ModEq.modulus_mul_add (m := p - 1) (a := j) (b := b))

theorem sunIndex_not_dvd {p b j : ℕ} (hnot : ¬(p - 1) ∣ b) :
    ¬(p - 1) ∣ sunIndex p b j := by
  intro hdvd
  apply hnot
  exact Nat.modEq_zero_iff_dvd.mp <|
    (sunIndex_modEq p b j).symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)

theorem sunIndex_even {p b j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hb : Even b) : Even (sunIndex p b j) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨r, hr⟩ := hpodd
  obtain ⟨q, hq⟩ := hb
  refine ⟨q + j * r, ?_⟩
  simp only [sunIndex, hr, hq]
  rw [show 2 * r + 1 - 1 = 2 * r by omega]
  ring

theorem hasPadicValAtLeast_natCast_mul_left
    {p : ℕ} [Fact p.Prime] {e : ℤ} (n : ℕ) {x : ℚ}
    (hx : HasPadicValAtLeast p e x) :
    HasPadicValAtLeast p e ((n : ℚ) * x) := by
  have hn := HasPadicValAtLeast.intCast (p := p) (n : ℤ)
  have h := hn.mul hx
  simpa using h

theorem assemble_sunInterpolation_of_unit
    {p k : ℕ} [Fact p.Prime]
    {C0 C1 Ck X0 X1 Xk T0 T1 Tk : ℚ}
    (hE0 : HasPadicValAtLeast p 2 (C0 * X0 - T0))
    (hE1 : HasPadicValAtLeast p 2 (C1 * X1 - T1))
    (hEk : HasPadicValAtLeast p 2 (Ck * Xk - Tk))
    (hCaff : HasPadicValAtLeast p 2
      (Ck - ((k : ℚ) * C1 - ((k - 1 : ℕ) : ℚ) * C0)))
    (hTaff : HasPadicValAtLeast p 2
      (Tk - ((k : ℚ) * T1 - ((k - 1 : ℕ) : ℚ) * T0)))
    (hCk1 : HasPadicValAtLeast p 1 (Ck - C1))
    (hX10 : HasPadicValAtLeast p 1 (X1 - X0))
    (hX0 : HasPadicValAtLeast p 0 X0)
    (hk : 1 ≤ k) (hCkne : Ck ≠ 0) (hCkval : padicValRat p Ck = 0) :
    HasPadicValAtLeast p 2
      (Xk - ((k : ℚ) * X1 - ((k - 1 : ℕ) : ℚ) * X0)) := by
  have hProducts : HasPadicValAtLeast p 2
      (Ck * Xk - (k : ℚ) * C1 * X1 +
        ((k - 1 : ℕ) : ℚ) * C0 * X0) := by
    have h := (hEk.sub (hasPadicValAtLeast_natCast_mul_left k hE1)).add
      (hasPadicValAtLeast_natCast_mul_left (k - 1) hE0) |>.add hTaff
    convert h using 1
    all_goals ring
  have hCross : HasPadicValAtLeast p 2
      ((k : ℚ) * ((Ck - C1) * (X1 - X0)) +
        (Ck - ((k : ℚ) * C1 - ((k - 1 : ℕ) : ℚ) * C0)) * X0) := by
    have h1 := hasPadicValAtLeast_natCast_mul_left k (hCk1.mul hX10)
    have h2 := hCaff.mul hX0
    exact h1.add h2
  have hCktimes : HasPadicValAtLeast p 2
      (Ck * (Xk - ((k : ℚ) * X1 - ((k - 1 : ℕ) : ℚ) * X0))) := by
    have h := hProducts.sub hCross
    rw [Nat.cast_sub hk, Nat.cast_one] at h ⊢
    convert h using 1
    all_goals ring
  exact Fermat.Irregular.KummerTheorem.HasPadicValAtLeast.of_mul_left_of_val_eq_zero
    hCkne hCkval hCktimes

theorem source_correction
    {p b k : ℕ} [Fact p.Prime] {X0 X1 Xk : ℚ}
    (hb : 3 ≤ b) (hk : 1 ≤ k)
    (hX0 : HasPadicValAtLeast p 0 X0)
    (h : HasPadicValAtLeast p 2
      (Xk - ((k : ℚ) * X1 - ((k - 1 : ℕ) : ℚ) * X0))) :
    HasPadicValAtLeast p 2
      (Xk - ((k : ℚ) * X1 -
        ((k : ℚ) - 1) * (1 - (p : ℚ) ^ (b - 1)) * X0)) := by
  have hp := HasPadicValAtLeast.primePow (p := p) (b - 1)
  have hpX : HasPadicValAtLeast p ((b - 1 : ℕ) : ℤ)
      ((p : ℚ) ^ (b - 1) * X0) := by
    simpa using hp.mul hX0
  have hpX2 := hpX.mono (by omega : (2 : ℤ) ≤ (b - 1 : ℕ))
  have hcor := hasPadicValAtLeast_natCast_mul_left (k - 1) hpX2
  rw [Nat.cast_sub hk, Nat.cast_one] at h hcor
  have hout := h.sub hcor
  convert hout using 1
  all_goals ring

theorem sunInterpolation_of_witness
    {p a b k s : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hb3 : 3 ≤ b) (hbeven : Even b) (hk : 1 ≤ k)
    (ha : a.Coprime p) (haPow : (a : ZMod p) ^ b ≠ 1)
    (hs0 : padicValNat p (sunIndex p b 0) ≤ s)
    (hs1 : padicValNat p (sunIndex p b 1) ≤ s)
    (hsk : padicValNat p (sunIndex p b k) ≤ s) :
    RationalModEq p 2
      (bernoulli (sunIndex p b k) / (sunIndex p b k : ℚ))
        ((k : ℚ) *
            (bernoulli (sunIndex p b 1) / (sunIndex p b 1 : ℚ)) -
          ((k - 1 : ℕ) : ℚ) *
            (bernoulli (sunIndex p b 0) / (sunIndex p b 0 : ℚ))) := by
  let n : ℕ → ℕ := fun j ↦ sunIndex p b j
  let C : ℕ → ℚ := fun j ↦ (a : ℚ) ^ n j - 1
  let X : ℕ → ℚ := fun j ↦ bernoulli (n j) / (n j : ℚ)
  let T : ℕ → ℚ := fun j ↦
    (quotientPowerSum p (s + 2) a (n j) : ℚ)

  have hnpos (j : ℕ) : 0 < n j := by
    simp only [n, sunIndex]
    omega
  have hneven (j : ℕ) : Even (n j) := by
    simpa only [n] using sunIndex_even (p := p) (j := j) hp5 hbeven

  have hE0 : HasPadicValAtLeast p 2 (C 0 * X 0 - T 0) := by
    simpa only [C, X, T, n, Nat.cast_ofNat] using
      normalized_voronoi_hasPadicValAtLeast
        (e := 2) hp5 (by omega) ha (hnpos 0) (hneven 0) hs0
  have hE1 : HasPadicValAtLeast p 2 (C 1 * X 1 - T 1) := by
    simpa only [C, X, T, n, Nat.cast_ofNat] using
      normalized_voronoi_hasPadicValAtLeast
        (e := 2) hp5 (by omega) ha (hnpos 1) (hneven 1) hs1
  have hEk : HasPadicValAtLeast p 2 (C k * X k - T k) := by
    simpa only [C, X, T, n, Nat.cast_ofNat] using
      normalized_voronoi_hasPadicValAtLeast
        (e := 2) hp5 (by omega) ha (hnpos k) (hneven k) hsk

  have hmod (i j : ℕ) : n i ≡ n j [MOD p - 1] :=
    (sunIndex_modEq p b i).trans (sunIndex_modEq p b j).symm
  have haPow0 : (a : ZMod p) ^ n 0 ≠ 1 := by
    simpa only [n, sunIndex, Nat.zero_mul, add_zero] using haPow
  have hcong01 : KummerCongruenceModPrime p (n 0) (n 1) :=
    Fermat.Irregular.KummerTheorem.kummerCongruenceModPrime_of_witness
      hp5 (hnpos 0) (hnpos 1) (hneven 0) (hneven 1) (hmod 0 1)
      ha haPow0
  have hcong0k : KummerCongruenceModPrime p (n 0) (n k) :=
    Fermat.Irregular.KummerTheorem.kummerCongruenceModPrime_of_witness
      hp5 (hnpos 0) (hnpos k) (hneven 0) (hneven k) (hmod 0 k)
      ha haPow0
  have hX0int : IsPIntegral p (X 0) := by
    simpa only [X] using hcong01.1
  have hX1int : IsPIntegral p (X 1) := by
    simpa only [X] using hcong01.2.1
  have hXkint : IsPIntegral p (X k) := by
    simpa only [X] using hcong0k.2.1
  have hX0 : HasPadicValAtLeast p 0 (X 0) := Or.inr hX0int
  have hX1 : HasPadicValAtLeast p 0 (X 1) := Or.inr hX1int
  have hXdiff : HasPadicValAtLeast p 1 (X 1 - X 0) := by
    have h : HasPadicValAtLeast p 1 (X 0 - X 1) := by
      simpa only [X, PadicValAtLeast, HasPadicValAtLeast,
        Nat.cast_ofNat, Nat.cast_one] using hcong01.2.2
    simpa only [neg_sub] using h.neg
  let Y : ℚ := (k : ℚ) * X 1 - ((k - 1 : ℕ) : ℚ) * X 0
  have hY : HasPadicValAtLeast p 0 Y := by
    dsimp only [Y]
    exact (hasPadicValAtLeast_natCast_mul_left k hX1).sub
      (hasPadicValAtLeast_natCast_mul_left (k - 1) hX0)
  have hYint : IsPIntegral p Y :=
    Fermat.Irregular.KummerTheorem.isPIntegral_of_hasPadicValAtLeast_zero hY

  have hTz := quotientPowerSum_sunIndex_affine_zmod_sq
    (p := p) (t := s + 2) (a := a) (b := b) (k := k) hb3 hk
  have hTz' :
      ((quotientPowerSum p (s + 2) a (n k) : ℤ) : ZMod (p ^ 2)) =
        (((k : ℤ) * quotientPowerSum p (s + 2) a (n 1) -
          ((k - 1 : ℕ) : ℤ) * quotientPowerSum p (s + 2) a (n 0) : ℤ) :
            ZMod (p ^ 2)) := by
    push_cast
    simpa only [n] using hTz
  have hTaffRaw := intCast_sub_hasPadicValAtLeast_of_zmod_eq hTz'
  have hTaff : HasPadicValAtLeast p 2
      (T k - ((k : ℚ) * T 1 - ((k - 1 : ℕ) : ℚ) * T 0)) := by
    simpa only [T, n, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Nat.cast_ofNat] using hTaffRaw

  let cInt : ℕ → ℤ := fun j ↦ (a : ℤ) ^ n j - 1
  have hCz := coefficient_sunIndex_affine_zmod_sq
    (p := p) (a := a) (b := b) (k := k) (by omega) hk
  have hCz' :
      (cInt k : ZMod (p ^ 2)) =
        (((k : ℤ) * cInt 1 - ((k - 1 : ℕ) : ℤ) * cInt 0 : ℤ) :
          ZMod (p ^ 2)) := by
    push_cast
    simpa only [cInt, C, n, Int.cast_sub, Int.cast_pow,
      Int.cast_natCast, Int.cast_one] using hCz
  have hCaffRaw := intCast_sub_hasPadicValAtLeast_of_zmod_eq hCz'
  have hCaff : HasPadicValAtLeast p 2
      (C k - ((k : ℚ) * C 1 - ((k - 1 : ℕ) : ℚ) * C 0)) := by
    simpa only [C, cInt, n, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Nat.cast_ofNat] using hCaffRaw

  have haNotDvd : ¬p ∣ a :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp ha.symm
  have haNonzero : (a : ZMod p) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff a p).mp haNotDvd
  have hpowk1 : (a : ZMod p) ^ n k = (a : ZMod p) ^ n 1 :=
    zmod_pow_eq_pow_of_modEq (hmod k 1) haNonzero
  have hCk1Z : (cInt k : ZMod p) = (cInt 1 : ZMod p) := by
    simp only [cInt, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one]
    exact congrArg (fun z : ZMod p ↦ z - 1) hpowk1
  have hCk1Raw :=
    Fermat.Irregular.KummerTheorem.intCast_sub_hasPadicValAtLeast_one hCk1Z
  have hCk1 : HasPadicValAtLeast p 1 (C k - C 1) := by
    simpa only [C, cInt, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one, Nat.cast_one] using hCk1Raw

  have hpowkb : (a : ZMod p) ^ n k = (a : ZMod p) ^ b :=
    zmod_pow_eq_pow_of_modEq (sunIndex_modEq p b k) haNonzero
  have hcKmod : (cInt k : ZMod p) ≠ 0 := by
    intro hzero
    apply haPow
    rw [← hpowkb]
    apply sub_eq_zero.mp
    simpa only [cInt, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] using hzero
  have hcKnotDvd : ¬(p : ℤ) ∣ cInt k := by
    intro hdvd
    exact hcKmod ((ZMod.intCast_zmod_eq_zero_iff_dvd (cInt k) p).2 hdvd)
  have hcKne : cInt k ≠ 0 := by
    intro hzero
    apply hcKnotDvd
    rw [hzero]
    exact dvd_zero _
  have hcKcast : (cInt k : ℚ) = C k := by
    simp only [cInt, C, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one]
  have hCkne : C k ≠ 0 := by
    rw [← hcKcast]
    exact Int.cast_ne_zero.mpr hcKne
  have hCkval : padicValRat p (C k) = 0 := by
    rw [← hcKcast, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hcKnotDvd]
    simp

  have hAffine : HasPadicValAtLeast p 2 (X k - Y) := by
    simpa only [Y] using assemble_sunInterpolation_of_unit
      hE0 hE1 hEk hCaff hTaff hCk1 hXdiff hX0 hk hCkne hCkval
  refine ⟨hXkint, hYint, ?_⟩
  simpa only [X, Y, n, PadicValAtLeast, HasPadicValAtLeast,
    Nat.cast_ofNat] using hAffine

/-- Sun's equation (1.1), at depth two, with an explicit Voronoi
cancelling residue and explicit common valuation bound. -/
theorem sunCongruence_of_witness_of_valBound
    {p a b k s : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hb3 : 3 ≤ b) (hbeven : Even b) (hk : 1 ≤ k)
    (ha : a.Coprime p) (haPow : (a : ZMod p) ^ b ≠ 1)
    (hs0 : padicValNat p (sunIndex p b 0) ≤ s)
    (hs1 : padicValNat p (sunIndex p b 1) ≤ s)
    (hsk : padicValNat p (sunIndex p b k) ≤ s) :
    RationalModEq p 2
      (bernoulli (sunIndex p b k) / (sunIndex p b k : ℚ))
      ((k : ℚ) *
          (bernoulli (sunIndex p b 1) / (sunIndex p b 1 : ℚ)) -
        ((k : ℚ) - 1) * (1 - (p : ℚ) ^ (b - 1)) *
          (bernoulli (sunIndex p b 0) / (sunIndex p b 0 : ℚ))) := by
  let n : ℕ → ℕ := fun j ↦ sunIndex p b j
  let X : ℕ → ℚ := fun j ↦ bernoulli (n j) / (n j : ℚ)
  let Y : ℚ := (k : ℚ) * X 1 - ((k - 1 : ℕ) : ℚ) * X 0
  let Yc : ℚ := (k : ℚ) * X 1 -
    ((k : ℚ) - 1) * (1 - (p : ℚ) ^ (b - 1)) * X 0
  have hunc : RationalModEq p 2 (X k) Y := by
    simpa only [X, Y, n] using sunInterpolation_of_witness
      hp5 hb3 hbeven hk ha haPow hs0 hs1 hsk
  have hnpos (j : ℕ) : 0 < n j := by
    simp only [n, sunIndex]
    omega
  have hneven (j : ℕ) : Even (n j) := by
    simpa only [n] using sunIndex_even (p := p) (j := j) hp5 hbeven
  have hmod01 : n 0 ≡ n 1 [MOD p - 1] :=
    (sunIndex_modEq p b 0).trans (sunIndex_modEq p b 1).symm
  have haPow0 : (a : ZMod p) ^ n 0 ≠ 1 := by
    simpa only [n, sunIndex, Nat.zero_mul, add_zero] using haPow
  have hcong01 : KummerCongruenceModPrime p (n 0) (n 1) :=
    Fermat.Irregular.KummerTheorem.kummerCongruenceModPrime_of_witness
      hp5 (hnpos 0) (hnpos 1) (hneven 0) (hneven 1) hmod01 ha haPow0
  have hX0 : HasPadicValAtLeast p 0 (X 0) := by
    right
    change IsPIntegral p (X 0)
    simpa only [X] using hcong01.1
  have huncVal : HasPadicValAtLeast p 2 (X k - Y) := by
    simpa only [PadicValAtLeast, HasPadicValAtLeast, Nat.cast_ofNat]
      using hunc.2.2
  have hcorrected : HasPadicValAtLeast p 2 (X k - Yc) := by
    simpa only [Y, Yc] using source_correction hb3 hk hX0 huncVal
  have hp := HasPadicValAtLeast.primePow (p := p) (b - 1)
  have hpX : HasPadicValAtLeast p ((b - 1 : ℕ) : ℤ)
      ((p : ℚ) ^ (b - 1) * X 0) := by
    simpa using hp.mul hX0
  have hpX0 : HasPadicValAtLeast p 0 ((p : ℚ) ^ (b - 1) * X 0) :=
    hpX.mono (by omega)
  have hcor0 := hasPadicValAtLeast_natCast_mul_left (k - 1) hpX0
  rw [Nat.cast_sub hk, Nat.cast_one] at hcor0
  have hY : HasPadicValAtLeast p 0 Y := Or.inr hunc.2.1
  have hYc : HasPadicValAtLeast p 0 Yc := by
    have h := hY.add hcor0
    dsimp only [Y] at h
    rw [Nat.cast_sub hk, Nat.cast_one] at h
    dsimp only [Yc]
    convert h using 1
    all_goals ring
  refine ⟨hunc.1,
    Fermat.Irregular.KummerTheorem.isPIntegral_of_hasPadicValAtLeast_zero hYc,
    ?_⟩
  simpa only [X, Yc, n, PadicValAtLeast, HasPadicValAtLeast,
    Nat.cast_ofNat] using hcorrected

/-- Sun's equation (1.1) modulo `p²`, in the range needed for irregular
Fermat channels.

The hypotheses `3 ≤ b` and `Even b` amount to the positive even range
`b ≥ 4`.  This is the range in which terms divisible by `p` vanish in the
depth-two quotient-sum interpolation. -/
theorem sunCongruence
    {p b k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hb3 : 3 ≤ b) (hbeven : Even b)
    (hnot : ¬(p - 1) ∣ b) (hk : 1 ≤ k) :
    RationalModEq p 2
      (bernoulli (sunIndex p b k) / (sunIndex p b k : ℚ))
      ((k : ℚ) *
          (bernoulli (sunIndex p b 1) / (sunIndex p b 1 : ℚ)) -
        ((k : ℚ) - 1) * (1 - (p : ℚ) ^ (b - 1)) *
          (bernoulli (sunIndex p b 0) / (sunIndex p b 0 : ℚ))) := by
  letI : IsCyclic (ZMod p)ˣ :=
    ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let a : ℕ := (g : ZMod p).val
  have ha : a.Coprime p := by
    simpa only [a] using ZMod.val_coe_unit_coprime g
  have haCast : (a : ZMod p) = (g : ZMod p) := by
    simpa only [a] using ZMod.natCast_zmod_val (g : ZMod p)
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : p.Prime)]
  have haPow : (a : ZMod p) ^ b ≠ 1 := by
    intro hpow
    have hunit : g ^ b = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, haCast] using hpow
    apply hnot
    rw [← horder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hunit
  let s : ℕ := max
    (max (padicValNat p (sunIndex p b 0))
      (padicValNat p (sunIndex p b 1)))
    (padicValNat p (sunIndex p b k))
  exact sunCongruence_of_witness_of_valBound
    (s := s) hp5 hb3 hbeven hk ha haPow (by simp [s]) (by simp [s])
      (by simp [s])

end Fermat.Irregular.SunCongruence
