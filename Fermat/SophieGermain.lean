import Fermat.Basic

/-!
# Sophie Germain's auxiliary-prime criterion

This file formalizes the elementary part of Sophie Germain's theorem.  Once
the two finite residue conditions at an auxiliary prime `q` are known, every
primitive solution of the Fermat equation for an odd prime exponent `p` is
in the second case: `p` divides one of the three entries.

The condition `q = 2 * k * p + 1` is the traditional way of finding and
checking the residue conditions.  It is not needed in the implication below
once those conditions have been stated directly in `ZMod q`.
-/

namespace Fermat.SophieGermain

open Finset

/-- The cofactor of `x + y` in `x ^ p + y ^ p` for odd `p`. -/
def cofactor {R : Type*} [CommRing R] (p : ℕ) (x y : R) : R :=
  ∑ i ∈ range p, x ^ i * (-y) ^ (p - 1 - i)

theorem add_mul_cofactor {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (x y : R) :
    (x + y) * cofactor p x y = x ^ p + y ^ p := by
  simpa only [cofactor, mul_comm, sub_neg_eq_add, hp.neg_pow, sub_neg_eq_add] using
    (geom_sum₂_mul x (-y) p)

theorem cofactor_eq_mul_pow_of_add_eq_zero {R : Type*} [CommRing R] {p : ℕ}
    {x y : R} (hxy : x + y = 0) :
    cofactor p x y = (p : R) * x ^ (p - 1) := by
  have hy : -y = x := by rw [eq_comm, ← sub_eq_zero]; simpa using hxy
  simp only [cofactor, hy, geom_sum₂_self]

/-- No two nonzero `p`-th powers modulo `q` differ by one. -/
def NoConsecutivePowers (p q : ℕ) : Prop :=
  ∀ x y : ZMod q, x ≠ 0 → y ≠ 0 → x ^ p ≠ 1 + y ^ p

/-- The exponent `p` is not itself a `p`-th power modulo `q`. -/
def ExponentNotPower (p q : ℕ) : Prop :=
  ∀ x : ZMod q, x ^ p ≠ (p : ZMod q)

/-- The first residue condition alone forces an auxiliary prime to divide
one of the entries of a Fermat solution. -/
theorem auxiliaryPrime_dvd_one {p q : ℕ} (hq : q.Prime)
    (hNC : NoConsecutivePowers p q) {x y z : ℤ}
    (hfermat : x ^ p + y ^ p = z ^ p) :
    (q : ℤ) ∣ x ∨ (q : ℤ) ∣ y ∨ (q : ℤ) ∣ z := by
  letI : Fact q.Prime := ⟨hq⟩
  by_contra h
  push Not at h
  obtain ⟨hx, hy, hz⟩ := h
  have hx0 : (x : ZMod q) ≠ 0 :=
    mt (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx
  have hy0 : (y : ZMod q) ≠ 0 :=
    mt (ZMod.intCast_zmod_eq_zero_iff_dvd y q).mp hy
  have hz0 : (z : ZMod q) ≠ 0 :=
    mt (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp hz
  have hmod : (x : ZMod q) ^ p + (y : ZMod q) ^ p = (z : ZMod q) ^ p := by
    simpa using congrArg (fun a : ℤ ↦ (a : ZMod q)) hfermat
  apply hNC ((z : ZMod q) / x) ((y : ZMod q) / x)
      (div_ne_zero hz0 hx0) (div_ne_zero hy0 hx0)
  calc
    ((z : ZMod q) / x) ^ p = (z : ZMod q) ^ p / x ^ p := div_pow _ _ _
    _ = ((x : ZMod q) ^ p + y ^ p) / x ^ p := by rw [hmod]
    _ = 1 + (y : ZMod q) ^ p / x ^ p := by
      rw [add_div, div_self (pow_ne_zero p hx0)]
    _ = 1 + ((y : ZMod q) / x) ^ p := by rw [div_pow]

/-- A form of the first residue condition adapted to the sum of three
`p`-th powers. -/
theorem zero_of_sum_three_powers {p q : ℕ} (hq : q.Prime) (hodd : Odd p)
    (hNC : NoConsecutivePowers p q) {a b c : ZMod q}
    (hsum : a ^ p + b ^ p + c ^ p = 0) :
    a = 0 ∨ b = 0 ∨ c = 0 := by
  letI : Fact q.Prime := ⟨hq⟩
  by_contra h
  push Not at h
  obtain ⟨ha, hb, hc⟩ := h
  apply hNC ((-a) / c) (b / c) (div_ne_zero (neg_ne_zero.mpr ha) hc) (div_ne_zero hb hc)
  have hneg : (-a) ^ p = b ^ p + c ^ p := by
    rw [hodd.neg_pow]
    linear_combination -hsum
  calc
    ((-a) / c) ^ p = (-a) ^ p / c ^ p := div_pow _ _ _
    _ = (b ^ p + c ^ p) / c ^ p := by rw [hneg]
    _ = 1 + b ^ p / c ^ p := by
      rw [add_div, div_self (pow_ne_zero p hc), add_comm]
    _ = 1 + (b / c) ^ p := by rw [div_pow]

private theorem prime_dvd_cofactor_of_dvd_add {p : ℕ} {r x y : ℤ}
    (hrxy : r ∣ x + y) (hrS : r ∣ cofactor p x y) :
    r ∣ (p : ℤ) * x ^ (p - 1) := by
  have hsub : r ∣ x - (-y) := by simpa only [sub_neg_eq_add] using hrxy
  exact (dvd_geom_sum₂_iff_of_dvd_sub' (n := p) hsub).mp (by simpa [cofactor] using hrS)

/-- In the first case, the two factors in the standard factorization are
coprime and hence are both signed `p`-th powers. -/
theorem extract_linear_and_cofactor {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {x y z : ℤ} (hxy : IsCoprime x y) (hpz : ¬(p : ℤ) ∣ z)
    (hfermat : x ^ p + y ^ p = z ^ p) :
    ∃ a α : ℤ, x + y = a ^ p ∧ cofactor p x y = α ^ p := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hprod : (x + y) * cofactor p x y = z ^ p :=
    (add_mul_cofactor hodd x y).trans hfermat
  have hprod0 : (x + y) * cofactor p x y ≠ 0 := by
    rw [hprod]
    exact pow_ne_zero _ fun hz ↦ hpz (hz ▸ dvd_zero _)
  have hcop : IsCoprime (x + y) (cofactor p x y) := by
    apply isCoprime_of_prime_dvd
    · exact fun h ↦ hprod0 (by simp only [h.1, h.2, mul_zero])
    · intro r hr hrxy hrS
      have hrmul := prime_dvd_cofactor_of_dvd_add hrxy hrS
      rcases hr.dvd_or_dvd hrmul with hrp | hrxpow
      · have hassoc : Associated r (p : ℤ) := hr.associated_of_dvd hpInt hrp
        have hpxy : (p : ℤ) ∣ x + y := hassoc.dvd_iff_dvd_left.mp hrxy
        have hpPow : (p : ℤ) ∣ z ^ p := by
          rw [← hprod]
          exact dvd_mul_of_dvd_left hpxy _
        exact hpz (hpInt.dvd_of_dvd_pow hpPow)
      · have hrx : r ∣ x := hr.dvd_of_dvd_pow hrxpow
        have hry : r ∣ y := by
          exact (dvd_add_right hrx).mp hrxy
        exact hr.not_unit (hxy.isUnit_of_dvd' hrx hry)
  obtain ⟨a, ha⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop hodd hprod
  obtain ⟨α, hα⟩ := Int.eq_pow_of_mul_eq_pow_odd_right hcop hodd hprod
  exact ⟨a, α, ha, hα⟩

private theorem firstCase_of_auxiliary_dvd_right {p q : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hq : q.Prime) (hNC : NoConsecutivePowers p q)
    (hNP : ExponentNotPower p q) {x y z : ℤ}
    (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ p + y ^ p = z ^ p) (hqz : (q : ℤ) ∣ z) :
    (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y ∨ (p : ℤ) ∣ z := by
  by_contra hfirst
  push Not at hfirst
  obtain ⟨hpx, hpy, hpz⟩ := hfirst
  obtain ⟨a, α, ha, hα⟩ :=
    extract_linear_and_cofactor hp hodd hxy hpz hfermat
  have hfermatZY : z ^ p + (-y) ^ p = x ^ p := by
    rw [hodd.neg_pow]
    omega
  obtain ⟨b, _, hb, _⟩ := extract_linear_and_cofactor hp hodd
    hyz.symm.neg_right hpx hfermatZY
  have hfermatZX : z ^ p + (-x) ^ p = y ^ p := by
    rw [hodd.neg_pow]
    omega
  obtain ⟨c, _, hc, _⟩ := extract_linear_and_cofactor hp hodd
    hxz.symm.neg_right hpy hfermatZX

  letI : Fact q.Prime := ⟨hq⟩
  have hqInt : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hz0 : (z : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mpr hqz
  have hx0 : (x : ZMod q) ≠ 0 := by
    intro hx0
    have hqx : (q : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx0
    exact hqInt.not_unit (hxz.isUnit_of_dvd' hqx hqz)
  have hy0 : (y : ZMod q) ≠ 0 := by
    intro hy0
    have hqy : (q : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd y q).mp hy0
    exact hqInt.not_unit (hyz.isUnit_of_dvd' hqy hqz)
  have haMod : (x : ZMod q) + y = (a : ZMod q) ^ p := by
    simpa using congrArg (fun t : ℤ ↦ (t : ZMod q)) ha
  have hbMod : (z : ZMod q) + -y = (b : ZMod q) ^ p := by
    simpa using congrArg (fun t : ℤ ↦ (t : ZMod q)) hb
  have hcMod : (z : ZMod q) + -x = (c : ZMod q) ^ p := by
    simpa using congrArg (fun t : ℤ ↦ (t : ZMod q)) hc
  have habc : (a : ZMod q) ^ p + (b : ZMod q) ^ p + (c : ZMod q) ^ p = 0 := by
    rw [← haMod, ← hbMod, ← hcMod, hz0]
    ring
  rcases zero_of_sum_three_powers hq hodd hNC habc with ha0 | hb0 | hc0
  · have hxy0 : (x : ZMod q) + y = 0 := by
      rw [haMod, ha0, zero_pow hp.ne_zero]
    have hαMod : (α : ZMod q) ^ p = (p : ZMod q) * (x : ZMod q) ^ (p - 1) := by
      calc
        (α : ZMod q) ^ p = (cofactor p x y : ℤ) := by
          simpa using congrArg (fun t : ℤ ↦ (t : ZMod q)) hα.symm
        _ = cofactor p (x : ZMod q) (y : ZMod q) := by simp [cofactor]
        _ = (p : ZMod q) * (x : ZMod q) ^ (p - 1) :=
          cofactor_eq_mul_pow_of_add_eq_zero hxy0
    have hxc : (x : ZMod q) = (-(c : ZMod q)) ^ p := by
      have hneg := congrArg Neg.neg hcMod
      simpa only [hz0, zero_add, neg_neg, hodd.neg_pow] using hneg
    have hxpow : (x : ZMod q) ^ (p - 1) = ((-(c : ZMod q)) ^ (p - 1)) ^ p := by
      rw [hxc]
      calc
        (((-c : ZMod q) ^ p) ^ (p - 1)) =
            (-c : ZMod q) ^ (p * (p - 1)) := (pow_mul _ _ _).symm
        _ = (-c : ZMod q) ^ ((p - 1) * p) := by rw [Nat.mul_comm]
        _ = (((-c : ZMod q) ^ (p - 1)) ^ p) := pow_mul _ _ _
    have hc0' : (c : ZMod q) ≠ 0 := by
      intro hc0'
      rw [hc0', neg_zero, zero_pow hp.ne_zero] at hxc
      exact hx0 hxc
    have hd0 : (-(c : ZMod q)) ^ (p - 1) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr hc0')
    apply hNP ((α : ZMod q) / ((-c : ZMod q) ^ (p - 1)))
    rw [div_pow, hαMod, hxpow]
    exact mul_div_cancel_right₀ _ (pow_ne_zero p hd0)
  · rw [hb0, zero_pow hp.ne_zero, hz0, zero_add] at hbMod
    exact hy0 (neg_eq_zero.mp hbMod)
  · rw [hc0, zero_pow hp.ne_zero, hz0, zero_add] at hcMod
    exact hx0 (neg_eq_zero.mp hcMod)

/-- Sophie Germain's auxiliary-prime criterion for a primitive integral
solution.  The conclusion is precisely that the first case is impossible. -/
theorem firstCase_of_pairwise_coprime {p q : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hq : q.Prime) (hNC : NoConsecutivePowers p q) (hNP : ExponentNotPower p q)
    {x y z : ℤ} (hxy : IsCoprime x y) (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    (hfermat : x ^ p + y ^ p = z ^ p) :
    (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y ∨ (p : ℤ) ∣ z := by
  rcases auxiliaryPrime_dvd_one hq hNC hfermat with hqx | hqy | hqz
  · have hperm : z ^ p + (-y) ^ p = x ^ p := by
      rw [hodd.neg_pow]
      omega
    rcases firstCase_of_auxiliary_dvd_right hp hodd hq hNC hNP
        hyz.symm.neg_right hxy.symm.neg_left hxz.symm hperm hqx with hpz | hpy | hpx
    · exact Or.inr (Or.inr hpz)
    · exact Or.inr (Or.inl (dvd_neg.mp hpy))
    · exact Or.inl hpx
  · have hperm : z ^ p + (-x) ^ p = y ^ p := by
      rw [hodd.neg_pow]
      omega
    rcases firstCase_of_auxiliary_dvd_right hp hodd hq hNC hNP
        hxz.symm.neg_right hxy.neg_left hyz.symm hperm hqy with hpz | hpx | hpy
    · exact Or.inr (Or.inr hpz)
    · exact Or.inl (dvd_neg.mp hpx)
    · exact Or.inr (Or.inl hpy)
  · exact firstCase_of_auxiliary_dvd_right hp hodd hq hNC hNP
      hxy hyz hxz hfermat hqz

end Fermat.SophieGermain
