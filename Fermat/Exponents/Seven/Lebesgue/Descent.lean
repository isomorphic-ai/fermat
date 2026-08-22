import Mathlib

/-!
# Lebesgue's corrected descent for exponent seven

This file formalizes Théorème I of Lebesgue's 1840 proof, together with the
repair published in his *Addition à la note sur l'équation x⁷+y⁷+z⁷=0*.
-/

namespace Fermat.Seven.Lebesgue

/-- The quartic family in Théorème I, written without truncated subtraction. -/
def DescentEquation (a p q r : ℕ) : Prop :=
  p ^ 2 + 2 ^ (2 * a) * 3 * 7 ^ 4 * q ^ 2 * r ^ 2 =
    q ^ 4 + 2 ^ (4 * a + 4) * 7 ^ 7 * r ^ 4

private theorem descentEquation_succ_iff (a p q r : ℕ) :
    DescentEquation (a + 1) p q r ↔
      p ^ 2 + 4 * (2 ^ a) ^ 2 * 3 * 7 ^ 4 * q ^ 2 * r ^ 2 =
        q ^ 4 + 256 * (2 ^ a) ^ 4 * 7 ^ 7 * r ^ 4 := by
  simp only [DescentEquation]
  ring_nf

private theorem exists_nat_pow_of_coprime_mul {a b c k : ℕ}
    (hab : a.Coprime b) (heq : a * b = c ^ k) : ∃ d : ℕ, a = d ^ k := by
  apply exists_eq_pow_of_mul_eq_pow
  · rw [show GCDMonoid.gcd a b = 1 by exact hab.gcd_eq_one]
    exact isUnit_one
  · exact heq

/-- Strip already allocated coefficients from two coprime factors of a
fourth power. -/
private theorem split_core_fourth {cf cg f g r : ℕ}
    (hcoeff : 0 < cf * cg) (hcf : cf ∣ f) (hcg : cg ∣ g)
    (hcop : f.Coprime g) (heq : f * g = (cf * cg) * r ^ 4) :
    ∃ s t : ℕ,
      f = cf * s ^ 4 ∧ g = cg * t ^ 4 ∧ r = s * t ∧ s.Coprime t := by
  obtain ⟨f₀, hf₀⟩ := hcf
  obtain ⟨g₀, hg₀⟩ := hcg
  have hf₀dvd : f₀ ∣ f := ⟨cf, by rw [hf₀]; ring⟩
  have hg₀dvd : g₀ ∣ g := ⟨cg, by rw [hg₀]; ring⟩
  have hcop₀ : f₀.Coprime g₀ := Nat.Coprime.of_dvd hf₀dvd hg₀dvd hcop
  have hcore : f₀ * g₀ = r ^ 4 := by
    apply Nat.eq_of_mul_eq_mul_left hcoeff
    calc
      (cf * cg) * (f₀ * g₀) = f * g := by rw [hf₀, hg₀]; ring
      _ = (cf * cg) * r ^ 4 := heq
  obtain ⟨s, hs⟩ := exists_nat_pow_of_coprime_mul hcop₀ hcore
  obtain ⟨t, ht⟩ := exists_nat_pow_of_coprime_mul hcop₀.symm (by
    simpa only [mul_comm] using hcore)
  have hr : r = s * t := by
    apply Nat.pow_left_injective (by norm_num : 4 ≠ 0)
    change r ^ 4 = (s * t) ^ 4
    rw [mul_pow, ← hs, ← ht, hcore]
  have hst : s.Coprime t := by
    rw [hs, ht] at hcop₀
    rwa [Nat.coprime_pow_left_iff (by norm_num : 0 < 4),
      Nat.coprime_pow_right_iff (by norm_num : 0 < 4)] at hcop₀
  exact ⟨s, t, by rw [hf₀, hs], by rw [hg₀, ht], hr, hst⟩

/-- The four allocations in Lebesgue's first difference-of-squares split.
The two factors are coprime, one receives the complete power of `2`, and
one receives the complete power `7 ^ 7`. -/
private theorem four_allocations {e f g r : ℕ} (hcop : f.Coprime g)
    (hsum : Odd (f + g))
    (hprod : f * g = (2 ^ e) ^ 4 * 7 ^ 7 * r ^ 4) :
    ∃ s t : ℕ, r = s * t ∧ s.Coprime t ∧
      ((f = s ^ 4 ∧ g = (2 ^ e) ^ 4 * 7 ^ 7 * t ^ 4) ∨
       (f = 7 ^ 7 * s ^ 4 ∧ g = (2 ^ e) ^ 4 * t ^ 4) ∨
       (f = (2 ^ e) ^ 4 * s ^ 4 ∧ g = 7 ^ 7 * t ^ 4) ∨
       (f = (2 ^ e) ^ 4 * 7 ^ 7 * s ^ 4 ∧ g = t ^ 4)) := by
  let K := (2 ^ e) ^ 4
  let L := 7 ^ 7
  have hKprod : K ∣ f * g := by
    rw [hprod]
    exact ⟨L * r ^ 4, by simp only [K, L]; ring⟩
  have hLprod : L ∣ f * g := by
    rw [hprod]
    exact ⟨K * r ^ 4, by simp only [K, L]; ring⟩
  have h7prod : 7 ∣ f * g := (dvd_pow (dvd_refl 7) (by norm_num)).trans hLprod
  have hKL : K.Coprime L := by
    simpa only [K, L] using
      ((((Nat.coprime_primes Nat.prime_two Nat.prime_seven).mpr (by norm_num)).pow_left e)
        |>.pow_left 4 |>.pow_right 7)
  have splitWith (cf cg : ℕ) (hcf : cf ∣ f) (hcg : cg ∣ g)
      (hcoeff : cf * cg = K * L) :
      ∃ s t : ℕ,
        f = cf * s ^ 4 ∧ g = cg * t ^ 4 ∧ r = s * t ∧ s.Coprime t := by
    apply split_core_fourth (cf := cf) (cg := cg)
    · rw [hcoeff]
      positivity
    · exact hcf
    · exact hcg
    · exact hcop
    · simpa only [hcoeff, K, L, mul_assoc] using hprod
  rcases Nat.even_or_odd f with hfEven | hfOdd
  · have hgOdd : Odd g := by
      apply Nat.not_even_iff_odd.mp
      intro hgEven
      exact (Nat.not_even_iff_odd.mpr hsum) (hfEven.add hgEven)
    have hKcopg : K.Coprime g := by
      simpa only [K] using (hgOdd.coprime_two_left.pow_left e).pow_left 4
    have hKf : K ∣ f := hKcopg.dvd_of_dvd_mul_right hKprod
    rcases Nat.prime_seven.dvd_mul.mp h7prod with h7f | h7g
    · have hn7g : ¬7 ∣ g := by
        intro h7g
        exact (Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨7, Nat.prime_seven, h7f, h7g⟩) hcop
      have hLf : L ∣ f :=
        ((Nat.prime_seven.coprime_iff_not_dvd.mpr hn7g).pow_left 7)
          |>.dvd_of_dvd_mul_right hLprod
      have hKLf : K * L ∣ f := hKL.mul_dvd_of_dvd_of_dvd hKf hLf
      obtain ⟨s, t, hfs, hgt, hr, hst⟩ :=
        splitWith (K * L) 1 hKLf (one_dvd g) (by ring)
      exact ⟨s, t, hr, hst, Or.inr (Or.inr (Or.inr ⟨by simpa [K, L] using hfs,
        by simpa using hgt⟩))⟩
    · have hn7f : ¬7 ∣ f := by
        intro h7f
        exact (Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨7, Nat.prime_seven, h7f, h7g⟩) hcop
      have hLg : L ∣ g :=
        ((Nat.prime_seven.coprime_iff_not_dvd.mpr hn7f).pow_left 7)
          |>.dvd_of_dvd_mul_left hLprod
      obtain ⟨s, t, hfs, hgt, hr, hst⟩ :=
        splitWith K L hKf hLg (by ring)
      exact ⟨s, t, hr, hst, Or.inr (Or.inr (Or.inl ⟨by simpa [K] using hfs,
        by simpa [L] using hgt⟩))⟩
  · have hgEven : Even g := (Nat.odd_add.mp hsum).mp hfOdd
    have hKcopf : K.Coprime f := by
      simpa only [K] using (hfOdd.coprime_two_left.pow_left e).pow_left 4
    have hKg : K ∣ g := hKcopf.dvd_of_dvd_mul_left hKprod
    rcases Nat.prime_seven.dvd_mul.mp h7prod with h7f | h7g
    · have hn7g : ¬7 ∣ g := by
        intro h7g
        exact (Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨7, Nat.prime_seven, h7f, h7g⟩) hcop
      have hLf : L ∣ f :=
        ((Nat.prime_seven.coprime_iff_not_dvd.mpr hn7g).pow_left 7)
          |>.dvd_of_dvd_mul_right hLprod
      obtain ⟨s, t, hfs, hgt, hr, hst⟩ :=
        splitWith L K hLf hKg (by ring)
      exact ⟨s, t, hr, hst, Or.inr (Or.inl ⟨by simpa [L] using hfs,
        by simpa [K] using hgt⟩)⟩
    · have hn7f : ¬7 ∣ f := by
        intro h7f
        exact (Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨7, Nat.prime_seven, h7f, h7g⟩) hcop
      have hLg : L ∣ g :=
        ((Nat.prime_seven.coprime_iff_not_dvd.mpr hn7f).pow_left 7)
          |>.dvd_of_dvd_mul_left hLprod
      have hKLg : K * L ∣ g := hKL.mul_dvd_of_dvd_of_dvd hKg hLg
      obtain ⟨s, t, hfs, hgt, hr, hst⟩ :=
        splitWith 1 (K * L) (one_dvd f) hKLg (by ring)
      exact ⟨s, t, hr, hst, Or.inl ⟨by simpa using hfs,
        by simpa [K, L] using hgt⟩⟩

/-- The analogous two-way allocation when the product contains no power of
`2`. -/
private theorem seven_allocations {f g r : ℕ} (hcop : f.Coprime g)
    (hprod : f * g = 7 ^ 7 * r ^ 4) :
    ∃ s t : ℕ, r = s * t ∧ s.Coprime t ∧
      ((f = s ^ 4 ∧ g = 7 ^ 7 * t ^ 4) ∨
       (f = 7 ^ 7 * s ^ 4 ∧ g = t ^ 4)) := by
  have h7prod : 7 ∣ f * g := by
    rw [hprod]
    exact (dvd_pow (dvd_refl 7) (by norm_num)).trans (dvd_mul_right (7 ^ 7) _)
  rcases Nat.prime_seven.dvd_mul.mp h7prod with h7f | h7g
  · have hn7g : ¬7 ∣ g := by
      intro h7g
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨7, Nat.prime_seven, h7f, h7g⟩) hcop
    have hLf : 7 ^ 7 ∣ f :=
      ((Nat.prime_seven.coprime_iff_not_dvd.mpr hn7g).pow_left 7)
        |>.dvd_of_dvd_mul_right (by rw [hprod]; exact dvd_mul_right (7 ^ 7) _)
    obtain ⟨s, t, hfs, hgt, hr, hst⟩ := split_core_fourth
      (cf := 7 ^ 7) (cg := 1) (by positivity) hLf (one_dvd g) hcop (by
        simpa only [mul_one] using hprod)
    exact ⟨s, t, hr, hst, Or.inr ⟨hfs, by simpa using hgt⟩⟩
  · have hn7f : ¬7 ∣ f := by
      intro h7f
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨7, Nat.prime_seven, h7f, h7g⟩) hcop
    have hLg : 7 ^ 7 ∣ g :=
      ((Nat.prime_seven.coprime_iff_not_dvd.mpr hn7f).pow_left 7)
        |>.dvd_of_dvd_mul_left (by rw [hprod]; exact dvd_mul_right (7 ^ 7) _)
    obtain ⟨s, t, hfs, hgt, hr, hst⟩ := split_core_fourth
      (cf := 1) (cg := 7 ^ 7) (by positivity) (one_dvd f) hLg hcop (by
        simpa only [one_mul] using hprod)
    exact ⟨s, t, hr, hst, Or.inl ⟨by simpa using hfs, hgt⟩⟩

private theorem zmod_eight_base :
    ∀ p q r : ZMod 8,
      (2 * p + 1) ^ 2 + 2 ^ (2 * 1) * 3 * 7 ^ 4 *
          (2 * q + 1) ^ 2 * (2 * r + 1) ^ 2 ≠
        (2 * q + 1) ^ 4 + 2 ^ (4 * 1 + 4) * 7 ^ 7 * (2 * r + 1) ^ 4 := by
  decide

/-- The bottom of Lebesgue's descent: `a = 1` is impossible modulo `8`. -/
private theorem base_case_impossible {p q r : ℕ} (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (heq : DescentEquation 1 p q r) : False := by
  obtain ⟨p₀, rfl⟩ := hp
  obtain ⟨q₀, rfl⟩ := hq
  obtain ⟨r₀, rfl⟩ := hr
  apply zmod_eight_base (p₀ : ZMod 8) (q₀ : ZMod 8) (r₀ : ZMod 8)
  simpa only [DescentEquation, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod 8)) heq

private theorem zmod_seven_zero_of_sq_eq_fourth :
    ∀ p q : ZMod 7, p ^ 2 = q ^ 4 → p = 0 → q = 0 := by
  decide

private theorem not_seven_dvd_p {a p q r : ℕ} (hpq : p.Coprime q)
    (heq : DescentEquation a p q r) : ¬7 ∣ p := by
  intro h7p
  have hmod := congrArg (fun n : ℕ => (n : ZMod 7)) heq
  have hpqmod : (p : ZMod 7) ^ 2 = (q : ZMod 7) ^ 4 := by
    have hbase : (7 : ZMod 7) = 0 := by decide
    simpa only [DescentEquation, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, hbase, zero_pow (by norm_num : 4 ≠ 0),
      zero_pow (by norm_num : 7 ≠ 0), mul_zero, zero_mul, add_zero] using hmod
  have hpzero : (p : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff p 7).mpr h7p
  have hqzero : (q : ZMod 7) = 0 :=
    zmod_seven_zero_of_sq_eq_fourth _ _ hpqmod hpzero
  have h7q : 7 ∣ q := (ZMod.natCast_eq_zero_iff q 7).mp hqzero
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨7, Nat.prime_seven, h7p, h7q⟩) hpq

/-- The four signed values of the middle term obtained from Lebesgue's first
factorization. -/
private theorem first_signed_allocations {a p q r : ℕ} (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hpq : p.Coprime q) (hpr : p.Coprime r)
    (heq : DescentEquation (a + 1) p q r) :
    let U : ℤ :=
      (q : ℤ) ^ 2 - 2 * (2 ^ a : ℤ) ^ 2 * 3 * 7 ^ 4 * (r : ℤ) ^ 2
    ∃ s t : ℕ, r = s * t ∧ s.Coprime t ∧
      (U = (s : ℤ) ^ 4 - (2 ^ a : ℤ) ^ 4 * 7 ^ 7 * (t : ℤ) ^ 4 ∨
       U = 7 ^ 7 * (s : ℤ) ^ 4 - (2 ^ a : ℤ) ^ 4 * (t : ℤ) ^ 4 ∨
       U = (2 ^ a : ℤ) ^ 4 * (s : ℤ) ^ 4 - 7 ^ 7 * (t : ℤ) ^ 4 ∨
       U = (2 ^ a : ℤ) ^ 4 * 7 ^ 7 * (s : ℤ) ^ 4 - (t : ℤ) ^ 4) := by
  let T := 2 ^ a
  let U : ℤ := (q : ℤ) ^ 2 - 2 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (r : ℤ) ^ 2
  let C := T ^ 4 * 7 ^ 7 * r ^ 4
  have hpoly := (descentEquation_succ_iff a p q r).mp heq
  have hpolyInt :
      (p : ℤ) ^ 2 + 4 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (q : ℤ) ^ 2 * (r : ℤ) ^ 2 =
        (q : ℤ) ^ 4 + 256 * (T : ℤ) ^ 4 * 7 ^ 7 * (r : ℤ) ^ 4 := by
    exact_mod_cast hpoly
  have hsqInt : (p : ℤ) ^ 2 = U ^ 2 + 4 * (C : ℤ) := by
    simp only [U, C]
    push_cast
    nlinarith [hpolyInt]
  let u := U.natAbs
  have huSq : (u : ℤ) ^ 2 = U ^ 2 := by
    rw [show (u : ℤ) = |U| by exact Int.natCast_natAbs U, sq_abs]
  have hsqNat : p ^ 2 = u ^ 2 + 4 * C := by
    have hsqCast : (p : ℤ) ^ 2 = (u : ℤ) ^ 2 + 4 * (C : ℤ) := by
      rw [hsqInt, huSq]
    exact_mod_cast hsqCast
  have hCpos : 0 < C := by
    simp only [C]
    have hrpos : 0 < r := hr.pos
    positivity
  have hu_lt_p : u < p := by
    nlinarith
  have hUodd : Odd U := by
    apply (hq.natCast.pow).sub_even
    rw [show 2 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (r : ℤ) ^ 2 =
      2 * ((T : ℤ) ^ 2 * 3 * 7 ^ 4 * (r : ℤ) ^ 2) by ring]
    exact even_two.mul_right _
  have huOdd : Odd u := hUodd.natAbs
  obtain ⟨f, hf⟩ := (hp.add_odd huOdd).two_dvd
  obtain ⟨g, hg⟩ := (Nat.Odd.sub_odd hp huOdd).two_dvd
  have hsum : f + g = p := by omega
  have hprod : f * g = C := by nlinarith
  have hcop : f.Coprime g := by
    by_contra hn
    obtain ⟨l, hl, hlf, hlg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hlp : l ∣ p := by
      rw [← hsum]
      exact dvd_add hlf hlg
    have hlwhole : l ∣ (T ^ 4) * (7 ^ 7 * r ^ 4) := by
      rw [← show C = T ^ 4 * (7 ^ 7 * r ^ 4) by simp only [C]; ring, ← hprod]
      exact hlf.trans (dvd_mul_right f g)
    rcases hl.dvd_mul.mp hlwhole with hlT | hlrest
    · have hlTwoPow : l ∣ T := hl.dvd_of_dvd_pow hlT
      have hlTwo : l ∣ 2 := by
        simp only [T] at hlTwoPow
        exact hl.dvd_of_dvd_pow hlTwoPow
      have hleq : l = 2 :=
        (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo
      have h2p : 2 ∣ p := by simpa only [hleq] using hlp
      exact (Nat.not_even_iff_odd.mpr hp) (even_iff_two_dvd.mpr h2p)
    · rcases hl.dvd_mul.mp hlrest with hlSevenPow | hlrPow
      · have hlSeven : l ∣ 7 := hl.dvd_of_dvd_pow hlSevenPow
        have hleq : l = 7 :=
          (Nat.prime_dvd_prime_iff_eq hl Nat.prime_seven).mp hlSeven
        exact not_seven_dvd_p hpq heq (by simpa only [hleq] using hlp)
      · have hlr : l ∣ r := hl.dvd_of_dvd_pow hlrPow
        exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hlp, hlr⟩) hpr
  have hsign : U = (f : ℤ) - (g : ℤ) ∨ U = (g : ℤ) - (f : ℤ) := by
    rcases le_total 0 U with hU | hU
    · left
      have hcast : (u : ℤ) = U := by
        simp only [u, Int.natCast_natAbs, abs_of_nonneg hU]
      have hfg : f = g + u := by omega
      rw [hfg]
      push_cast
      omega
    · right
      have hcast : (u : ℤ) = -U := by
        simp only [u, Int.natCast_natAbs, abs_of_nonpos hU]
      have hfg : f = g + u := by omega
      rw [hfg]
      push_cast
      omega
  have hsumOdd : Odd (f + g) := by rw [hsum]; exact hp
  obtain ⟨s, t, hrst, hst, hall⟩ := four_allocations hcop hsumOdd (by
    simpa only [C, T, mul_assoc] using hprod)
  rcases hsign with hsign | hsign
  · rcases hall with h₁ | h₂ | h₃ | h₄
    · exact ⟨s, t, hrst, hst, Or.inl (by
        change U = _
        rw [hsign, h₁.1, h₁.2]; push_cast; simp)⟩
    · exact ⟨s, t, hrst, hst, Or.inr (Or.inl (by
        change U = _
        rw [hsign, h₂.1, h₂.2]; push_cast; simp))⟩
    · exact ⟨s, t, hrst, hst, Or.inr (Or.inr (Or.inl (by
        change U = _
        rw [hsign, h₃.1, h₃.2]; push_cast; simp)))⟩
    · exact ⟨s, t, hrst, hst, Or.inr (Or.inr (Or.inr (by
        change U = _
        rw [hsign, h₄.1, h₄.2]; push_cast; simp)))⟩
  · rcases hall with h₁ | h₂ | h₃ | h₄
    · exact ⟨t, s, by simpa only [mul_comm] using hrst, hst.symm,
        Or.inr (Or.inr (Or.inr (by
          change U = _
          rw [hsign, h₁.1, h₁.2]; push_cast; simp)))⟩
    · exact ⟨t, s, by simpa only [mul_comm] using hrst, hst.symm,
        Or.inr (Or.inr (Or.inl (by
          change U = _
          rw [hsign, h₂.1, h₂.2]; push_cast; simp)))⟩
    · exact ⟨t, s, by simpa only [mul_comm] using hrst, hst.symm,
        Or.inr (Or.inl (by
          change U = _
          rw [hsign, h₃.1, h₃.2]; push_cast; simp))⟩
    · exact ⟨t, s, by simpa only [mul_comm] using hrst, hst.symm,
        Or.inl (by
          change U = _
          rw [hsign, h₄.1, h₄.2]; push_cast; simp)⟩

private theorem zmod_four_two_pow_sq_eq_zero {a : ℕ} (ha : 0 < a) :
    ((2 : ZMod 4) ^ a) ^ 2 = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  rw [pow_succ]
  calc
    ((2 : ZMod 4) ^ b * 2) ^ 2 = 4 * ((2 : ZMod 4) ^ b) ^ 2 := by ring
    _ = 0 := by rw [show (4 : ZMod 4) = 0 by decide, zero_mul]

private theorem zmod_four_two_pow_fourth_eq_zero {a : ℕ} (ha : 0 < a) :
    ((2 : ZMod 4) ^ a) ^ 4 = 0 := by
  calc
    ((2 : ZMod 4) ^ a) ^ 4 = (((2 : ZMod 4) ^ a) ^ 2) ^ 2 := by ring
    _ = 0 := by rw [zmod_four_two_pow_sq_eq_zero ha]; norm_num

private theorem zmod_four_initial_second :
    ∀ q s : ZMod 4, (2 * q + 1) ^ 2 ≠ 7 ^ 7 * (2 * s + 1) ^ 4 := by
  decide

private theorem initial_second_allocation_impossible {a q s t : ℕ}
    (ha : 0 < a) (hq : Odd q) (hs : Odd s)
    (heq :
      (q : ℤ) ^ 2 - 2 * (2 ^ a : ℤ) ^ 2 * 3 * 7 ^ 4 * (s * t : ℕ) ^ 2 =
        7 ^ 7 * (s : ℤ) ^ 4 - (2 ^ a : ℤ) ^ 4 * (t : ℤ) ^ 4) : False := by
  obtain ⟨q₀, rfl⟩ := hq
  obtain ⟨s₀, rfl⟩ := hs
  apply zmod_four_initial_second (q₀ : ZMod 4) (s₀ : ZMod 4)
  have hmod := congrArg (fun z : ℤ => (z : ZMod 4)) heq
  push_cast at hmod
  rw [zmod_four_two_pow_sq_eq_zero ha,
    zmod_four_two_pow_fourth_eq_zero ha] at hmod
  norm_num at hmod
  exact hmod

private theorem zmod_four_initial_fourth :
    ∀ q t : ZMod 4, (2 * q + 1) ^ 2 ≠ -(2 * t + 1) ^ 4 := by
  decide

private theorem initial_fourth_allocation_impossible {a q s t : ℕ}
    (ha : 0 < a) (hq : Odd q) (ht : Odd t)
    (heq :
      (q : ℤ) ^ 2 - 2 * (2 ^ a : ℤ) ^ 2 * 3 * 7 ^ 4 * (s * t : ℕ) ^ 2 =
        (2 ^ a : ℤ) ^ 4 * 7 ^ 7 * (s : ℤ) ^ 4 - (t : ℤ) ^ 4) : False := by
  obtain ⟨q₀, rfl⟩ := hq
  obtain ⟨t₀, rfl⟩ := ht
  apply zmod_four_initial_fourth (q₀ : ZMod 4) (t₀ : ZMod 4)
  have hmod := congrArg (fun z : ℤ => (z : ZMod 4)) heq
  push_cast at hmod
  rw [zmod_four_two_pow_sq_eq_zero ha,
    zmod_four_two_pow_fourth_eq_zero ha] at hmod
  norm_num at hmod
  exact hmod

private theorem zmod_four_second_stage :
    ∀ s u : ZMod 4, (2 * s + 1) ^ 2 ≠ 7 ^ 7 * (2 * u + 1) ^ 4 := by
  decide

private theorem second_stage_allocation_impossible {a s u v : ℕ}
    (ha : 0 < a) (hs : Odd s) (hu : Odd u)
    (heq : s ^ 2 + (2 ^ a) ^ 2 * 3 * 7 ^ 4 * u ^ 2 * v ^ 2 =
      7 ^ 7 * u ^ 4 + (2 ^ (a + 1)) ^ 4 * v ^ 4) : False := by
  obtain ⟨s₀, rfl⟩ := hs
  obtain ⟨u₀, rfl⟩ := hu
  apply zmod_four_second_stage (s₀ : ZMod 4) (u₀ : ZMod 4)
  have hmod := congrArg (fun n : ℕ => (n : ZMod 4)) heq
  push_cast at hmod
  rw [zmod_four_two_pow_sq_eq_zero ha,
    zmod_four_two_pow_fourth_eq_zero (by omega : 0 < a + 1)] at hmod
  norm_num at hmod
  exact hmod

private theorem zmod_four_corrected_first :
    ∀ u v : ZMod 4,
      3 * 7 ^ 4 * (2 * u + 1) ^ 2 * (2 * v + 1) ^ 2 ≠
        (2 * u + 1) ^ 4 + 16 * 7 ^ 7 * (2 * v + 1) ^ 4 := by
  decide

private theorem corrected_first_split_impossible {T s u v : ℕ}
    (hT : Even T) (hu : Odd u) (hv : Odd v)
    (heq : T ^ 2 * s ^ 2 + 3 * 7 ^ 4 * u ^ 2 * v ^ 2 =
      u ^ 4 + 16 * 7 ^ 7 * v ^ 4) : False := by
  obtain ⟨T₀, rfl⟩ := hT
  obtain ⟨u₀, rfl⟩ := hu
  obtain ⟨v₀, rfl⟩ := hv
  apply zmod_four_corrected_first (u₀ : ZMod 4) (v₀ : ZMod 4)
  have hmod := congrArg (fun n : ℕ => (n : ZMod 4)) heq
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hmod ⊢
  have hzero : ((T₀ : ZMod 4) + T₀) ^ 2 * (s : ZMod 4) ^ 2 = 0 := by
    calc
      ((T₀ : ZMod 4) + T₀) ^ 2 * (s : ZMod 4) ^ 2 =
          4 * (T₀ ^ 2 * s ^ 2) := by ring
      _ = 0 := by rw [show (4 : ZMod 4) = 0 by decide, zero_mul]
  rw [hzero, zero_add] at hmod
  exact hmod

private theorem zmod_sixteen_final :
    ∀ m n : ZMod 16,
      (2 * m + 1) ^ 4 + 7 ^ 7 * (2 * n + 1) ^ 4 ≠ 0 := by
  decide

private theorem final_sum_impossible {T s m n : ℕ} (hT : Even T)
    (hm : Odd m) (hn : Odd n)
    (heq : 16 * T * s = m ^ 4 + 7 ^ 7 * n ^ 4) : False := by
  obtain ⟨T₀, rfl⟩ := hT
  obtain ⟨m₀, rfl⟩ := hm
  obtain ⟨n₀, rfl⟩ := hn
  apply zmod_sixteen_final (m₀ : ZMod 16) (n₀ : ZMod 16)
  have hmod := congrArg (fun n : ℕ => (n : ZMod 16)) heq
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hmod ⊢
  have hzero : 16 * ((T₀ : ZMod 16) + T₀) * (s : ZMod 16) = 0 := by
    rw [show (16 : ZMod 16) = 0 by decide, zero_mul, zero_mul]
  rw [hzero] at hmod
  exact hmod.symm

/-- The second allocation in Lebesgue's Addition.  Its last
difference-of-squares split gives `16 T s = m⁴ + 7⁷ n⁴`, which is impossible
modulo `16`. -/
private theorem corrected_second_split_impossible {a s u v : ℕ} (ha : 0 < a)
    (hv : Odd v) (hsu : s.Coprime u) (huv : u.Coprime v)
    (heq : (2 ^ a) ^ 2 * s ^ 2 + 3 * 7 ^ 4 * u ^ 2 * v ^ 2 =
      7 ^ 7 * v ^ 4 + 16 * u ^ 4) : False := by
  let T := 2 ^ a
  let A := 8 * T * s
  let H : ℤ := 32 * (u : ℤ) ^ 2 - 3 * 7 ^ 4 * (v : ℤ) ^ 2
  have heqInt :
      (T : ℤ) ^ 2 * (s : ℤ) ^ 2 + 3 * 7 ^ 4 * (u : ℤ) ^ 2 * (v : ℤ) ^ 2 =
        7 ^ 7 * (v : ℤ) ^ 4 + 16 * (u : ℤ) ^ 4 := by
    exact_mod_cast heq
  have hsqInt : (A : ℤ) ^ 2 = H ^ 2 + 7 ^ 7 * (v : ℤ) ^ 4 := by
    simp only [A, H]
    push_cast
    nlinarith [heqInt]
  let h := H.natAbs
  have hhSq : (h : ℤ) ^ 2 = H ^ 2 := by
    rw [show (h : ℤ) = |H| by exact Int.natCast_natAbs H, sq_abs]
  have hsqNat : A ^ 2 = h ^ 2 + 7 ^ 7 * v ^ 4 := by
    have hsqCast : (A : ℤ) ^ 2 = (h : ℤ) ^ 2 + 7 ^ 7 * (v : ℤ) ^ 4 := by
      rw [hsqInt, hhSq]
    exact_mod_cast hsqCast
  have hresPos : 0 < 7 ^ 7 * v ^ 4 := by
    have hvpos : 0 < v := hv.pos
    positivity
  have hh_lt_A : h < A := by nlinarith
  have hTEven : Even T := by
    simp only [T]
    exact even_two.pow_of_ne_zero ha.ne'
  have hAEven : Even A := by
    rw [show A = 8 * (T * s) by simp only [A]; ring]
    exact (by norm_num : Even (8 : ℕ)).mul_right _
  have hHOdd : Odd H := by
    apply ((by norm_num : Even (32 : ℤ)).mul_right _).sub_odd
    exact ((by norm_num : Odd (3 : ℤ)).mul
      ((by norm_num : Odd (7 : ℤ)).pow)).mul (hv.natCast.pow)
  have hhOdd : Odd h := hHOdd.natAbs
  let f := A + h
  let g := A - h
  have hfOdd : Odd f := hAEven.add_odd hhOdd
  have hgOdd : Odd g := Nat.Even.sub_odd hh_lt_A.le hAEven hhOdd
  have hsum : f + g = 2 * A := by
    simp only [f, g]
    omega
  have hprod : f * g = 7 ^ 7 * v ^ 4 := by
    let d := A - h
    have hA : A = d + h := by
      simp only [d]
      omega
    have hsqD : (d + h) ^ 2 = h ^ 2 + 7 ^ 7 * v ^ 4 := by
      rw [← hA]
      exact hsqNat
    simp only [f, g]
    rw [show A + h = (A - h) + 2 * h by omega]
    nlinarith
  have hcop : f.Coprime g := by
    by_contra hn
    obtain ⟨l, hl, hlf, hlg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hlTwoA : l ∣ 2 * A := by rw [← hsum]; exact dvd_add hlf hlg
    have hlneTwo : l ≠ 2 := by
      intro hleq
      have h2f : 2 ∣ f := by simpa only [hleq] using hlf
      exact (Nat.not_even_iff_odd.mpr hfOdd) (even_iff_two_dvd.mpr h2f)
    have hlA : l ∣ A := by
      rcases hl.dvd_mul.mp hlTwoA with hlTwo | hlA
      · exact (hlneTwo ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo)).elim
      · exact hlA
    have hlh : l ∣ h := by
      apply (Nat.dvd_add_iff_right hlA).mpr
      simpa only [f] using hlf
    have hlAparts : l ∣ 8 * (T * s) := by
      simpa only [A, mul_assoc] using hlA
    have hls : l ∣ s := by
      rcases hl.dvd_mul.mp hlAparts with hlEight | hlTs
      · have hlEight' : l ∣ 2 ^ 3 := by norm_num at hlEight ⊢; exact hlEight
        have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlEight'
        exact (hlneTwo ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo)).elim
      · rcases hl.dvd_mul.mp hlTs with hlT | hls
        · simp only [T] at hlT
          have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlT
          exact (hlneTwo ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo)).elim
        · exact hls
    have hlwhole : l ∣ 7 ^ 7 * v ^ 4 := by rw [← hprod]; exact hlf.trans (dvd_mul_right f g)
    rcases hl.dvd_mul.mp hlwhole with hlSevenPow | hlvPow
    · have hlSeven : l ∣ 7 := hl.dvd_of_dvd_pow hlSevenPow
      have hleq : l = 7 :=
        (Nat.prime_dvd_prime_iff_eq hl Nat.prime_seven).mp hlSeven
      have hlHInt : (l : ℤ) ∣ H := by
        apply Int.dvd_natAbs.mp
        exact Int.natCast_dvd_natCast.mpr hlh
      have hluTermInt : (l : ℤ) ∣ 32 * (u : ℤ) ^ 2 := by
        have hvTerm : (l : ℤ) ∣ 3 * 7 ^ 4 * (v : ℤ) ^ 2 := by
          rw [hleq]
          exact ⟨3 * 7 ^ 3 * (v : ℤ) ^ 2, by ring⟩
        have := dvd_add hlHInt hvTerm
        simpa only [H, sub_add_cancel] using this
      have hluTerm : l ∣ 32 * u ^ 2 := by exact_mod_cast hluTermInt
      rcases hl.dvd_mul.mp hluTerm with hlThirtyTwo | hluPow
      · have hlThirtyTwo' : l ∣ 2 ^ 5 := by
          norm_num at hlThirtyTwo ⊢
          exact hlThirtyTwo
        have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlThirtyTwo'
        exact (hlneTwo ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo)).elim
      · have hlu : l ∣ u := hl.dvd_of_dvd_pow hluPow
        exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hls, hlu⟩) hsu
    · have hlv : l ∣ v := hl.dvd_of_dvd_pow hlvPow
      have hlHInt : (l : ℤ) ∣ H := by
        apply Int.dvd_natAbs.mp
        exact Int.natCast_dvd_natCast.mpr hlh
      have hvTermInt : (l : ℤ) ∣ 3 * 7 ^ 4 * (v : ℤ) ^ 2 := by
        exact dvd_mul_of_dvd_right (dvd_pow (Int.natCast_dvd_natCast.mpr hlv)
          (by norm_num)) _
      have hluTermInt : (l : ℤ) ∣ 32 * (u : ℤ) ^ 2 := by
        have := dvd_add hlHInt hvTermInt
        simpa only [H, sub_add_cancel] using this
      have hluTerm : l ∣ 32 * u ^ 2 := by exact_mod_cast hluTermInt
      rcases hl.dvd_mul.mp hluTerm with hlThirtyTwo | hluPow
      · have hlThirtyTwo' : l ∣ 2 ^ 5 := by
          norm_num at hlThirtyTwo ⊢
          exact hlThirtyTwo
        have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlThirtyTwo'
        exact (hlneTwo ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo)).elim
      · have hlu : l ∣ u := hl.dvd_of_dvd_pow hluPow
        exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hlu, hlv⟩) huv
  obtain ⟨m, n, hvMn, hmn, hall⟩ := seven_allocations hcop hprod
  have hmOdd : Odd m := by
    rw [hvMn] at hv
    exact Nat.Odd.of_mul_left hv
  have hnOdd : Odd n := by
    rw [hvMn] at hv
    exact Nat.Odd.of_mul_right hv
  rcases hall with h₁ | h₂
  · apply final_sum_impossible hTEven hmOdd hnOdd
    calc
      16 * T * s = 2 * A := by simp only [A]; ring
      _ = f + g := hsum.symm
      _ = m ^ 4 + 7 ^ 7 * n ^ 4 := by rw [h₁.1, h₁.2]
  · apply final_sum_impossible hTEven hnOdd hmOdd
    calc
      16 * T * s = 2 * A := by simp only [A]; ring
      _ = f + g := hsum.symm
      _ = n ^ 4 + 7 ^ 7 * m ^ 4 := by rw [h₂.1, h₂.2]; ring

/-- Lebesgue's published repair of the third of the four initial
allocations. -/
private theorem corrected_third_allocation_impossible {a q s t : ℕ}
    (ha : 0 < a) (hq : Odd q) (ht : Odd t)
    (hqs : q.Coprime s) (hst : s.Coprime t)
    (hthird :
      (q : ℤ) ^ 2 - 2 * (2 ^ a : ℤ) ^ 2 * 3 * 7 ^ 4 * (s * t : ℕ) ^ 2 =
        (2 ^ a : ℤ) ^ 4 * (s : ℤ) ^ 4 - 7 ^ 7 * (t : ℤ) ^ 4) : False := by
  let T := 2 ^ a
  have hthird' :
      (q : ℤ) ^ 2 - 2 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (s * t : ℕ) ^ 2 =
        (T : ℤ) ^ 4 * (s : ℤ) ^ 4 - 7 ^ 7 * (t : ℤ) ^ 4 := by
    simpa only [T, Nat.cast_pow, Nat.cast_ofNat] using hthird
  have hqeqInt :
      (q : ℤ) ^ 2 + 7 ^ 7 * (t : ℤ) ^ 4 =
        (T : ℤ) ^ 4 * (s : ℤ) ^ 4 +
          2 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (s : ℤ) ^ 2 * (t : ℤ) ^ 2 := by
    push_cast at hthird'
    nlinarith
  have hqeq :
      q ^ 2 + 7 ^ 7 * t ^ 4 =
        T ^ 4 * s ^ 4 + 2 * T ^ 2 * 3 * 7 ^ 4 * s ^ 2 * t ^ 2 := by
    exact_mod_cast hqeqInt
  let W := T ^ 2 * s ^ 2 + 3 * 7 ^ 4 * t ^ 2
  have hWsq : W ^ 2 = q ^ 2 + 64 * 7 ^ 7 * t ^ 4 := by
    calc
      W ^ 2 = (q ^ 2 + 7 ^ 7 * t ^ 4) + 63 * 7 ^ 7 * t ^ 4 := by
        simp only [W]
        rw [hqeq]
        ring
      _ = q ^ 2 + 64 * 7 ^ 7 * t ^ 4 := by ring
  have htpos : 0 < t := ht.pos
  have hresPos : 0 < 64 * 7 ^ 7 * t ^ 4 := by positivity
  have hq_lt_W : q < W := by nlinarith
  have hTEven : Even T := by
    simp only [T]
    exact even_two.pow_of_ne_zero ha.ne'
  have hFirstEven : Even (T ^ 2 * s ^ 2) :=
    (hTEven.pow_of_ne_zero (by norm_num)).mul_right _
  have hSecondOdd : Odd (3 * 7 ^ 4 * t ^ 2) :=
    ((by norm_num : Odd (3 : ℕ)).mul ((by norm_num : Odd (7 : ℕ)).pow)).mul ht.pow
  have hWOdd : Odd W := hFirstEven.add_odd hSecondOdd
  obtain ⟨f, hf⟩ := (hWOdd.add_odd hq).two_dvd
  obtain ⟨g, hg⟩ := (Nat.Odd.sub_odd hWOdd hq).two_dvd
  have hsum : f + g = W := by omega
  have hdiff : f = g + q := by omega
  have hprod : f * g = 16 * 7 ^ 7 * t ^ 4 := by nlinarith
  have hcop : f.Coprime g := by
    by_contra hn
    obtain ⟨l, hl, hlf, hlg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hlW : l ∣ W := by rw [← hsum]; exact dvd_add hlf hlg
    have hlq : l ∣ q := by
      rw [hdiff] at hlf
      exact (Nat.dvd_add_iff_right hlg).mpr hlf
    have hlwhole : l ∣ 16 * (7 ^ 7 * t ^ 4) := by
      have : l ∣ 16 * 7 ^ 7 * t ^ 4 := by
        rw [← hprod]
        exact hlf.trans (dvd_mul_right f g)
      simpa only [mul_assoc] using this
    rcases hl.dvd_mul.mp hlwhole with hlSixteen | hlrest
    · have hlSixteen' : l ∣ 2 ^ 4 := by norm_num at hlSixteen ⊢; exact hlSixteen
      have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlSixteen'
      have hleq : l = 2 :=
        (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo
      have h2W : 2 ∣ W := by simpa only [hleq] using hlW
      exact (Nat.not_even_iff_odd.mpr hWOdd) (even_iff_two_dvd.mpr h2W)
    · rcases hl.dvd_mul.mp hlrest with hlSevenPow | hltPow
      · have hlSeven : l ∣ 7 := hl.dvd_of_dvd_pow hlSevenPow
        have hleq : l = 7 :=
          (Nat.prime_dvd_prime_iff_eq hl Nat.prime_seven).mp hlSeven
        have hlSecond : l ∣ 3 * 7 ^ 4 * t ^ 2 := by
          rw [hleq]
          exact ⟨3 * 7 ^ 3 * t ^ 2, by ring⟩
        have hlFirst : l ∣ T ^ 2 * s ^ 2 := by
          apply (Nat.dvd_add_iff_left hlSecond).mpr
          simpa only [W] using hlW
        rcases hl.dvd_mul.mp hlFirst with hlTPow | hlsPow
        · have hlT : l ∣ T := hl.dvd_of_dvd_pow hlTPow
          simp only [T] at hlT
          have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlT
          have : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo
          omega
        · have hls : l ∣ s := hl.dvd_of_dvd_pow hlsPow
          exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hlq, hls⟩) hqs
      · have hlt : l ∣ t := hl.dvd_of_dvd_pow hltPow
        have hlSecond : l ∣ 3 * 7 ^ 4 * t ^ 2 :=
          dvd_mul_of_dvd_right (dvd_pow hlt (by norm_num)) _
        have hlFirst : l ∣ T ^ 2 * s ^ 2 := by
          apply (Nat.dvd_add_iff_left hlSecond).mpr
          simpa only [W] using hlW
        rcases hl.dvd_mul.mp hlFirst with hlTPow | hlsPow
        · have hlT : l ∣ T := hl.dvd_of_dvd_pow hlTPow
          simp only [T] at hlT
          have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlT
          have hleq : l = 2 :=
            (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo
          have h2t : 2 ∣ t := by simpa only [hleq] using hlt
          exact (Nat.not_even_iff_odd.mpr ht) (even_iff_two_dvd.mpr h2t)
        · have hls : l ∣ s := hl.dvd_of_dvd_pow hlsPow
          exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hls, hlt⟩) hst
  obtain ⟨u, v, htuv, huv, hall⟩ := four_allocations (e := 1) hcop (by
    rw [hsum]
    exact hWOdd) (by simpa using hprod)
  have huOdd : Odd u := by
    rw [htuv] at ht
    exact Nat.Odd.of_mul_left ht
  have hvOdd : Odd v := by
    rw [htuv] at ht
    exact Nat.Odd.of_mul_right ht
  have hsuv : s.Coprime (u * v) := by simpa only [← htuv] using hst
  have hsu : s.Coprime u := (Nat.coprime_mul_iff_right.mp hsuv).1
  have hsv : s.Coprime v := (Nat.coprime_mul_iff_right.mp hsuv).2
  rcases hall with h₁ | h₂ | h₃ | h₄
  · apply corrected_first_split_impossible hTEven huOdd hvOdd
    calc
      T ^ 2 * s ^ 2 + 3 * 7 ^ 4 * u ^ 2 * v ^ 2 = W := by
        simp only [W]
        rw [htuv]
        ring
      _ = f + g := hsum.symm
      _ = u ^ 4 + 16 * 7 ^ 7 * v ^ 4 := by rw [h₁.1, h₁.2]; norm_num
  · apply corrected_second_split_impossible ha huOdd hsv huv.symm
    calc
      T ^ 2 * s ^ 2 + 3 * 7 ^ 4 * v ^ 2 * u ^ 2 = W := by
        simp only [W]
        rw [htuv]
        ring
      _ = f + g := hsum.symm
      _ = 7 ^ 7 * u ^ 4 + 16 * v ^ 4 := by rw [h₂.1, h₂.2]; norm_num
  · apply corrected_second_split_impossible ha hvOdd hsu huv
    calc
      T ^ 2 * s ^ 2 + 3 * 7 ^ 4 * u ^ 2 * v ^ 2 = W := by
        simp only [W]
        rw [htuv]
        ring
      _ = f + g := hsum.symm
      _ = 7 ^ 7 * v ^ 4 + 16 * u ^ 4 := by rw [h₃.1, h₃.2]; norm_num; ring
  · apply corrected_first_split_impossible hTEven hvOdd huOdd
    calc
      T ^ 2 * s ^ 2 + 3 * 7 ^ 4 * v ^ 2 * u ^ 2 = W := by
        simp only [W]
        rw [htuv]
        ring
      _ = f + g := hsum.symm
      _ = v ^ 4 + 16 * 7 ^ 7 * u ^ 4 := by rw [h₄.1, h₄.2]; norm_num; ring

/-- The first initial allocation is the one that continues the descent: its
second difference-of-squares split has exactly the same shape with `a`
replaced by `a - 1`. -/
private theorem first_allocation_descends {a q s t : ℕ} (ha : 0 < a)
    (hq : Odd q) (hs : Odd s) (ht : Odd t)
    (hqs : q.Coprime s) (hst : s.Coprime t)
    (hfirst :
      (q : ℤ) ^ 2 - 2 * (2 ^ a : ℤ) ^ 2 * 3 * 7 ^ 4 * (s * t : ℕ) ^ 2 =
        (s : ℤ) ^ 4 - (2 ^ a : ℤ) ^ 4 * 7 ^ 7 * (t : ℤ) ^ 4) :
    ∃ p' q' r' : ℕ,
      Odd p' ∧ Odd q' ∧ Odd r' ∧
      p'.Coprime q' ∧ p'.Coprime r' ∧ q'.Coprime r' ∧
      DescentEquation a p' q' r' := by
  let T := 2 ^ a
  have hfirst' :
      (q : ℤ) ^ 2 - 2 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (s * t : ℕ) ^ 2 =
        (s : ℤ) ^ 4 - (T : ℤ) ^ 4 * 7 ^ 7 * (t : ℤ) ^ 4 := by
    simpa only [T, Nat.cast_pow, Nat.cast_ofNat] using hfirst
  have hqeqInt :
      (q : ℤ) ^ 2 + (T : ℤ) ^ 4 * 7 ^ 7 * (t : ℤ) ^ 4 =
        (s : ℤ) ^ 4 +
          2 * (T : ℤ) ^ 2 * 3 * 7 ^ 4 * (s : ℤ) ^ 2 * (t : ℤ) ^ 2 := by
    push_cast at hfirst'
    nlinarith
  have hqeq :
      q ^ 2 + T ^ 4 * 7 ^ 7 * t ^ 4 =
        s ^ 4 + 2 * T ^ 2 * 3 * 7 ^ 4 * s ^ 2 * t ^ 2 := by
    exact_mod_cast hqeqInt
  let W := s ^ 2 + T ^ 2 * 3 * 7 ^ 4 * t ^ 2
  have hWsq : W ^ 2 = q ^ 2 + 64 * T ^ 4 * 7 ^ 7 * t ^ 4 := by
    calc
      W ^ 2 = (q ^ 2 + T ^ 4 * 7 ^ 7 * t ^ 4) +
          63 * T ^ 4 * 7 ^ 7 * t ^ 4 := by
        simp only [W]
        rw [hqeq]
        ring
      _ = q ^ 2 + 64 * T ^ 4 * 7 ^ 7 * t ^ 4 := by ring
  have htpos : 0 < t := ht.pos
  have hTpos : 0 < T := by simp only [T]; positivity
  have hresPos : 0 < 64 * T ^ 4 * 7 ^ 7 * t ^ 4 := by positivity
  have hq_lt_W : q < W := by nlinarith
  have hTEven : Even T := by
    simp only [T]
    exact even_two.pow_of_ne_zero ha.ne'
  have hSecondEven : Even (T ^ 2 * 3 * 7 ^ 4 * t ^ 2) := by
    rw [show T ^ 2 * 3 * 7 ^ 4 * t ^ 2 = T ^ 2 * (3 * 7 ^ 4 * t ^ 2) by ring]
    exact (hTEven.pow_of_ne_zero (by norm_num : 2 ≠ 0)).mul_right _
  have hWOdd : Odd W := hs.pow.add_even hSecondEven
  obtain ⟨f, hf⟩ := (hWOdd.add_odd hq).two_dvd
  obtain ⟨g, hg⟩ := (Nat.Odd.sub_odd hWOdd hq).two_dvd
  have hsum : f + g = W := by omega
  have hdiff : f = g + q := by omega
  have hprodRaw : f * g = 16 * T ^ 4 * 7 ^ 7 * t ^ 4 := by nlinarith
  have hpow : (2 ^ (a + 1)) ^ 4 = 16 * T ^ 4 := by
    simp only [T, pow_add, pow_one, mul_pow]
    ring
  have hprod : f * g = (2 ^ (a + 1)) ^ 4 * 7 ^ 7 * t ^ 4 := by
    rw [hpow]
    exact hprodRaw
  have hcop : f.Coprime g := by
    by_contra hn
    obtain ⟨l, hl, hlf, hlg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hlW : l ∣ W := by rw [← hsum]; exact dvd_add hlf hlg
    have hlq : l ∣ q := by
      rw [hdiff] at hlf
      exact (Nat.dvd_add_iff_right hlg).mpr hlf
    have hlwhole : l ∣ (2 ^ (a + 1)) ^ 4 * (7 ^ 7 * t ^ 4) := by
      have : l ∣ (2 ^ (a + 1)) ^ 4 * 7 ^ 7 * t ^ 4 := by
        rw [← hprod]
        exact hlf.trans (dvd_mul_right f g)
      simpa only [mul_assoc] using this
    rcases hl.dvd_mul.mp hlwhole with hlTwoPow | hlrest
    · have hlTwoSucc : l ∣ 2 ^ (a + 1) := hl.dvd_of_dvd_pow hlTwoPow
      have hlTwo : l ∣ 2 := hl.dvd_of_dvd_pow hlTwoSucc
      have hleq : l = 2 :=
        (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hlTwo
      have h2W : 2 ∣ W := by simpa only [hleq] using hlW
      exact (Nat.not_even_iff_odd.mpr hWOdd) (even_iff_two_dvd.mpr h2W)
    · rcases hl.dvd_mul.mp hlrest with hlSevenPow | hltPow
      · have hlSeven : l ∣ 7 := hl.dvd_of_dvd_pow hlSevenPow
        have hleq : l = 7 :=
          (Nat.prime_dvd_prime_iff_eq hl Nat.prime_seven).mp hlSeven
        have hlSecond : l ∣ T ^ 2 * 3 * 7 ^ 4 * t ^ 2 := by
          rw [hleq]
          exact ⟨T ^ 2 * 3 * 7 ^ 3 * t ^ 2, by ring⟩
        have hlsPow : l ∣ s ^ 2 := by
          apply (Nat.dvd_add_iff_left hlSecond).mpr
          simpa only [W] using hlW
        have hls : l ∣ s := hl.dvd_of_dvd_pow hlsPow
        exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hlq, hls⟩) hqs
      · have hlt : l ∣ t := hl.dvd_of_dvd_pow hltPow
        have hlSecond : l ∣ T ^ 2 * 3 * 7 ^ 4 * t ^ 2 :=
          dvd_mul_of_dvd_right (dvd_pow hlt (by norm_num)) _
        have hlsPow : l ∣ s ^ 2 := by
          apply (Nat.dvd_add_iff_left hlSecond).mpr
          simpa only [W] using hlW
        have hls : l ∣ s := hl.dvd_of_dvd_pow hlsPow
        exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l, hl, hlq, hls⟩) hqs
  obtain ⟨u, v, htuv, huv, hall⟩ := four_allocations (e := a + 1) hcop (by
    rw [hsum]
    exact hWOdd) hprod
  have huOdd : Odd u := by
    rw [htuv] at ht
    exact Nat.Odd.of_mul_left ht
  have hvOdd : Odd v := by
    rw [htuv] at ht
    exact Nat.Odd.of_mul_right ht
  have hsuv : s.Coprime (u * v) := by simpa only [← htuv] using hst
  have hsu : s.Coprime u := (Nat.coprime_mul_iff_right.mp hsuv).1
  have hsv : s.Coprime v := (Nat.coprime_mul_iff_right.mp hsuv).2
  have toDescent {x y : ℕ}
      (heq : s ^ 2 + T ^ 2 * 3 * 7 ^ 4 * x ^ 2 * y ^ 2 =
        x ^ 4 + (2 ^ (a + 1)) ^ 4 * 7 ^ 7 * y ^ 4) :
      DescentEquation a s x y := by
    rw [DescentEquation]
    have htwo : 2 ^ (2 * a) = T ^ 2 := by
      simp only [T]
      rw [show 2 * a = a * 2 by omega, pow_mul]
    have hfour : 2 ^ (4 * a + 4) = (2 ^ (a + 1)) ^ 4 := by
      rw [show 4 * a + 4 = (a + 1) * 4 by omega, pow_mul]
    rw [htwo, hfour]
    exact heq
  rcases hall with h₁ | h₂ | h₃ | h₄
  · refine ⟨s, u, v, hs, huOdd, hvOdd, hsu, hsv, huv, toDescent ?_⟩
    calc
      s ^ 2 + T ^ 2 * 3 * 7 ^ 4 * u ^ 2 * v ^ 2 = W := by
        simp only [W]
        rw [htuv]
        ring
      _ = f + g := hsum.symm
      _ = u ^ 4 + (2 ^ (a + 1)) ^ 4 * 7 ^ 7 * v ^ 4 := by rw [h₁.1, h₁.2]
  · exact (second_stage_allocation_impossible ha hs huOdd (by
      calc
        s ^ 2 + T ^ 2 * 3 * 7 ^ 4 * u ^ 2 * v ^ 2 = W := by
          simp only [W]
          rw [htuv]
          ring
        _ = f + g := hsum.symm
        _ = 7 ^ 7 * u ^ 4 + (2 ^ (a + 1)) ^ 4 * v ^ 4 := by
          rw [h₂.1, h₂.2])).elim
  · exact (second_stage_allocation_impossible ha hs hvOdd (by
      calc
        s ^ 2 + T ^ 2 * 3 * 7 ^ 4 * v ^ 2 * u ^ 2 = W := by
          simp only [W]
          rw [htuv]
          ring
        _ = f + g := hsum.symm
        _ = 7 ^ 7 * v ^ 4 + (2 ^ (a + 1)) ^ 4 * u ^ 4 := by
          rw [h₃.1, h₃.2]
          ring)).elim
  · refine ⟨s, v, u, hs, hvOdd, huOdd, hsv, hsu, huv.symm, toDescent ?_⟩
    calc
      s ^ 2 + T ^ 2 * 3 * 7 ^ 4 * v ^ 2 * u ^ 2 = W := by
        simp only [W]
        rw [htuv]
        ring
      _ = f + g := hsum.symm
      _ = v ^ 4 + (2 ^ (a + 1)) ^ 4 * 7 ^ 7 * u ^ 4 := by
        rw [h₄.1, h₄.2]
        ring

/-- One step of Lebesgue's corrected descent.  The third allocation is
disposed of by the argument from the published Addition; the first allocation
produces the new solution. -/
private theorem descend {a p q r : ℕ} (ha : 0 < a)
    (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r)
    (heq : DescentEquation (a + 1) p q r) :
    ∃ p' q' r' : ℕ,
      Odd p' ∧ Odd q' ∧ Odd r' ∧
      p'.Coprime q' ∧ p'.Coprime r' ∧ q'.Coprime r' ∧
      DescentEquation a p' q' r' := by
  obtain ⟨s, t, hrst, hst, hall⟩ :=
    first_signed_allocations hp hq hr hpq hpr heq
  have hs : Odd s := by
    rw [hrst] at hr
    exact Nat.Odd.of_mul_left hr
  have ht : Odd t := by
    rw [hrst] at hr
    exact Nat.Odd.of_mul_right hr
  have hqst : q.Coprime (s * t) := by simpa only [← hrst] using hqr
  have hqs : q.Coprime s := (Nat.coprime_mul_iff_right.mp hqst).1
  rcases hall with h₁ | h₂ | h₃ | h₄
  · exact first_allocation_descends ha hq hs ht hqs hst (by
      simpa only [hrst] using h₁)
  · exact (initial_second_allocation_impossible (t := t) ha hq hs (by
      simpa only [hrst] using h₂)).elim
  · exact (corrected_third_allocation_impossible ha hq ht hqs hst (by
      simpa only [hrst] using h₃)).elim
  · exact (initial_fourth_allocation_impossible (s := s) ha hq ht (by
      simpa only [hrst] using h₄)).elim

/-- Lebesgue's Théorème I, in contradiction form: the quartic family has no
solution with positive index and odd pairwise-coprime entries.  The proof is
the repaired infinite descent, terminating at the modulo-eight base case. -/
theorem descentEquation_impossible {a p q r : ℕ}
    (ha : 0 < a) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r)
    (heq : DescentEquation a p q r) : False := by
  induction a using Nat.strong_induction_on generalizing p q r with
  | h a ih =>
      rcases a with _ | a
      · omega
      · by_cases haZero : a = 0
        · subst a
          exact base_case_impossible hp hq hr (by simpa using heq)
        · have haPos : 0 < a := Nat.pos_of_ne_zero haZero
          obtain ⟨p', q', r', hp', hq', hr', hpq', hpr', hqr', heq'⟩ :=
            descend haPos hp hq hr hpq hpr hqr (by simpa only [Nat.succ_eq_add_one] using heq)
          exact ih a (Nat.lt_succ_self a) haPos hp' hq' hr' hpq' hpr' hqr' heq'

/-- The traditional conclusion of Théorème I.  Under the oddness assumptions
the stronger contradiction theorem applies, hence in particular `r = 0`. -/
theorem theoremI_r_eq_zero {a p q r : ℕ}
    (ha : 0 < a) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r)
    (heq : DescentEquation a p q r) : r = 0 := by
  exact (descentEquation_impossible ha hp hq hr hpq hpr hqr heq).elim

/-- Alternate name for the contradiction form of Théorème I. -/
theorem theoremI_impossible {a p q r : ℕ}
    (ha : 0 < a) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r)
    (heq : DescentEquation a p q r) : False :=
  descentEquation_impossible ha hp hq hr hpq hpr hqr heq

end Fermat.Seven.Lebesgue
