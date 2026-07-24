import Fermat.Irregular.BernoulliData

/-!
# Finite-field ingredients for the Voronoi--Kummer congruence

This file gives a sound port of the Voronoi route used in Manuel Eberl's
Isabelle AFP formalization of Kummer's congruence.  It proves both independent
inputs to Voronoi's congruence: the first-order reindexing of a power sum
modulo the square of a prime power, and the matching Faulhaber remainder
bound.  Their composition is `voronoi_primePower_hasPadicValAtLeast`.

The last section records the finite-field transport used after Voronoi:
powers of nonzero residues, and weighted sums of such powers, depend only on
the exponent modulo `p - 1`.
-/

namespace Fermat.Irregular.Voronoi

open Finset

/-! ## The exact Faulhaber remainder -/

/-- One summand in the part of Faulhaber's formula below `B_k * n`. -/
noncomputable def faulhaberSummand (k n i : ℕ) : ℚ :=
  bernoulli i * ((k + 1).choose i : ℚ) *
    (n : ℚ) ^ (k + 1 - i) / ((k + 1 : ℕ) : ℚ)

/-- The part of Faulhaber's formula strictly below the `B_k * n` term. -/
noncomputable def faulhaberRemainder (k n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k, faulhaberSummand k n i

/-- Exact Faulhaber decomposition isolating the linear Bernoulli term. -/
theorem sum_Ico_pow_eq_faulhaberRemainder_add {k n : ℕ} (hk : 0 < k) :
    (∑ m ∈ Finset.Ico 1 n, (m : ℚ) ^ k) =
      faulhaberRemainder k n + (n : ℚ) * bernoulli k := by
  have hfilter :
      (∑ m ∈ Finset.Ico 1 n, (m : ℚ) ^ k) =
        ∑ m ∈ Finset.range n, (m : ℚ) ^ k := by
    cases n <;> simp [Finset.sum_range_eq_add_Ico, hk.ne']
  rw [hfilter, sum_range_pow, Finset.sum_range_succ,
    Nat.choose_succ_self_right, show k + 1 - k = 1 by omega]
  simp only [faulhaberRemainder, faulhaberSummand, pow_one]
  push_cast
  field_simp

/-! ## Uniform denominator bound for Bernoulli numbers -/

/-- A zero-aware lower bound for the rational `p`-adic valuation. -/
def HasPadicValAtLeast (p : ℕ) (e : ℤ) (x : ℚ) : Prop :=
  x = 0 ∨ e ≤ padicValRat p x

namespace HasPadicValAtLeast

variable {p : ℕ} {e : ℤ} {x y : ℚ}

theorem zero : HasPadicValAtLeast p e 0 := Or.inl rfl

theorem mono {e' : ℤ} (hee' : e' ≤ e)
    (hx : HasPadicValAtLeast p e x) : HasPadicValAtLeast p e' x := by
  rcases hx with rfl | hx
  · exact zero
  · exact Or.inr (hee'.trans hx)

theorem neg (hx : HasPadicValAtLeast p e x) :
    HasPadicValAtLeast p e (-x) := by
  rcases hx with rfl | hx
  · exact zero
  · right
    simpa using hx

theorem add [Fact p.Prime]
    (hx : HasPadicValAtLeast p e x) (hy : HasPadicValAtLeast p e y) :
    HasPadicValAtLeast p e (x + y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · simpa [HasPadicValAtLeast] using Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · exact Or.inr <| (le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy)

theorem sub [Fact p.Prime]
    (hx : HasPadicValAtLeast p e x) (hy : HasPadicValAtLeast p e y) :
    HasPadicValAtLeast p e (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem mul [Fact p.Prime] {e' : ℤ} {y : ℚ}
    (hx : HasPadicValAtLeast p e x) (hy : HasPadicValAtLeast p e' y) :
    HasPadicValAtLeast p (e + e') (x * y) := by
  by_cases hx0 : x = 0
  · subst x
    simp [zero]
  by_cases hy0 : y = 0
  · subst y
    simp [zero]
  have hx := hx.resolve_left hx0
  have hy := hy.resolve_left hy0
  right
  rw [padicValRat.mul hx0 hy0]
  omega

theorem sum [Fact p.Prime] {s : Finset α} {f : α → ℚ}
    (hf : ∀ a ∈ s, HasPadicValAtLeast p e (f a)) :
    HasPadicValAtLeast p e (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add (hf a (by simp)) (ih fun b hb ↦ hf b (by simp [hb]))

theorem intCast (z : ℤ) : HasPadicValAtLeast p 0 (z : ℚ) := by
  by_cases hz : z = 0
  · subst z
    exact zero
  · right
    rw [padicValRat.of_int]
    simp

theorem primePow [Fact p.Prime] (t : ℕ) :
    HasPadicValAtLeast p (t : ℤ) ((p : ℚ) ^ t) := by
  right
  rw [padicValRat.pow (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    padicValRat.self (Fact.out : p.Prime).one_lt]
  simp

/-- Cancel a nonzero prime power from a valuation lower bound. -/
theorem of_primePow_mul [Fact p.Prime] {e : ℤ} {t : ℕ} {x : ℚ}
    (hx : HasPadicValAtLeast p (e + t) ((p : ℚ) ^ t * x)) :
    HasPadicValAtLeast p e x := by
  by_cases hzero : x = 0
  · exact Or.inl hzero
  right
  rcases hx with hx | hx
  · exact (hzero ((mul_eq_zero.mp hx).resolve_left
      (pow_ne_zero t (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)))).elim
  · rw [padicValRat.mul
      (pow_ne_zero t (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hzero,
      padicValRat.pow (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
      padicValRat.self (Fact.out : p.Prime).one_lt] at hx
    simpa using (show e ≤ padicValRat p x by omega)

/-- Cancel a nonzero natural factor whose `p`-adic valuation is bounded by
`s`.  This is the cancellation used after applying Voronoi at depth `s + 1`:
one factor of `p` remains after division by the index. -/
theorem of_nat_mul [Fact p.Prime] {e : ℤ} {s k : ℕ} {x : ℚ}
    (hk : k ≠ 0) (hks : padicValNat p k ≤ s)
    (hx : HasPadicValAtLeast p (e + (s : ℤ)) ((k : ℚ) * x)) :
    HasPadicValAtLeast p e x := by
  by_cases hzero : x = 0
  · exact Or.inl hzero
  right
  rcases hx with hx | hx
  · exact (hzero ((mul_eq_zero.mp hx).resolve_left
      (Nat.cast_ne_zero.mpr hk))).elim
  · rw [padicValRat.mul (Nat.cast_ne_zero.mpr hk) hzero,
      padicValRat.of_nat] at hx
    exact_mod_cast (show e ≤ padicValRat p x by
      have hks' : (padicValNat p k : ℤ) ≤ s := by exact_mod_cast hks
      omega)

theorem one_div_prime [Fact p.Prime] {q : ℕ} (hq : q.Prime) :
    HasPadicValAtLeast p (-1) ((1 : ℚ) / q) := by
  right
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  rw [padicValRat.div one_ne_zero hq0, padicValRat.one, padicValRat.of_nat]
  by_cases hpq : p = q
  · subst q
    simp
  · have hnot : ¬p ∣ q := by
      intro hdvd
      rcases (Nat.dvd_prime hq).mp hdvd with hp1 | hpq'
      · exact (Fact.out : p.Prime).ne_one hp1
      · exact hpq hpq'
    rw [padicValNat.eq_zero_of_not_dvd hnot]
    omega

end HasPadicValAtLeast

/-- Every Bernoulli number has rational `p`-adic valuation at least `-1`,
with zero treated as having infinite valuation.

This is the exact denominator estimate needed for the Faulhaber remainder.
It follows directly from the public von Staudt--Clausen theorem: each prime
reciprocal in its correction sum has valuation at least `-1`, while the
resulting integer has nonnegative valuation. -/
theorem bernoulli_hasPadicValAtLeast_neg_one (p k : ℕ) [Fact p.Prime] :
    HasPadicValAtLeast p (-1) (bernoulli k) := by
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨r, rfl⟩ := even_iff_two_dvd.mp heven
    let primes :=
      (Finset.range (2 * r + 2)).filter fun q ↦
        q.Prime ∧ (q - 1) ∣ 2 * r
    let correction : ℚ := ∑ q ∈ primes, (1 : ℚ) / q
    have hcorrection : HasPadicValAtLeast p (-1) correction := by
      apply HasPadicValAtLeast.sum
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      exact HasPadicValAtLeast.one_div_prime hq'.2.1
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen r
    have hz' : (z : ℚ) = bernoulli (2 * r) + correction := by
      simpa only [correction, primes, Finset.sum_filter] using hz
    have hint : HasPadicValAtLeast p (-1) (z : ℚ) :=
      (HasPadicValAtLeast.intCast z).mono (by omega)
    have hbernoulli : bernoulli (2 * r) = (z : ℚ) - correction := by
      linarith
    rw [hbernoulli]
    exact hint.sub hcorrection
  · by_cases hk : k = 1
    · subst k
      have hhalf : HasPadicValAtLeast p (-1) ((1 : ℚ) / 2) :=
        HasPadicValAtLeast.one_div_prime (by norm_num)
      rw [bernoulli_one]
      have heq : -((1 : ℚ) / 2) = -1 / 2 := by norm_num
      rw [← heq]
      exact hhalf.neg
    · have hkgt : 1 < k := by
        have hkpos := hodd.pos
        omega
      rw [bernoulli_eq_zero_of_odd hodd hkgt]
      exact HasPadicValAtLeast.zero

/-- At primes at least five, odd-index Bernoulli numbers are `p`-integral:
the only nonzero one is `B₁ = -1/2`. -/
theorem bernoulli_odd_hasPadicValAtLeast_zero {p k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hkodd : Odd k) :
    HasPadicValAtLeast p 0 (bernoulli k) := by
  by_cases hk : k = 1
  · subst k
    right
    have hnot : ¬p ∣ 2 := by
      intro hdvd
      have hple := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      omega
    have htwo : padicValRat p (2 : ℚ) = 0 := by
      rw [show (2 : ℚ) = (2 : ℕ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd hnot]
      simp
    rw [bernoulli_one, padicValRat.div (by norm_num) (by norm_num),
      padicValRat.neg, padicValRat.one, htwo]
    simp
  · have hkgt : 1 < k := by
      have hkpos := hkodd.pos
      omega
    rw [bernoulli_eq_zero_of_odd hkodd hkgt]
    exact HasPadicValAtLeast.zero

/-- For primes at least five, the valuation of an integer `d ≥ 3` is at
most `d - 3`.  This elementary estimate is the numerical input that lets the
power of a prime in a Faulhaber summand dominate all denominators. -/
theorem padicValNat_le_sub_three {p d : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hd3 : 3 ≤ d) :
    padicValNat p d ≤ d - 3 := by
  by_cases hd5 : d < 5
  · have hnot : ¬p ∣ d := by
      intro hdvd
      have hple := Nat.le_of_dvd (by omega : 0 < d) hdvd
      omega
    rw [padicValNat.eq_zero_of_not_dvd hnot]
    exact Nat.zero_le _
  · have haux : ∀ m : ℕ, m + 5 ≤ 5 ^ (m + 2) := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
          calc
            m + 1 + 5 ≤ 5 * (m + 5) := by omega
            _ ≤ 5 * 5 ^ (m + 2) := Nat.mul_le_mul_left 5 ih
            _ = 5 ^ (m + 1 + 2) := by
              rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]
              ring
    have hd_pow_five : d ≤ 5 ^ (d - 3) := by
      have h := haux (d - 5)
      calc
        d = d - 5 + 5 := (Nat.sub_add_cancel (by omega)).symm
        _ ≤ 5 ^ (d - 5 + 2) := h
        _ = 5 ^ (d - 3) := by
          congr 1
          omega
    have hd_pow_p : d ≤ p ^ (d - 3) :=
      hd_pow_five.trans (Nat.pow_le_pow_left hp5 (d - 3))
    rw [← Nat.factorization_def d (Fact.out : p.Prime)]
    exact Nat.factorization_le_of_le_pow hd_pow_p

/-- Normalize the binomial coefficient in a Faulhaber summand so that its
only explicit natural denominator is the power gap `k + 1 - i`. -/
theorem choose_succ_div_succ_eq_choose_div_gap {k i : ℕ} (hi : i ≤ k) :
    (((k + 1).choose i : ℚ) / ((k + 1 : ℕ) : ℚ)) =
      (k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ) := by
  have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hgap : ((k + 1 - i : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show 0 < k + 1 - i by omega).ne'
  rw [div_eq_div_iff hk1 hgap]
  exact_mod_cast (Nat.choose_mul_succ_eq k i).symm

/-- Each lower Faulhaber summand at `n = p^t` is divisible by `p^(2t)`
in the rational, zero-aware valuation sense. -/
theorem faulhaberSummand_primePower_hasPadicValAtLeast
    {p t k i : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (ht : 1 ≤ t) (hkeven : Even k) (hi : i < k) :
    HasPadicValAtLeast p (2 * (t : ℤ))
      (faulhaberSummand k (p ^ t) i) := by
  let d := k + 1 - i
  have hi_le : i ≤ k := hi.le
  have hd2 : 2 ≤ d := by
    dsimp only [d]
    omega
  have hrewrite :
      faulhaberSummand k (p ^ t) i =
        bernoulli i * (k.choose i : ℚ) *
          (((p : ℚ) ^ t) ^ d) / (d : ℚ) := by
    rw [faulhaberSummand]
    have hchoose := choose_succ_div_succ_eq_choose_div_gap hi_le
    rw [show ((p ^ t : ℕ) : ℚ) = (p : ℚ) ^ t by norm_cast]
    rw [show k + 1 - i = d by rfl]
    calc
      bernoulli i * ((k + 1).choose i : ℚ) * ((p : ℚ) ^ t) ^ d /
          ((k + 1 : ℕ) : ℚ) =
        bernoulli i * ((p : ℚ) ^ t) ^ d *
          (((k + 1).choose i : ℚ) / ((k + 1 : ℕ) : ℚ)) := by ring
      _ = bernoulli i * ((p : ℚ) ^ t) ^ d *
          ((k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ)) := by rw [hchoose]
      _ = _ := by simp only [d]; ring
  rw [hrewrite]
  by_cases hBi : bernoulli i = 0
  · simp [hBi, HasPadicValAtLeast]
  right
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpow0 : ((p : ℚ) ^ t) ^ d ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp0)
  have hchoose0 : (k.choose i : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hi_le)
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hBval :
      if d = 2 then (0 : ℤ) ≤ padicValRat p (bernoulli i)
      else (-1 : ℤ) ≤ padicValRat p (bernoulli i) := by
    split_ifs with hd
    · have hi_eq : i = k - 1 := by
        dsimp only [d] at hd
        omega
      have hi_odd : Odd i := by
        obtain ⟨r, hr⟩ := hkeven
        refine ⟨r - 1, ?_⟩
        omega
      rcases bernoulli_odd_hasPadicValAtLeast_zero hp5 hi_odd with hzero | hval
      · exact (hBi hzero).elim
      · exact hval
    · rcases bernoulli_hasPadicValAtLeast_neg_one p i with hzero | hval
      · exact (hBi hzero).elim
      · exact hval
  have hchooseVal : 0 ≤ padicValRat p (k.choose i : ℚ) := by
    rw [padicValRat.of_nat]
    simp
  have hpPowVal : padicValRat p (((p : ℚ) ^ t) ^ d) = (d : ℤ) * t := by
    rw [padicValRat.pow (pow_ne_zero _ hp0), padicValRat.pow hp0,
      padicValRat.self (Fact.out : p.Prime).one_lt]
    ring
  have hdVal :
      if d = 2 then padicValRat p (d : ℚ) = 0
      else padicValRat p (d : ℚ) ≤ ((d - 3 : ℕ) : ℤ) := by
    split_ifs with hd
    · have hnot : ¬p ∣ d := by
        intro hpd
        have hple := Nat.le_of_dvd (by omega : 0 < d) hpd
        omega
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnot]
      simp
    · rw [padicValRat.of_nat]
      exact_mod_cast padicValNat_le_sub_three hp5 (by omega : 3 ≤ d)
  rw [padicValRat.div (mul_ne_zero (mul_ne_zero hBi hchoose0) hpow0) hd0,
    padicValRat.mul (mul_ne_zero hBi hchoose0) hpow0,
    padicValRat.mul hBi hchoose0, hpPowVal]
  by_cases hd : d = 2
  · rw [if_pos hd] at hBval hdVal
    subst d
    nlinarith
  · rw [if_neg hd] at hBval hdVal
    have hd3 : 3 ≤ d := by omega
    have hcastSub : ((d - 3 : ℕ) : ℤ) = (d : ℤ) - 3 := by
      rw [Nat.cast_sub hd3]
      norm_num
    rw [hcastSub] at hdVal
    have hmul : (0 : ℤ) ≤ ((t : ℤ) - 1) * ((d : ℤ) - 2) := by
      apply mul_nonneg <;> omega
    nlinarith

/-- The complete Faulhaber remainder at `p^t` has valuation at least `2t`.
This is the square-modulus power-sum approximation needed by Voronoi. -/
theorem faulhaberRemainder_primePower_hasPadicValAtLeast
    {p t k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (ht : 1 ≤ t) (hkeven : Even k) :
    HasPadicValAtLeast p (2 * (t : ℤ))
      (faulhaberRemainder k (p ^ t)) := by
  rw [faulhaberRemainder]
  apply HasPadicValAtLeast.sum
  intro i hi
  exact faulhaberSummand_primePower_hasPadicValAtLeast hp5 ht hkeven
    (Finset.mem_range.mp hi)

/-- Power-sum approximation modulo the square of `p^t`, stated directly as
a rational valuation bound. -/
theorem powerSum_sub_bernoulli_primePower_hasPadicValAtLeast
    {p t k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (ht : 1 ≤ t) (hk : 0 < k) (hkeven : Even k) :
    HasPadicValAtLeast p (2 * (t : ℤ))
      ((∑ m ∈ Finset.Ico 1 (p ^ t), (m : ℚ) ^ k) -
        ((p ^ t : ℕ) : ℚ) * bernoulli k) := by
  rw [sum_Ico_pow_eq_faulhaberRemainder_add hk]
  convert faulhaberRemainder_primePower_hasPadicValAtLeast hp5 ht hkeven using 1
  ring

/-- Equality of two integer casts modulo `p^e` gives the corresponding
zero-aware rational valuation bound on their difference. -/
theorem intCast_sub_hasPadicValAtLeast_of_zmod_eq
    {p e : ℕ} [Fact p.Prime] {A B : ℤ}
    (h : (A : ZMod (p ^ e)) = (B : ZMod (p ^ e))) :
    HasPadicValAtLeast p (e : ℤ) ((A - B : ℤ) : ℚ) := by
  have hzero : ((A - B : ℤ) : ZMod (p ^ e)) = 0 := by
    push_cast
    exact sub_eq_zero.mpr h
  have hdvd : ((p : ℤ) ^ e) ∣ A - B := by
    have hdvd' := (ZMod.intCast_zmod_eq_zero_iff_dvd (A - B) (p ^ e)).mp hzero
    norm_cast at hdvd' ⊢
  rcases (padicValInt_dvd_iff e (A - B)).mp hdvd with hz | hval
  · left
    exact_mod_cast hz
  · right
    rw [padicValRat.of_int]
    exact_mod_cast hval

/-! ## First-order power expansion modulo a square -/

/-- The first-order binomial expansion modulo `n²`.

This is the Taylor step in Voronoi's argument: all terms containing two
copies of `n * q` disappear modulo `n²`.  The formulation in `ZMod` avoids
any choice of representatives and includes the harmless case `n = 0`. -/
theorem add_multiple_pow_zmod_sq (n : ℕ) (y q : ℤ) (k : ℕ) :
    ((y + (n : ℤ) * q : ℤ) : ZMod (n ^ 2)) ^ k =
      (y : ZMod (n ^ 2)) ^ k +
        (k : ZMod (n ^ 2)) * ((n : ℤ) * q : ℤ) *
          (y : ZMod (n ^ 2)) ^ (k - 1) := by
  let Y : ZMod (n ^ 2) := y
  let T : ZMod (n ^ 2) := ((n : ℤ) * q : ℤ)
  have hn_sq : (n : ZMod (n ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hT_sq : T ^ 2 = 0 := by
    calc
      T ^ 2 = (n : ZMod (n ^ 2)) ^ 2 * (q : ZMod (n ^ 2)) ^ 2 := by
        simp only [T]
        push_cast
        ring
      _ = 0 := by rw [hn_sq, zero_mul]
  have hmain :
      (Y + T) ^ k = Y ^ k + (k : ZMod (n ^ 2)) * T * Y ^ (k - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rcases k with _ | k
        · simp
        · conv_lhs => rw [pow_succ]
          rw [ih]
          simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
          have hTT : T * T = 0 := by simpa [pow_two] using hT_sq
          linear_combination (k + 1 : ZMod (n ^ 2)) * Y ^ k * hTT
  simpa [Y, T] using hmain

/-- Integer-congruence form of `add_multiple_pow_zmod_sq`. -/
theorem add_multiple_pow_int_modEq_sq (n : ℕ) (y q : ℤ) (k : ℕ) :
    (y + (n : ℤ) * q) ^ k ≡
      y ^ k + (k : ℤ) * ((n : ℤ) * q) * y ^ (k - 1) [ZMOD n ^ 2] := by
  rw [show (n : ℤ) ^ 2 = ((n ^ 2 : ℕ) : ℤ) by norm_cast]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  simpa using add_multiple_pow_zmod_sq n y q k

/-- Multiplication by the modulus lifts equality modulo `n` of two powers to
equality modulo `n²`. -/
theorem modulus_mul_pow_eq_of_int_modEq (n k : ℕ) {u v : ℤ}
    (huv : u ≡ v [ZMOD n]) :
    (n : ZMod (n ^ 2)) * (u : ZMod (n ^ 2)) ^ k =
      (n : ZMod (n ^ 2)) * (v : ZMod (n ^ 2)) ^ k := by
  obtain ⟨c, hc⟩ := huv.dvd
  have hv : v = u + (n : ℤ) * c := by
    linarith
  rw [hv]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have ht := add_multiple_pow_zmod_sq n u c k
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at ht
  rw [ht]
  have hn_sq : (n : ZMod (n ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  linear_combination
    -(k : ZMod (n ^ 2)) * (c : ZMod (n ^ 2)) *
      (u : ZMod (n ^ 2)) ^ (k - 1) * hn_sq

/-! ## Multiplication reindexes a complete residue system -/

/-- Multiplication by a number coprime to `n` permutes the standard
representatives of `ZMod n`, so it preserves every power sum of their
integer representatives. -/
theorem sum_val_pow_mul_coprime {n : ℕ} [NeZero n] (a k : ℕ)
    (ha : a.Coprime n) :
    (∑ x : ZMod n, (x.val : ℤ) ^ k) =
      ∑ x : ZMod n, ((((a : ZMod n) * x).val : ℕ) : ℤ) ^ k := by
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime a ha
  have h := Equiv.sum_comp (Units.mulLeft u) (fun x : ZMod n ↦ (x.val : ℤ) ^ k)
  simpa [u, ZMod.coe_unitOfCoprime] using h.symm

/-- The sum over the canonical representatives of `ZMod n` is the usual
sum over `0, ..., n-1`. -/
theorem sum_val_pow_eq_sum_range_zmod_sq {n : ℕ} [NeZero n] (k : ℕ) :
    (∑ x : ZMod n, (x.val : ZMod (n ^ 2)) ^ k) =
      ∑ m ∈ Finset.range n, (m : ZMod (n ^ 2)) ^ k := by
  exact Finset.sum_bij'
    (fun x _ ↦ x.val)
    (fun m _ ↦ (m : ZMod n))
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ ZMod.natCast_zmod_val x)
    (fun m hm ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hm))
    (fun _ _ ↦ rfl)

/-- Positive powers allow the zero term to be removed from the complete
residue-system sum. -/
theorem sum_val_pow_eq_sum_Ico_zmod_sq {n : ℕ} [NeZero n] {k : ℕ}
    (hk : 0 < k) :
    (∑ x : ZMod n, (x.val : ZMod (n ^ 2)) ^ k) =
      ∑ m ∈ Finset.Ico 1 n, (m : ZMod (n ^ 2)) ^ k := by
  rw [sum_val_pow_eq_sum_range_zmod_sq]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => simp [Finset.sum_range_eq_add_Ico, hk.ne']

/-- Reindex the quotient-weighted Taylor term by the usual representatives
`1, ..., n-1`.  The omitted zero summand vanishes because its quotient is
zero, independently of the exponent. -/
theorem sum_quotient_mul_pow_eq_sum_Ico_zmod_sq {n : ℕ} [NeZero n]
    (a e : ℕ) :
    (∑ x : ZMod n,
        (((a * x.val) / n : ℕ) : ZMod (n ^ 2)) *
          ((a * x.val : ℕ) : ZMod (n ^ 2)) ^ e) =
      ∑ m ∈ Finset.Ico 1 n,
        (((a * m) / n : ℕ) : ZMod (n ^ 2)) *
          ((a * m : ℕ) : ZMod (n ^ 2)) ^ e := by
  calc
    _ = ∑ m ∈ Finset.range n,
        (((a * m) / n : ℕ) : ZMod (n ^ 2)) *
          ((a * m : ℕ) : ZMod (n ^ 2)) ^ e := by
      exact Finset.sum_bij'
        (fun x _ ↦ x.val)
        (fun m _ ↦ (m : ZMod n))
        (fun x _ ↦ Finset.mem_range.mpr x.val_lt)
        (fun _ _ ↦ Finset.mem_univ _)
        (fun x _ ↦ ZMod.natCast_zmod_val x)
        (fun m hm ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hm))
        (fun _ _ ↦ rfl)
    _ = _ := by
      cases n with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => simp [Finset.sum_range_eq_add_Ico]

/-- The summed first-order Taylor identity behind Voronoi's congruence.

Write `a * x.val = n * Q(x) + R(x)`, where `R(x)` is the standard
representative of `a*x` in `ZMod n`.  Expanding modulo `n²` and then using
that `x ↦ a*x` permutes `ZMod n` leaves exactly the displayed first-order
term. -/
theorem taylor_powerSum_zmod_sq {n : ℕ} [NeZero n] (a k : ℕ)
    (ha : a.Coprime n) :
    ((a : ZMod (n ^ 2)) ^ k - 1) *
        (∑ x : ZMod n, (x.val : ZMod (n ^ 2)) ^ k) =
      (k : ZMod (n ^ 2)) * (n : ZMod (n ^ 2)) *
        ∑ x : ZMod n,
          (((a * x.val) / n : ℕ) : ZMod (n ^ 2)) *
            ((a * x.val : ℕ) : ZMod (n ^ 2)) ^ (k - 1) := by
  let R : ZMod n → ℕ := fun x ↦ ((a : ZMod n) * x).val
  let Q : ZMod n → ℕ := fun x ↦ (a * x.val) / n
  let S : ZMod (n ^ 2) := ∑ x : ZMod n, (x.val : ZMod (n ^ 2)) ^ k
  have hR (x : ZMod n) : R x = (a * x.val) % n := by
    simp only [R, ZMod.val_mul, ZMod.val_natCast]
    rw [Nat.mul_mod]
    simp [Nat.mod_eq_of_lt x.val_lt]
  have hdecomp (x : ZMod n) : a * x.val = R x + n * Q x := by
    rw [hR]
    exact (Nat.mod_add_div (a * x.val) n).symm
  have htaylor (x : ZMod n) :
      ((a * x.val : ℕ) : ZMod (n ^ 2)) ^ k =
        (R x : ZMod (n ^ 2)) ^ k +
          (k : ZMod (n ^ 2)) * (n : ZMod (n ^ 2)) *
            (Q x : ZMod (n ^ 2)) * (R x : ZMod (n ^ 2)) ^ (k - 1) := by
    have h := add_multiple_pow_zmod_sq n (R x : ℤ) (Q x : ℤ) k
    rw [hdecomp x]
    push_cast
    simpa [mul_assoc] using h
  have hreindex :
      (∑ x : ZMod n, (R x : ZMod (n ^ 2)) ^ k) = S := by
    have h := sum_val_pow_mul_coprime a k ha
    have h' := congrArg (fun z : ℤ ↦ (z : ZMod (n ^ 2))) h
    push_cast at h'
    apply Eq.symm
    simpa only [S, R] using h'
  have hmul :
      (a : ZMod (n ^ 2)) ^ k * S =
        ∑ x : ZMod n, ((a * x.val : ℕ) : ZMod (n ^ 2)) ^ k := by
    simp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    rw [mul_pow]
  rw [sub_mul, one_mul, hmul]
  simp_rw [htaylor, Finset.sum_add_distrib]
  rw [hreindex, add_sub_cancel_left]
  simp only [Finset.mul_sum]
  simp only [Q, R]
  apply Finset.sum_congr rfl
  intro x _
  have hmod :
      (((a : ZMod n) * x).val : ℤ) ≡ (a * x.val : ℕ) [ZMOD n] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(Q x : ℤ), ?_⟩
    have hd : a * x.val = ((a : ZMod n) * x).val + n * Q x := by
      simpa only [R] using hdecomp x
    push_cast
    omega
  have hp := modulus_mul_pow_eq_of_int_modEq n (k - 1) hmod
  simp only [Int.cast_natCast] at hp
  linear_combination
    (k : ZMod (n ^ 2)) * ((a * x.val) / n : ZMod (n ^ 2)) * hp

/-- Usual complete-residue-system form of the summed Taylor identity.  This
is the exact combinatorial congruence used in the AFP derivation of
Voronoi's theorem. -/
theorem taylor_powerSum_Ico_zmod_sq {n : ℕ} [NeZero n] (a k : ℕ)
    (ha : a.Coprime n) (hk : 0 < k) :
    ((a : ZMod (n ^ 2)) ^ k - 1) *
        (∑ m ∈ Finset.Ico 1 n, (m : ZMod (n ^ 2)) ^ k) =
      (k : ZMod (n ^ 2)) * (n : ZMod (n ^ 2)) *
        ∑ m ∈ Finset.Ico 1 n,
          (((a * m) / n : ℕ) : ZMod (n ^ 2)) *
            ((a * m : ℕ) : ZMod (n ^ 2)) ^ (k - 1) := by
  rw [← sum_val_pow_eq_sum_Ico_zmod_sq hk,
    ← sum_quotient_mul_pow_eq_sum_Ico_zmod_sq]
  exact taylor_powerSum_zmod_sq a k ha

/-- Rational valuation form of the summed Taylor congruence at `n = p^t`.
This is the combinatorial input in exactly the form needed for composition
with the Faulhaber approximation. -/
theorem taylor_powerSum_primePower_hasPadicValAtLeast
    {p t a k : ℕ} [Fact p.Prime]
    (ha : a.Coprime (p ^ t)) (hk : 0 < k) :
    HasPadicValAtLeast p (2 * (t : ℤ))
      (((a : ℚ) ^ k - 1) *
          (∑ m ∈ Finset.Ico 1 (p ^ t), (m : ℚ) ^ k) -
        (k : ℚ) * (p ^ t : ℕ) *
          ∑ m ∈ Finset.Ico 1 (p ^ t),
            (((a * m) / (p ^ t) : ℕ) : ℚ) *
              ((a * m : ℕ) : ℚ) ^ (k - 1)) := by
  let n := p ^ t
  let A : ℤ :=
    ((a : ℤ) ^ k - 1) *
      ∑ m ∈ Finset.Ico 1 n, (m : ℤ) ^ k
  let B : ℤ :=
    (k : ℤ) * n *
      ∑ m ∈ Finset.Ico 1 n,
        (((a * m) / n : ℕ) : ℤ) * ((a * m : ℕ) : ℤ) ^ (k - 1)
  letI : NeZero n := ⟨pow_ne_zero t (Fact.out : p.Prime).ne_zero⟩
  have hAB : (A : ZMod (n ^ 2)) = (B : ZMod (n ^ 2)) := by
    simp only [A, B, Int.cast_mul, Int.cast_sub, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Int.cast_sum]
    simpa only [n] using taylor_powerSum_Ico_zmod_sq a k ha hk
  have hn_sq : n ^ 2 = p ^ (2 * t) := by
    simp only [n]
    rw [mul_comm 2 t, pow_mul]
  have hAB' : (A : ZMod (p ^ (2 * t))) = (B : ZMod (p ^ (2 * t))) := by
    rw [← hn_sq]
    exact hAB
  have hbound := intCast_sub_hasPadicValAtLeast_of_zmod_eq hAB'
  have hexp : ((2 * t : ℕ) : ℤ) = 2 * (t : ℤ) := by norm_num
  rw [hexp] at hbound
  simpa only [A, B, n, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, Int.cast_one, Int.cast_sum, Int.natCast_mul,
    Nat.cast_mul, Int.ofNat_eq_natCast] using hbound

/-- Voronoi's congruence for a prime-power modulus, in zero-aware rational
valuation form.

This theorem is the composition point of the two independent deep inputs
above: the summed Taylor congruence modulo `p^(2t)` and the Faulhaber
remainder bound of the same depth.  Cancelling one factor `p^t` yields the
classical Voronoi depth `t`. -/
theorem voronoi_primePower_hasPadicValAtLeast
    {p t a k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (ht : 1 ≤ t) (ha : a.Coprime (p ^ t))
    (hk : 0 < k) (hkeven : Even k) :
    HasPadicValAtLeast p (t : ℤ)
      (((a : ℚ) ^ k - 1) * bernoulli k -
        (k : ℚ) *
          ∑ m ∈ Finset.Ico 1 (p ^ t),
            (((a * m) / (p ^ t) : ℕ) : ℚ) *
              ((a * m : ℕ) : ℚ) ^ (k - 1)) := by
  let n : ℚ := (p : ℚ) ^ t
  let S : ℚ := ∑ m ∈ Finset.Ico 1 (p ^ t), (m : ℚ) ^ k
  let T : ℚ :=
    ∑ m ∈ Finset.Ico 1 (p ^ t),
      (((a * m) / (p ^ t) : ℕ) : ℚ) *
        ((a * m : ℕ) : ℚ) ^ (k - 1)
  let C : ℚ := (a : ℚ) ^ k - 1
  have hcomb : HasPadicValAtLeast p (2 * (t : ℤ)) (C * S - (k : ℚ) * n * T) := by
    simpa only [C, S, T, n, Nat.cast_pow] using
      taylor_powerSum_primePower_hasPadicValAtLeast ha hk
  have happrox :
      HasPadicValAtLeast p (2 * (t : ℤ)) (S - n * bernoulli k) := by
    simpa only [S, n, Nat.cast_pow] using
      powerSum_sub_bernoulli_primePower_hasPadicValAtLeast hp5 ht hk hkeven
  have hC : HasPadicValAtLeast p 0 C := by
    have h := HasPadicValAtLeast.intCast (p := p) ((a : ℤ) ^ k - 1)
    simpa only [C, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one] using h
  have hprod :
      HasPadicValAtLeast p (2 * (t : ℤ)) (C * (S - n * bernoulli k)) := by
    simpa using hC.mul happrox
  have hdiff := hcomb.sub hprod
  have hfactor :
      (C * S - (k : ℚ) * n * T) - C * (S - n * bernoulli k) =
        n * (C * bernoulli k - (k : ℚ) * T) := by ring
  rw [hfactor] at hdiff
  have hshifted :
      HasPadicValAtLeast p ((t : ℤ) + t)
        ((p : ℚ) ^ t * (C * bernoulli k - (k : ℚ) * T)) := by
    simpa only [n, show (2 : ℤ) * t = t + t by ring] using hdiff
  simpa only [C, T] using HasPadicValAtLeast.of_primePow_mul hshifted

/-- The integer quotient-weighted sum on the right-hand side of Voronoi's
congruence.  Keeping it integer-valued makes the subsequent reduction modulo
`p` independent of rational denominator bookkeeping. -/
def quotientPowerSum (p t a k : ℕ) : ℤ :=
  ∑ m ∈ Finset.Ico 1 (p ^ t),
    (((a * m) / (p ^ t) : ℕ) : ℤ) *
      ((a * m : ℕ) : ℤ) ^ (k - 1)

/-- Voronoi after division by the index.

Applying the prime-power congruence at depth `s + 1` and assuming
`vₚ(k) ≤ s` leaves a congruence of depth one for `Bₖ / k`.  This is the
rational cancellation step used in Kummer's proof. -/
theorem normalized_voronoi_hasPadicValAtLeast_one
    {p s a k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (ha : a.Coprime p) (hk : 0 < k)
    (hkeven : Even k) (hks : padicValNat p k ≤ s) :
    HasPadicValAtLeast p 1
      (((a : ℚ) ^ k - 1) * (bernoulli k / (k : ℚ)) -
        (quotientPowerSum p (s + 1) a k : ℚ)) := by
  have hcoprime : a.Coprime (p ^ (s + 1)) := ha.pow_right (s + 1)
  have h := voronoi_primePower_hasPadicValAtLeast hp5 (by omega)
    hcoprime hk hkeven
  have hfactor :
      ((a : ℚ) ^ k - 1) * bernoulli k -
          (k : ℚ) * (quotientPowerSum p (s + 1) a k : ℚ) =
        (k : ℚ) *
          (((a : ℚ) ^ k - 1) * (bernoulli k / (k : ℚ)) -
            (quotientPowerSum p (s + 1) a k : ℚ)) := by
    field_simp [Nat.cast_ne_zero.mpr hk.ne']
  have h' :
      HasPadicValAtLeast p ((1 : ℤ) + s)
        ((k : ℚ) *
          (((a : ℚ) ^ k - 1) * (bernoulli k / (k : ℚ)) -
            (quotientPowerSum p (s + 1) a k : ℚ))) := by
    rw [← hfactor]
    simpa only [quotientPowerSum, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, Int.cast_pow, Nat.cast_pow,
      show ((s + 1 : ℕ) : ℤ) = (1 : ℤ) + s by omega] using h
  exact HasPadicValAtLeast.of_nat_mul hk.ne' hks h'

/-- Over `ZMod p`, the sum of the `k`-th powers of the nonzero standard
residues is `-1` when `p - 1` divides `k`, and zero otherwise. -/
theorem sum_Ico_pow_zmod {p : ℕ} (k : ℕ) [Fact p.Prime] :
    (∑ a ∈ Ico 1 p, (a : ZMod p) ^ k) =
      if (p - 1) ∣ k then -1 else 0 := by
  have hbij :
      (∑ a ∈ Ico 1 p, (a : ZMod p) ^ k) =
        ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k :=
    Finset.sum_bij'
      (fun a ha ↦ Units.mk0 (a : ZMod p) (mt (ZMod.natCast_eq_zero_iff a p).mp (by
        intro hdvd
        have ha' := Finset.mem_Ico.mp ha
        have hle := Nat.le_of_dvd (by omega : 0 < a) hdvd
        omega)))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun a ha ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp ha).2])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card]

/-- Integer-congruence form of `sum_Ico_pow_zmod`. -/
theorem sum_Ico_pow_int_modEq {p : ℕ} (k : ℕ) [Fact p.Prime] :
    (∑ a ∈ Ico 1 p, (a : ℤ) ^ k) ≡
      (if (p - 1) ∣ k then -1 else 0) [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  exact sum_Ico_pow_zmod k

/-- A nonzero residue has the same powers at exponents congruent modulo
`p - 1`. -/
theorem zmod_pow_eq_pow_of_modEq {p k k' : ℕ} [Fact p.Prime]
    (hkk' : k ≡ k' [MOD p - 1]) {a : ZMod p} (ha : a ≠ 0) :
    a ^ k = a ^ k' := by
  let u : (ZMod p)ˣ := Units.mk0 a ha
  have hu : u ^ k = u ^ k' :=
    (IsOfFinOrder.pow_eq_pow_iff_modEq (isOfFinOrder_of_finite u)).2
      (hkk'.of_dvd (ZMod.orderOf_units_dvd_card_sub_one u))
  exact congrArg Units.val hu

/-- Weighted sums over nonzero residues depend on a positive exponent only
through its class modulo `p - 1`.

The weight is deliberately arbitrary.  In the Voronoi proof it is the
integer quotient `⌊am / p^(s+e)⌋`, reduced modulo `p`; separating it here
makes the later Kummer comparison independent of the floor arithmetic. -/
theorem weightedPowerSum_eq_of_modEq {p k k' : ℕ} [Fact p.Prime]
    (hkk' : k ≡ k' [MOD p - 1]) (w : ℕ → ZMod p) :
    (∑ a ∈ Ico 1 p, (a : ZMod p) ^ k * w a) =
      ∑ a ∈ Ico 1 p, (a : ZMod p) ^ k' * w a := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [zmod_pow_eq_pow_of_modEq hkk' (by
    intro hzero
    have hdvd := (ZMod.natCast_eq_zero_iff a p).mp hzero
    have ha' := Finset.mem_Ico.mp ha
    have hle := Nat.le_of_dvd (by omega : 0 < a) hdvd
    omega)]

/-- The same weighted-power transport for integer-valued weights, expressed
as an integer congruence. -/
theorem weightedPowerSum_int_modEq {p k k' : ℕ} [Fact p.Prime]
    (hkk' : k ≡ k' [MOD p - 1]) (w : ℕ → ℤ) :
    (∑ a ∈ Ico 1 p, (a : ℤ) ^ k * w a) ≡
      (∑ a ∈ Ico 1 p, (a : ℤ) ^ k' * w a) [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  exact weightedPowerSum_eq_of_modEq hkk' fun a ↦ (w a : ZMod p)

end Fermat.Irregular.Voronoi
