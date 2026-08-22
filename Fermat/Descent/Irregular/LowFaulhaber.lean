import Fermat.Descent.Irregular.DirectBernoulli

/-!
# Low-precision Faulhaber contacts

This module converts a finite power-sum receipt modulo `p³` into a
`p²`-accurate representation of the corresponding Bernoulli number.
It is the low-index provenance bridge used before Sun's depth-two
interpolation: two short contacts replace one lifted high-index check.

The computation remains an ordinary kernel-checked finite sum. The
improvement is that its exponent is a low Bernoulli contact rather than
the lifted target index.
-/
namespace Fermat.Irregular.LowFaulhaber

open Fermat.Irregular.DirectBernoulli

set_option maxRecDepth 100000

/-- The `p^3`-precision top quotient.  Unlike the lifted `p^4` engine,
this version needs no extra factor of `p` in the top binomial coefficient. -/
def cubeTopQuotient (n : ℕ) : ℚ :=
  bernoulli (n - 2) * ((n + 1).choose (n - 2) : ℚ) / (n + 1)

theorem pIntegral_cubeTopQuotient {p n : ℕ} [Fact p.Prime]
    (hden : ¬p ∣ n + 1) (hprev : PIntegral p (bernoulli (n - 2))) :
    PIntegral p (cubeTopQuotient n) := by
  unfold cubeTopQuotient
  have hnum : PIntegral p
      (bernoulli (n - 2) * ((n + 1).choose (n - 2) : ℚ)) :=
    pIntegral_mul hprev (pIntegral_nat p ((n + 1).choose (n - 2)))
  simpa only [Nat.cast_add, Nat.cast_one] using
    pIntegral_div_nat (d := n + 1) hnum (by omega) hden

theorem faulhaberTerm_top_cube_eq {p n : ℕ} (hn : 4 ≤ n) :
    faulhaberTerm p n (n - 2) =
      (p : ℚ) ^ 3 * cubeTopQuotient n := by
  rw [faulhaberTerm, cubeTopQuotient]
  have hexp : n + 1 - (n - 2) = 3 := by omega
  rw [hexp]
  ring

/-- Faulhaber decomposition at one digit less precision than the existing
lifted-channel engine. -/
theorem faulhaber_decomposition_cube {p n : ℕ}
    (hn : 6 ≤ n) (heven : Even n) :
    (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
      (p : ℚ) ^ 3 *
          ((p : ℚ) *
              (∑ i ∈ Finset.range (n - 3), lowQuotient p n i) +
            cubeTopQuotient n) +
        p * bernoulli n := by
  have hfaulhaber :
      (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
        ∑ i ∈ Finset.range (n + 1), faulhaberTerm p n i := by
    simpa [faulhaberTerm] using sum_range_pow p n
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp heven
  have hodd3 : Odd (n - 3) := by
    refine ⟨k - 2, ?_⟩
    omega
  have hodd1 : Odd (n - 1) := by
    refine ⟨k - 1, ?_⟩
    omega
  have hsplit1 :
      (∑ i ∈ Finset.range n, faulhaberTerm p n i) =
        (∑ i ∈ Finset.range (n - 1), faulhaberTerm p n i) +
          faulhaberTerm p n (n - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      (Finset.sum_range_succ (f := fun i ↦ faulhaberTerm p n i) (n - 1))
  have hsplit2 :
      (∑ i ∈ Finset.range (n - 1), faulhaberTerm p n i) =
        (∑ i ∈ Finset.range (n - 2), faulhaberTerm p n i) +
          faulhaberTerm p n (n - 2) := by
    have h := Finset.sum_range_succ
      (f := fun i ↦ faulhaberTerm p n i) (n - 2)
    have heq : n - 2 + 1 = n - 1 := by omega
    simpa only [heq] using h
  have hsplit3 :
      (∑ i ∈ Finset.range (n - 2), faulhaberTerm p n i) =
        (∑ i ∈ Finset.range (n - 3), faulhaberTerm p n i) +
          faulhaberTerm p n (n - 3) := by
    have h := Finset.sum_range_succ
      (f := fun i ↦ faulhaberTerm p n i) (n - 3)
    have heq : n - 3 + 1 = n - 2 := by omega
    simpa only [heq] using h
  rw [hfaulhaber, Finset.sum_range_succ,
    hsplit1, hsplit2, hsplit3,
    lowRemainder_eq (by omega : 4 ≤ n),
    faulhaberTerm_odd_eq_zero hodd3 (by omega),
    faulhaberTerm_top_cube_eq (by omega : 4 ≤ n),
    faulhaberTerm_odd_eq_zero hodd1 (by omega),
    faulhaberTerm_last_eq]
  ring

def cubeRemainder (p n : ℕ) : ℚ :=
  (p : ℚ) * (∑ i ∈ Finset.range (n - 3), lowQuotient p n i) +
    cubeTopQuotient n

theorem pIntegral_cubeRemainder {p n : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hden : ¬p ∣ n + 1)
    (hprev : PIntegral p (bernoulli (n - 2))) :
    PIntegral p (cubeRemainder p n) := by
  unfold cubeRemainder
  exact pIntegral_add
    (pIntegral_mul (pIntegral_nat p p)
      (pIntegral_lowQuotient_sum hp5 hden))
    (pIntegral_cubeTopQuotient hden hprev)

def powerSumInt (p n : ℕ) : ℤ :=
  ∑ a ∈ Finset.range p, (a : ℤ) ^ n

theorem powerSumRat_eq_cube {p n r : ℕ} [Fact p.Prime]
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 3)) ^ n) = p * r) :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
        p * (r : ℚ) + (p : ℚ) ^ 3 * (t : ℚ) := by
  have hcast :
      ((powerSumInt p n - p * r : ℤ) : ZMod (p ^ 3)) = 0 := by
    rw [Int.cast_sub]
    have hsum :
        (powerSumInt p n : ZMod (p ^ 3)) =
          ∑ a ∈ Finset.range p, (a : ZMod (p ^ 3)) ^ n := by
      simp [powerSumInt]
    rw [hsum, hmod]
    push_cast
    ring
  have hdvd : ((p ^ 3 : ℕ) : ℤ) ∣ powerSumInt p n - p * r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  have ht' : powerSumInt p n = p * r + (p : ℤ) ^ 3 * t := by
    push_cast at ht ⊢
    omega
  have htRat := congrArg (fun z : ℤ ↦ (z : ℚ)) ht'
  push_cast at htRat
  simpa [powerSumInt] using htRat

/-- A power sum modulo `p^3` determines `B_n` modulo `p^2`. -/
theorem bernoulli_representation_of_powerSum_cube
    {p n r : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 6 ≤ n) (heven : Even n)
    (hden : ¬p ∣ n + 1)
    (hprev : PIntegral p (bernoulli (n - 2)))
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 3)) ^ n) = p * r) :
    ∃ u : ℚ, PIntegral p u ∧
      bernoulli n = (r : ℚ) + (p : ℚ) ^ 2 * u := by
  obtain ⟨t, ht⟩ := powerSumRat_eq_cube hmod
  have hdecomp := faulhaber_decomposition_cube (p := p) hn heven
  rw [hdecomp] at ht
  have hrem : PIntegral p (cubeRemainder p n) :=
    pIntegral_cubeRemainder hp5 hden hprev
  refine ⟨(t : ℚ) - cubeRemainder p n,
    pIntegral_sub (pIntegral_int p t) hrem, ?_⟩
  change (p : ℚ) ^ 3 * cubeRemainder p n + p * bernoulli n =
    p * (r : ℚ) + (p : ℚ) ^ 3 * (t : ℚ) at ht
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcanceled :
      (p : ℚ) ^ 2 * cubeRemainder p n + bernoulli n =
        (r : ℚ) + (p : ℚ) ^ 2 * (t : ℚ) := by
    apply mul_left_cancel₀ hp0
    calc
      (p : ℚ) * ((p : ℚ) ^ 2 * cubeRemainder p n + bernoulli n) =
          (p : ℚ) ^ 3 * cubeRemainder p n + p * bernoulli n := by ring
      _ = p * (r : ℚ) + (p : ℚ) ^ 3 * (t : ℚ) := ht
      _ = (p : ℚ) * ((r : ℚ) + (p : ℚ) ^ 2 * (t : ℚ)) := by ring
  linear_combination hcanceled

theorem padicValRat_prime_square {p : ℕ} [Fact p.Prime] :
    padicValRat p ((p : ℚ) ^ 2) = 2 := by
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValRat.pow hp0, padicValRat.of_nat, padicValNat_self]
  norm_num

/-- A `p^2`-accurate representation preserves any residue valuation below
two. -/
theorem representation_square_ne_zero_and_padicValRat_eq
    {p r : ℕ} [Fact p.Prime] {x u : ℚ}
    (hr0 : r ≠ 0) (hu : PIntegral p u)
    (hx : x = (r : ℚ) + (p : ℚ) ^ 2 * u)
    (hrlt : padicValRat p (r : ℚ) < 2) :
    x ≠ 0 ∧ padicValRat p x = padicValRat p (r : ℚ) := by
  have hrq0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  by_cases hu0 : u = 0
  · rw [hx, hu0, mul_zero, add_zero]
    exact ⟨hrq0, rfl⟩
  · have hpow0 : (p : ℚ) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hrem0 : (p : ℚ) ^ 2 * u ≠ 0 := mul_ne_zero hpow0 hu0
    have hremval : 2 ≤ padicValRat p ((p : ℚ) ^ 2 * u) := by
      change 0 ≤ padicValRat p u at hu
      rw [padicValRat.mul hpow0 hu0, padicValRat_prime_square]
      omega
    have hlt :
        padicValRat p (r : ℚ) <
          padicValRat p ((p : ℚ) ^ 2 * u) := hrlt.trans_le hremval
    have hsum0 : (r : ℚ) + (p : ℚ) ^ 2 * u ≠ 0 := by
      intro hzero
      have heq : (r : ℚ) = -((p : ℚ) ^ 2 * u) := by linarith
      have hvals := congrArg (padicValRat p) heq
      rw [padicValRat.neg] at hvals
      omega
    rw [hx]
    exact ⟨hsum0,
      padicValRat.add_eq_of_lt hsum0 hrq0 hrem0 hlt⟩

end Fermat.Irregular.LowFaulhaber
