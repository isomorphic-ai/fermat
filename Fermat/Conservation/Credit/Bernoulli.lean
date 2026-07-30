/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Pole-safe Bernoulli certificates

This file turns fourth-order modular power sums into prime-cube
certificates for Bernoulli numerators.  The correction is generic over an
arbitrary odd prime: when the adjacent Bernoulli number has a von
Staudt--Clausen pole, it normalizes `p * B_(n-2)` before applying
Faulhaber's formula.
-/
import Mathlib

open scoped BigOperators

namespace Fermat.Conservation.Credit.Bernoulli

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Rational `p`-integrality, stated without importing the repository's
irregular-prime layer. -/
def PIntegral (p : ℕ) (x : ℚ) : Prop :=
  0 ≤ padicValRat p x

theorem pIntegral_zero (p : ℕ) : PIntegral p 0 := by
  simp [PIntegral]

theorem pIntegral_nat (p n : ℕ) : PIntegral p (n : ℚ) := by
  simp only [PIntegral, padicValRat.of_nat]
  exact_mod_cast Nat.zero_le (padicValNat p n)

theorem pIntegral_int (p : ℕ) (z : ℤ) : PIntegral p (z : ℚ) := by
  simp only [PIntegral, padicValRat.of_int]
  exact_mod_cast Nat.zero_le (padicValInt p z)

theorem pIntegral_neg {p : ℕ} {x : ℚ}
    (hx : PIntegral p x) : PIntegral p (-x) := by
  simpa only [PIntegral, padicValRat.neg] using hx

theorem pIntegral_add {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PIntegral p x) (hy : PIntegral p y) : PIntegral p (x + y) := by
  by_cases hxy : x + y = 0
  · simpa [hxy] using pIntegral_zero p
  · exact (le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy)

theorem pIntegral_sub {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PIntegral p x) (hy : PIntegral p y) : PIntegral p (x - y) := by
  rw [sub_eq_add_neg]
  exact pIntegral_add hx (pIntegral_neg hy)

theorem pIntegral_mul {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : PIntegral p x) (hy : PIntegral p y) : PIntegral p (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0, PIntegral]
  by_cases hy0 : y = 0
  · simp [hy0, PIntegral]
  change 0 ≤ padicValRat p x at hx
  change 0 ≤ padicValRat p y at hy
  rw [PIntegral, padicValRat.mul hx0 hy0]
  exact add_nonneg hx hy

theorem pIntegral_sum {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ i ∈ s, PIntegral p (f i)) : PIntegral p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [pIntegral_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact pIntegral_add (hf a (by simp)) (ih fun i hi ↦ hf i (by simp [hi]))

theorem pIntegral_div_nat {p d : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : PIntegral p x) (hd0 : d ≠ 0) (hd : ¬p ∣ d) :
    PIntegral p (x / (d : ℚ)) := by
  by_cases hx0 : x = 0
  · simp [hx0, PIntegral]
  rw [PIntegral, padicValRat.div hx0 (Nat.cast_ne_zero.mpr hd0),
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
  simpa [PIntegral] using hx

theorem pIntegral_prime_div_prime {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) : PIntegral p ((p : ℚ) / q) := by
  by_cases hqp : q = p
  · subst q
    simp [PIntegral, (Fact.out : p.Prime).ne_zero]
  · have hnot : ¬p ∣ q := by
      intro hdvd
      rcases (Nat.dvd_prime hq).mp hdvd with h | h
      · exact (Fact.out : p.Prime).ne_one h
      · exact hqp h.symm
    have hp0 : (p : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    rw [PIntegral, padicValRat.div hp0 hq0, padicValRat.of_nat,
      padicValNat_self, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hnot]
    norm_num

theorem pIntegral_prime_mul_bernoulli_even {p : ℕ} [Fact p.Prime] (k : ℕ) :
    PIntegral p ((p : ℚ) * bernoulli (2 * k)) := by
  let primes :=
    (Finset.range (2 * k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k
  let correction : ℚ := ∑ q ∈ primes, (1 : ℚ) / q
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hz' : bernoulli (2 * k) + correction = (z : ℚ) := by
    simpa [primes, correction] using hz.symm
  have hcorrection : PIntegral p ((p : ℚ) * correction) := by
    rw [Finset.mul_sum]
    apply pIntegral_sum
    intro q hq
    have hq' : q.Prime ∧ (q - 1) ∣ 2 * k := by
      change q ∈ (Finset.range (2 * k + 2)).filter
        (fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k) at hq
      exact (Finset.mem_filter.mp hq).2
    simpa [div_eq_mul_inv, mul_assoc] using
      pIntegral_prime_div_prime (p := p) hq'.1
  have hscaled : (p : ℚ) * bernoulli (2 * k) =
      (p : ℚ) * (z : ℚ) - p * correction := by
    rw [← hz']
    ring
  rw [hscaled]
  exact pIntegral_sub
    (pIntegral_mul (pIntegral_nat p p) (pIntegral_int p z)) hcorrection

theorem pIntegral_prime_mul_bernoulli {p : ℕ} [Fact p.Prime]
    (hpOdd : Odd p) (n : ℕ) :
    PIntegral p ((p : ℚ) * bernoulli n) := by
  rcases n.even_or_odd with heven | hodd
  · obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp heven
    exact pIntegral_prime_mul_bernoulli_even k
  · by_cases hn : n = 1
    · subst n
      rw [bernoulli_one]
      have heq : (p : ℚ) * (-1 / 2) = -(p : ℚ) / 2 := by ring
      rw [heq]
      exact pIntegral_div_nat (x := -(p : ℚ)) (d := 2)
        (pIntegral_neg (pIntegral_nat p p)) (by norm_num)
        (by
          intro hp2
          have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hp2
          have htwo : p = 2 := by
            have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
            omega
          subst p
          norm_num at hpOdd)
    · have hn1 : 1 < n := by
        have hn0 : n ≠ 0 := by
          intro hzero
          subst n
          norm_num at hodd
        omega
      rw [bernoulli_eq_zero_of_odd hodd hn1, mul_zero]
      exact pIntegral_zero p

theorem pIntegral_one_div_prime_of_ne
    {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hne : q ≠ p) :
    PIntegral p ((1 : ℚ) / q) := by
  have hnot : ¬p ∣ q := by
    intro hdvd
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hne h.symm
  exact pIntegral_div_nat (d := q)
    (pIntegral_nat p 1) hq.ne_zero hnot

/-- Von Staudt--Clausen in the exact normalized form required by the
exceptional row: `p * B_(2p-2) = -1 (mod p)` in the `p`-integral rationals. -/
theorem prime_mul_exceptional_predecessor_representation
    {p : ℕ} [Fact p.Prime] :
    ∃ u : ℚ, PIntegral p u ∧
      (p : ℚ) * bernoulli (2 * (p - 1)) =
        -1 + p * u := by
  let primes :=
    (Finset.range (2 * (p - 1) + 2)).filter fun q ↦
      q.Prime ∧ (q - 1) ∣ 2 * (p - 1)
  let rest : ℚ :=
    ∑ q ∈ primes.erase p, (1 : ℚ) / q
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen (p - 1)
  have hz' :
      bernoulli (2 * (p - 1)) +
          (∑ q ∈ primes, (1 : ℚ) / q) =
        (z : ℚ) := by
    simpa [primes] using hz.symm
  have hp_mem : p ∈ primes := by
    apply Finset.mem_filter.mpr
    refine
      ⟨Finset.mem_range.mpr ?_, Fact.out,
        dvd_mul_left (p - 1) 2⟩
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hsplit :
      (∑ q ∈ primes, (1 : ℚ) / q) =
        (1 : ℚ) / p + rest := by
    simpa [rest] using
      (Finset.add_sum_erase primes
        (fun q ↦ (1 : ℚ) / q) hp_mem).symm
  have hrest : PIntegral p rest := by
    apply pIntegral_sum
    intro q hq
    have hmemErase : q ∈ primes.erase p := by
      simpa [rest] using hq
    have hne : q ≠ p := (Finset.mem_erase.mp hmemErase).1
    have hprime : q.Prime := by
      have hmem : q ∈ primes := (Finset.mem_erase.mp hmemErase).2
      exact (Finset.mem_filter.mp hmem).2.1
    exact pIntegral_one_div_prime_of_ne hprime hne
  refine
    ⟨(z : ℚ) - rest,
      pIntegral_sub (pIntegral_int p z) hrest, ?_⟩
  rw [hsplit] at hz'
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  field_simp [hp0] at hz' ⊢
  linear_combination hz'

def faulhaberTerm (p n i : ℕ) : ℚ :=
  bernoulli i * ((n + 1).choose i : ℚ) *
    (p : ℚ) ^ (n + 1 - i) / (n + 1)

def lowQuotient (p n i : ℕ) : ℚ :=
  ((p : ℚ) * bernoulli i) * ((n + 1).choose i : ℚ) *
    (p : ℚ) ^ (n - 4 - i) / (n + 1)

theorem pIntegral_lowQuotient {p n i : ℕ} [Fact p.Prime]
    (hpOdd : Odd p) (hden : ¬p ∣ n + 1) :
    PIntegral p (lowQuotient p n i) := by
  unfold lowQuotient
  have hnum : PIntegral p
      (((p : ℚ) * bernoulli i) * ((n + 1).choose i : ℚ) *
        (p : ℚ) ^ (n - 4 - i)) := by
    apply pIntegral_mul
    · exact pIntegral_mul (pIntegral_prime_mul_bernoulli hpOdd i)
        (pIntegral_nat p ((n + 1).choose i))
    · simpa only [Nat.cast_pow] using
        pIntegral_nat p (p ^ (n - 4 - i))
  simpa only [Nat.cast_add, Nat.cast_one] using
    pIntegral_div_nat (d := n + 1) hnum (by omega) hden

theorem faulhaberTerm_eq_pow_four_mul_lowQuotient {p n i : ℕ}
    (hn : 4 ≤ n) (hi : i < n - 3) :
    faulhaberTerm p n i = (p : ℚ) ^ 4 * lowQuotient p n i := by
  have hexp : n + 1 - i = 4 + 1 + (n - 4 - i) := by omega
  rw [faulhaberTerm, lowQuotient, hexp, pow_add, pow_add]
  ring

theorem lowRemainder_eq {p n : ℕ} (hn : 4 ≤ n) :
    (∑ i ∈ Finset.range (n - 3), faulhaberTerm p n i) =
      (p : ℚ) ^ 4 *
        ∑ i ∈ Finset.range (n - 3), lowQuotient p n i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact faulhaberTerm_eq_pow_four_mul_lowQuotient hn
    (Finset.mem_range.mp hi)

theorem pIntegral_lowQuotient_sum {p n : ℕ} [Fact p.Prime]
    (hpOdd : Odd p) (hden : ¬p ∣ n + 1) :
    PIntegral p
      (∑ i ∈ Finset.range (n - 3), lowQuotient p n i) := by
  exact pIntegral_sum fun i _ ↦ pIntegral_lowQuotient hpOdd hden

/-- The pole-safe top quotient in the exceptional Faulhaber row. Unlike
`B_(n-2) * c/(n+1)`, this is integral at `p` when `B_(n-2)` has its
von-Staudt factor `p` in the denominator. -/
def exceptionalTopQuotient (p n c : ℕ) : ℚ :=
  ((p : ℚ) * bernoulli (n - 2)) * (c : ℚ) / (n + 1)

theorem faulhaberTerm_exceptionalTop_eq {p n c : ℕ}
    (hn : 4 ≤ n)
    (hchoose : (n + 1).choose (n - 2) = p * c) :
    faulhaberTerm p n (n - 2) =
      (p : ℚ) ^ 3 * exceptionalTopQuotient p n c := by
  rw [faulhaberTerm, exceptionalTopQuotient, hchoose]
  have hexp : n + 1 - (n - 2) = 3 := by omega
  rw [hexp]
  push_cast
  ring

theorem faulhaberTerm_last_eq {p n : ℕ} :
    faulhaberTerm p n n = (p : ℚ) * bernoulli n := by
  rw [faulhaberTerm, Nat.choose_succ_self_right]
  have hexp : n + 1 - n = 1 := by omega
  rw [hexp, pow_one]
  field_simp
  push_cast
  ring

theorem faulhaberTerm_odd_eq_zero {p n i : ℕ}
    (hi : Odd i) (hi1 : 1 < i) :
    faulhaberTerm p n i = 0 := by
  rw [faulhaberTerm, bernoulli_eq_zero_of_odd hi hi1]
  ring

/-- Generic Faulhaber decomposition for the exceptional adjacent pole.
The `B_(n-2)` term is deliberately only factored by `p^3`, with the
remaining factor normalized as `p * B_(n-2)`. -/
theorem exceptional_faulhaber_decomposition {p n c : ℕ}
    (hn : 6 ≤ n) (heven : Even n)
    (hchoose : (n + 1).choose (n - 2) = p * c) :
    (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
      (p : ℚ) ^ 4 *
          (∑ i ∈ Finset.range (n - 3), lowQuotient p n i) +
        (p : ℚ) ^ 3 * exceptionalTopQuotient p n c +
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
      (Finset.sum_range_succ
        (f := fun i ↦ faulhaberTerm p n i) (n - 1))
  have hsplit2 :
      (∑ i ∈ Finset.range (n - 1), faulhaberTerm p n i) =
        (∑ i ∈ Finset.range (n - 2), faulhaberTerm p n i) +
          faulhaberTerm p n (n - 2) := by
    have h :=
      Finset.sum_range_succ
        (f := fun i ↦ faulhaberTerm p n i) (n - 2)
    have heq : n - 2 + 1 = n - 1 := by omega
    simpa only [heq] using h
  have hsplit3 :
      (∑ i ∈ Finset.range (n - 2), faulhaberTerm p n i) =
        (∑ i ∈ Finset.range (n - 3), faulhaberTerm p n i) +
          faulhaberTerm p n (n - 3) := by
    have h :=
      Finset.sum_range_succ
        (f := fun i ↦ faulhaberTerm p n i) (n - 3)
    have heq : n - 3 + 1 = n - 2 := by omega
    simpa only [heq] using h
  rw [hfaulhaber, Finset.sum_range_succ,
    hsplit1, hsplit2, hsplit3,
    lowRemainder_eq (by omega : 4 ≤ n),
    faulhaberTerm_odd_eq_zero hodd3 (by omega),
    faulhaberTerm_exceptionalTop_eq (by omega : 4 ≤ n) hchoose,
    faulhaberTerm_odd_eq_zero hodd1 (by omega),
    faulhaberTerm_last_eq]
  ring

def powerSumInt (p n : ℕ) : ℤ :=
  ∑ a ∈ Finset.range p, (a : ℤ) ^ n

/-- A `ZMod (p^4)` power-sum certificate can be lifted to an equality over
the rationals with an unknown integral multiple of `p^4`. -/
theorem powerSumRat_eq {p n raw : ℕ} [Fact p.Prime]
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * raw) :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
        p * (raw : ℚ) + (p : ℚ) ^ 4 * (t : ℚ) := by
  have hcast :
      ((powerSumInt p n - p * raw : ℤ) : ZMod (p ^ 4)) = 0 := by
    rw [Int.cast_sub]
    have hsum :
        (powerSumInt p n : ZMod (p ^ 4)) =
          ∑ a ∈ Finset.range p, (a : ZMod (p ^ 4)) ^ n := by
      simp [powerSumInt]
    rw [hsum, hmod]
    push_cast
    ring
  have hdvd : ((p ^ 4 : ℕ) : ℤ) ∣ powerSumInt p n - p * raw :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  have ht' : powerSumInt p n = p * raw + (p : ℤ) ^ 4 * t := by
    push_cast at ht ⊢
    omega
  have htRat := congrArg (fun z : ℤ ↦ (z : ℚ)) ht'
  push_cast at htRat
  simpa [powerSumInt] using htRat

/-- Core correction lemma.

`raw` is the residue obtained after removing the leading `p` from the
power sum. `q` certifies `p * B_(n-2) mod p`; `w` certifies
`c/(n+1) mod p`. Consequently the target residue is

`raw - p^2*q*w mod p^3`.

The `hdecomp` premise is the generic pole-safe Faulhaber decomposition; it
is separated here so the correction algebra has a small stable API. -/
theorem exceptional_corrected_representation
    {p n c raw s : ℕ} {q w correctionLift : ℤ} [Fact p.Prime]
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * raw)
    (hdecomp :
      ∃ low : ℚ, PIntegral p low ∧
        (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
          (p : ℚ) ^ 4 * low +
            (p : ℚ) ^ 3 * exceptionalTopQuotient p n c +
              p * bernoulli n)
    (hprev :
      ∃ v : ℚ, PIntegral p v ∧
        (p : ℚ) * bernoulli (n - 2) =
          (q : ℚ) + p * v)
    (hweight :
      ∃ z : ℚ, PIntegral p z ∧
        (c : ℚ) / (n + 1) =
          (w : ℚ) + p * z)
    (hnormalize :
      (raw : ℤ) - (p : ℤ) ^ 2 * q * w =
        (s : ℤ) + (p : ℤ) ^ 3 * correctionLift) :
    ∃ u : ℚ, PIntegral p u ∧
      bernoulli n = (s : ℚ) + (p : ℚ) ^ 3 * u := by
  obtain ⟨t, ht⟩ := powerSumRat_eq hmod
  obtain ⟨low, hlow, hdecomp⟩ := hdecomp
  obtain ⟨v, hv, hprev⟩ := hprev
  obtain ⟨z, hz, hweight⟩ := hweight
  let error : ℚ := (q : ℚ) * z + v * ((w : ℚ) + p * z)
  have herror : PIntegral p error := by
    apply pIntegral_add
    · exact pIntegral_mul (pIntegral_int p q) hz
    · apply pIntegral_mul hv
      exact pIntegral_add (pIntegral_int p w)
        (pIntegral_mul (pIntegral_nat p p) hz)
  have htop :
      exceptionalTopQuotient p n c =
        (q : ℚ) * (w : ℚ) + (p : ℚ) * error := by
    rw [exceptionalTopQuotient, hprev]
    calc
      ((q : ℚ) + p * v) * (c : ℚ) / (n + 1) =
          ((q : ℚ) + p * v) * ((c : ℚ) / (n + 1)) := by ring
      _ = ((q : ℚ) + p * v) * ((w : ℚ) + p * z) := by rw [hweight]
      _ = (q : ℚ) * (w : ℚ) + (p : ℚ) * error := by
        dsimp [error]
        ring
  have hnormalizeRat := congrArg (fun z : ℤ ↦ (z : ℚ)) hnormalize
  push_cast at hnormalizeRat
  refine
    ⟨(correctionLift : ℚ) + (t : ℚ) - low - error, ?_, ?_⟩
  · exact pIntegral_sub
      (pIntegral_sub
        (pIntegral_add (pIntegral_int p correctionLift)
          (pIntegral_int p t))
        hlow)
      herror
  · rw [hdecomp, htop] at ht
    have hp0 : (p : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    apply mul_left_cancel₀ hp0
    calc
      (p : ℚ) * bernoulli n =
          p * (s + (p : ℚ) ^ 3 *
            ((correctionLift : ℚ) + (t : ℚ) - low - error)) := by
              linear_combination ht + p * hnormalizeRat
      _ = (p : ℚ) *
          ((s : ℚ) + (p : ℚ) ^ 3 *
            ((correctionLift : ℚ) + (t : ℚ) - low - error)) := by
              ring

/-- One-call pole-safe Faulhaber API. All premises after the universal
arithmetic side conditions are finite certificates suitable for a thin
per-prime instance. -/
theorem exceptional_bernoulli_representation_of_faulhaber
    {p n c raw s : ℕ} {q w correctionLift : ℤ} [Fact p.Prime]
    (hpOdd : Odd p) (hn : 6 ≤ n) (heven : Even n)
    (hdenNext : ¬p ∣ n + 1)
    (hchoose : (n + 1).choose (n - 2) = p * c)
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * raw)
    (hprev :
      ∃ v : ℚ, PIntegral p v ∧
        (p : ℚ) * bernoulli (n - 2) =
          (q : ℚ) + p * v)
    (hweight :
      ∃ z : ℚ, PIntegral p z ∧
        (c : ℚ) / (n + 1) =
          (w : ℚ) + p * z)
    (hnormalize :
      (raw : ℤ) - (p : ℤ) ^ 2 * q * w =
        (s : ℤ) + (p : ℤ) ^ 3 * correctionLift) :
    ∃ u : ℚ, PIntegral p u ∧
      bernoulli n = (s : ℚ) + (p : ℚ) ^ 3 * u := by
  apply exceptional_corrected_representation hmod
  · refine
      ⟨∑ i ∈ Finset.range (n - 3), lowQuotient p n i,
        pIntegral_lowQuotient_sum hpOdd hdenNext, ?_⟩
    exact exceptional_faulhaber_decomposition hn heven hchoose
  · exact hprev
  · exact hweight
  · exact hnormalize

def DenominatorPrimeTo (p : ℕ) (x : ℚ) : Prop :=
  ¬p ∣ x.den

theorem bernoulli_denominatorPrimeTo_of_not_dvd_sub_one
    {p k : ℕ} [Fact p.Prime]
    (hnot : ¬(p - 1) ∣ 2 * k) :
    DenominatorPrimeTo p (bernoulli (2 * k)) := by
  let primes :=
    (Finset.range (2 * k + 2)).filter fun q ↦
      q.Prime ∧ (q - 1) ∣ 2 * k
  let correction : ℚ :=
    ∑ q ∈ primes, (1 : ℚ) / q
  have hprod :
      (∏ q ∈ primes, ((1 : ℚ) / q).den).Coprime p := by
    refine Nat.Coprime.prod_left fun q hq ↦ ?_
    have hq' :
        q ∈ Finset.range (2 * k + 2) ∧
          q.Prime ∧ (q - 1) ∣ 2 * k := by
      simpa [primes] using hq
    have hne : q ≠ p := fun h ↦
      hnot (h ▸ hq'.2.2)
    rw [show ((1 : ℚ) / q).den = q by
      simp [hq'.2.1.ne_zero]]
    exact
      (Nat.coprime_primes hq'.2.1 Fact.out).mpr hne
  have hcorrection : correction.den.Coprime p := by
    refine Nat.Coprime.of_dvd_left ?_ hprod
    exact Finset.Rat.den_sum_dvd_prod_den primes
      fun q ↦ (1 : ℚ) / q
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hsum :
      (∑ q ∈ Finset.range (2 * k + 2) with
        q.Prime ∧ (q - 1) ∣ 2 * k,
          (1 : ℚ) / q) = correction := by
    rfl
  rw [hsum] at hz
  have hbernoulli :
      bernoulli (2 * k) = (z : ℚ) - correction := by
    linarith
  rw [hbernoulli]
  change ¬p ∣ ((z : ℚ) - correction).den
  rw [Rat.intCast_sub_den]
  exact
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
      hcorrection.symm

theorem bernoulli_denominatorPrimeTo
    {p n : ℕ} [Fact p.Prime]
    (heven : Even n) (hnot : ¬(p - 1) ∣ n) :
    DenominatorPrimeTo p (bernoulli n) := by
  obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp heven
  exact
    bernoulli_denominatorPrimeTo_of_not_dvd_sub_one hnot

theorem padicValRat_eq_numeratorVal {p : ℕ} {x : ℚ}
    (hden : DenominatorPrimeTo p x) :
    padicValRat p x = padicValInt p x.num := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden]
  simp

theorem pIntegral_of_denominatorPrimeTo
    {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hden : DenominatorPrimeTo p x) :
    PIntegral p x := by
  rw [PIntegral, padicValRat_eq_numeratorVal hden]
  exact_mod_cast Nat.zero_le (padicValInt p x.num)

theorem numerator_pow_dvd_iff_le_padicValRat
    {p exponent : ℕ} {x : ℚ} [Fact p.Prime]
    (hx : x ≠ 0) (hden : DenominatorPrimeTo p x) :
    (p : ℤ) ^ exponent ∣ x.num ↔
      (exponent : ℤ) ≤ padicValRat p x := by
  rw [padicValRat_eq_numeratorVal hden, padicValInt_dvd_iff]
  simp [Rat.num_ne_zero.mpr hx]

theorem numerator_not_dvd_pow_of_padicValRat_lt
    {p exponent : ℕ} {x : ℚ} [Fact p.Prime]
    (hx : x ≠ 0) (hden : DenominatorPrimeTo p x)
    (hval : padicValRat p x < exponent) :
    ¬(p : ℤ) ^ exponent ∣ x.num := by
  intro hdvd
  exact (not_le_of_gt hval)
    ((numerator_pow_dvd_iff_le_padicValRat hx hden).mp hdvd)

theorem padicValRat_prime_cube {p : ℕ} [Fact p.Prime] :
    padicValRat p ((p : ℚ) ^ 3) = 3 := by
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValRat.pow hp0, padicValRat.of_nat, padicValNat_self]
  norm_num

theorem representation_ne_zero_and_padicValRat_eq
    {p residue : ℕ} [Fact p.Prime] {x u : ℚ}
    (hresidue0 : residue ≠ 0) (hu : PIntegral p u)
    (hx : x = (residue : ℚ) + (p : ℚ) ^ 3 * u)
    (hresidueLt : padicValRat p (residue : ℚ) < 3) :
    x ≠ 0 ∧
      padicValRat p x = padicValRat p (residue : ℚ) := by
  have hrq0 : (residue : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hresidue0
  by_cases hu0 : u = 0
  · rw [hx, hu0, mul_zero, add_zero]
    exact ⟨hrq0, rfl⟩
  · have hpow0 : (p : ℚ) ^ 3 ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr
        (Fact.out : p.Prime).ne_zero)
    have hrem0 : (p : ℚ) ^ 3 * u ≠ 0 :=
      mul_ne_zero hpow0 hu0
    have hremval :
        3 ≤ padicValRat p ((p : ℚ) ^ 3 * u) := by
      change 0 ≤ padicValRat p u at hu
      rw [padicValRat.mul hpow0 hu0, padicValRat_prime_cube]
      omega
    have hlt :
        padicValRat p (residue : ℚ) <
          padicValRat p ((p : ℚ) ^ 3 * u) :=
      hresidueLt.trans_le hremval
    have hsum0 :
        (residue : ℚ) + (p : ℚ) ^ 3 * u ≠ 0 := by
      intro hzero
      have heq :
          (residue : ℚ) = -((p : ℚ) ^ 3 * u) := by
        linarith
      have hvals := congrArg (padicValRat p) heq
      rw [padicValRat.neg] at hvals
      omega
    rw [hx]
    exact
      ⟨hsum0,
        padicValRat.add_eq_of_lt hsum0 hrq0 hrem0 hlt⟩

theorem numerator_not_dvd_cube_of_representation
    {p residue : ℕ} [Fact p.Prime] {x u : ℚ}
    (hresidue0 : residue ≠ 0)
    (hresidueCube : ¬(p : ℤ) ^ 3 ∣ (residue : ℤ))
    (hden : DenominatorPrimeTo p x)
    (hu : PIntegral p u)
    (hx : x = (residue : ℚ) + (p : ℚ) ^ 3 * u) :
    ¬(p : ℤ) ^ 3 ∣ x.num := by
  have hdenResidue :
      DenominatorPrimeTo p (residue : ℚ) := by
    simp [DenominatorPrimeTo, (Fact.out : p.Prime).ne_one]
  have hresidueLt :
      padicValRat p (residue : ℚ) < 3 := by
    by_contra hnotlt
    have hle :
        (3 : ℤ) ≤ padicValRat p (residue : ℚ) := by
      omega
    apply hresidueCube
    simpa using
      (numerator_pow_dvd_iff_le_padicValRat
        (p := p) (exponent := 3)
        (Nat.cast_ne_zero.mpr hresidue0)
        hdenResidue).mpr hle
  obtain ⟨hx0, hval⟩ :=
    representation_ne_zero_and_padicValRat_eq
      hresidue0 hu hx hresidueLt
  apply numerator_not_dvd_pow_of_padicValRat_lt hx0 hden
  rw [hval]
  exact hresidueLt

/-- Direct exceptional endpoint: the corrected residue, rather than the raw
power-sum residue, controls cube-freeness of the target numerator. -/
theorem exceptional_bernoulli_numerator_not_dvd_cube_of_faulhaber
    {p n c raw residue : ℕ}
    {q w correctionLift : ℤ} [Fact p.Prime]
    (hpOdd : Odd p) (hn : 6 ≤ n) (heven : Even n)
    (hdenNext : ¬p ∣ n + 1)
    (hchoose : (n + 1).choose (n - 2) = p * c)
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * raw)
    (hprev :
      ∃ v : ℚ, PIntegral p v ∧
        (p : ℚ) * bernoulli (n - 2) =
          (q : ℚ) + p * v)
    (hweight :
      ∃ z : ℚ, PIntegral p z ∧
        (c : ℚ) / (n + 1) =
          (w : ℚ) + p * z)
    (hnormalize :
      (raw : ℤ) - (p : ℤ) ^ 2 * q * w =
        (residue : ℤ) + (p : ℤ) ^ 3 * correctionLift)
    (hresidue0 : residue ≠ 0)
    (hresidueCube :
      ¬(p : ℤ) ^ 3 ∣ (residue : ℤ))
    (htarget :
      DenominatorPrimeTo p (bernoulli n)) :
    ¬(p : ℤ) ^ 3 ∣ (bernoulli n).num := by
  obtain ⟨u, hu, hB⟩ :=
    exceptional_bernoulli_representation_of_faulhaber
      hpOdd hn heven hdenNext hchoose hmod
      hprev hweight hnormalize
  exact numerator_not_dvd_cube_of_representation
    hresidue0 hresidueCube htarget hu hB

end Fermat.Conservation.Credit.Bernoulli
