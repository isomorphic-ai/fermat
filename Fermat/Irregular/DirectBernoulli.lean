import Fermat.Irregular.VandiverData

/-!
# Direct Faulhaber certificates for high Bernoulli numerators

This module extracts the prime-independent engine first developed for
exponent `37`.  For an odd prime `p`, Faulhaber's formula separates a finite
power sum into a multiple of `p^4`, one explicitly controlled top term, and
`p * B_n`.  Consequently an equality in `ZMod (p^4)` determines `B_n`
modulo `p^3`.

`bernoulli_numerator_not_dvd_cube_of_faulhaber` is the public certificate
endpoint.  It leaves only finite, exponent-local facts to callers and proves
the numerator nondivisibility required by Vandiver's second-case data.  The
exceptional `j = 2` channel, where `p` may divide the denominator of
`B_(2p-2)`, remains a separate calculation.
-/

namespace Fermat.Irregular.DirectBernoulli

open Fermat.Irregular.BernoulliData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

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

theorem pIntegral_of_denominatorPrimeTo {p : ℕ} {x : ℚ}
    (hx : DenominatorPrimeTo p x) : PIntegral p x := by
  rw [PIntegral, padicValRat_eq_numeratorVal hx]
  exact_mod_cast Nat.zero_le (padicValInt p x.num)

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
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
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
    (hp5 : 5 ≤ p) (n : ℕ) : PIntegral p ((p : ℚ) * bernoulli n) := by
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
        (by intro hp2; have := Nat.le_of_dvd (by norm_num : 0 < 2) hp2; omega)
    · have hn1 : 1 < n := by
        have hn0 : n ≠ 0 := by
          intro hzero
          subst n
          norm_num at hodd
        omega
      rw [bernoulli_eq_zero_of_odd hodd hn1, mul_zero]
      exact pIntegral_zero p

def faulhaberTerm (p n i : ℕ) : ℚ :=
  bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / (n + 1)

def lowQuotient (p n i : ℕ) : ℚ :=
  ((p : ℚ) * bernoulli i) * ((n + 1).choose i : ℚ) *
    (p : ℚ) ^ (n - 4 - i) / (n + 1)

theorem pIntegral_lowQuotient {p n i : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hden : ¬p ∣ n + 1) : PIntegral p (lowQuotient p n i) := by
  unfold lowQuotient
  have hnum : PIntegral p
      (((p : ℚ) * bernoulli i) * ((n + 1).choose i : ℚ) *
        (p : ℚ) ^ (n - 4 - i)) := by
    apply pIntegral_mul
    · exact pIntegral_mul (pIntegral_prime_mul_bernoulli hp5 i)
        (pIntegral_nat p ((n + 1).choose i))
    · simpa only [Nat.cast_pow] using pIntegral_nat p (p ^ (n - 4 - i))
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
      (p : ℚ) ^ 4 * ∑ i ∈ Finset.range (n - 3), lowQuotient p n i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact faulhaberTerm_eq_pow_four_mul_lowQuotient hn (Finset.mem_range.mp hi)

theorem pIntegral_lowQuotient_sum {p n : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hden : ¬p ∣ n + 1) :
    PIntegral p (∑ i ∈ Finset.range (n - 3), lowQuotient p n i) := by
  exact pIntegral_sum fun i _ ↦ pIntegral_lowQuotient hp5 hden

def topQuotient (n c : ℕ) : ℚ :=
  bernoulli (n - 2) * (c : ℚ) / (n + 1)

theorem pIntegral_topQuotient {p n c : ℕ} [Fact p.Prime]
    (hden : ¬p ∣ n + 1) (hprev : PIntegral p (bernoulli (n - 2))) :
    PIntegral p (topQuotient n c) := by
  unfold topQuotient
  have hnum : PIntegral p (bernoulli (n - 2) * (c : ℚ)) :=
    pIntegral_mul hprev (pIntegral_nat p c)
  simpa only [Nat.cast_add, Nat.cast_one] using
    pIntegral_div_nat (d := n + 1) hnum (by omega) hden

theorem faulhaberTerm_top_eq {p n c : ℕ} (hn : 4 ≤ n)
    (hchoose : (n + 1).choose (n - 2) = p * c) :
    faulhaberTerm p n (n - 2) = (p : ℚ) ^ 4 * topQuotient n c := by
  rw [faulhaberTerm, topQuotient, hchoose]
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
    (hi : Odd i) (hi1 : 1 < i) : faulhaberTerm p n i = 0 := by
  rw [faulhaberTerm, bernoulli_eq_zero_of_odd hi hi1]
  ring

theorem faulhaber_decomposition {p n c : ℕ}
    (hn : 6 ≤ n) (heven : Even n)
    (hchoose : (n + 1).choose (n - 2) = p * c) :
    (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
      (p : ℚ) ^ 4 *
          ((∑ i ∈ Finset.range (n - 3), lowQuotient p n i) + topQuotient n c) +
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
    have h := Finset.sum_range_succ (f := fun i ↦ faulhaberTerm p n i) (n - 2)
    have heq : n - 2 + 1 = n - 1 := by omega
    simpa only [heq] using h
  have hsplit3 :
      (∑ i ∈ Finset.range (n - 2), faulhaberTerm p n i) =
        (∑ i ∈ Finset.range (n - 3), faulhaberTerm p n i) +
          faulhaberTerm p n (n - 3) := by
    have h := Finset.sum_range_succ (f := fun i ↦ faulhaberTerm p n i) (n - 3)
    have heq : n - 3 + 1 = n - 2 := by omega
    simpa only [heq] using h
  rw [hfaulhaber, Finset.sum_range_succ,
    hsplit1, hsplit2, hsplit3,
    lowRemainder_eq (by omega : 4 ≤ n),
    faulhaberTerm_odd_eq_zero hodd3 (by omega),
    faulhaberTerm_top_eq (by omega : 4 ≤ n) hchoose,
    faulhaberTerm_odd_eq_zero hodd1 (by omega),
    faulhaberTerm_last_eq]
  ring

def powerSumInt (p n : ℕ) : ℤ :=
  ∑ a ∈ Finset.range p, (a : ℤ) ^ n

theorem powerSumRat_eq {p n r : ℕ} [Fact p.Prime]
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * r) :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range p, (a : ℚ) ^ n) =
        p * (r : ℚ) + (p : ℚ) ^ 4 * (t : ℚ) := by
  have hcast :
      ((powerSumInt p n - p * r : ℤ) : ZMod (p ^ 4)) = 0 := by
    rw [Int.cast_sub]
    have hsum :
        (powerSumInt p n : ZMod (p ^ 4)) =
          ∑ a ∈ Finset.range p, (a : ZMod (p ^ 4)) ^ n := by
      simp [powerSumInt]
    rw [hsum, hmod]
    push_cast
    ring
  have hdvd : ((p ^ 4 : ℕ) : ℤ) ∣ powerSumInt p n - p * r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  have ht' : powerSumInt p n = p * r + (p : ℤ) ^ 4 * t := by
    push_cast at ht ⊢
    omega
  have htRat := congrArg (fun z : ℤ ↦ (z : ℚ)) ht'
  push_cast at htRat
  simpa [powerSumInt] using htRat

/-- A finite power-sum residue and the top binomial quotient determine
`B_n` modulo `p^3`. -/
theorem bernoulli_representation_of_faulhaber
    {p n c r : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 6 ≤ n) (heven : Even n)
    (hden : ¬p ∣ n + 1)
    (hprev : PIntegral p (bernoulli (n - 2)))
    (hchoose : (n + 1).choose (n - 2) = p * c)
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * r) :
    ∃ u : ℚ, PIntegral p u ∧
      bernoulli n = (r : ℚ) + (p : ℚ) ^ 3 * u := by
  obtain ⟨t, ht⟩ := powerSumRat_eq hmod
  have hdecomp := faulhaber_decomposition hn heven hchoose
  rw [hdecomp] at ht
  let remainder : ℚ :=
    (∑ i ∈ Finset.range (n - 3), lowQuotient p n i) +
      topQuotient n c
  have hrem : PIntegral p remainder := by
    apply pIntegral_add
    · exact pIntegral_lowQuotient_sum hp5 hden
    · exact pIntegral_topQuotient hden hprev
  refine ⟨(t : ℚ) - remainder,
    pIntegral_sub (pIntegral_int p t) hrem, ?_⟩
  change (p : ℚ) ^ 4 * remainder + p * bernoulli n =
    p * (r : ℚ) + (p : ℚ) ^ 4 * (t : ℚ) at ht
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcanceled :
      (p : ℚ) ^ 3 * remainder + bernoulli n =
        (r : ℚ) + (p : ℚ) ^ 3 * (t : ℚ) := by
    apply mul_left_cancel₀ hp0
    calc
      (p : ℚ) * ((p : ℚ) ^ 3 * remainder + bernoulli n) =
          (p : ℚ) ^ 4 * remainder + p * bernoulli n := by ring
      _ = p * (r : ℚ) + (p : ℚ) ^ 4 * (t : ℚ) := ht
      _ = (p : ℚ) * ((r : ℚ) + (p : ℚ) ^ 3 * (t : ℚ)) := by ring
  linear_combination hcanceled

theorem padicValRat_prime_cube {p : ℕ} [Fact p.Prime] :
    padicValRat p ((p : ℚ) ^ 3) = 3 := by
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValRat.pow hp0, padicValRat.of_nat, padicValNat_self]
  norm_num

theorem representation_ne_zero_and_padicValRat_eq
    {p r : ℕ} [Fact p.Prime] {x u : ℚ}
    (hr0 : r ≠ 0) (hu : PIntegral p u)
    (hx : x = (r : ℚ) + (p : ℚ) ^ 3 * u)
    (hrlt : padicValRat p (r : ℚ) < 3) :
    x ≠ 0 ∧ padicValRat p x = padicValRat p (r : ℚ) := by
  have hrq0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  by_cases hu0 : u = 0
  · rw [hx, hu0, mul_zero, add_zero]
    exact ⟨hrq0, rfl⟩
  · have hpow0 : (p : ℚ) ^ 3 ≠ 0 := by
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hrem0 : (p : ℚ) ^ 3 * u ≠ 0 := mul_ne_zero hpow0 hu0
    have hremval : 3 ≤ padicValRat p ((p : ℚ) ^ 3 * u) := by
      change 0 ≤ padicValRat p u at hu
      rw [padicValRat.mul hpow0 hu0, padicValRat_prime_cube]
      omega
    have hlt :
        padicValRat p (r : ℚ) <
          padicValRat p ((p : ℚ) ^ 3 * u) := hrlt.trans_le hremval
    have hsum0 : (r : ℚ) + (p : ℚ) ^ 3 * u ≠ 0 := by
      intro hzero
      have heq : (r : ℚ) = -((p : ℚ) ^ 3 * u) := by linarith
      have hvals := congrArg (padicValRat p) heq
      rw [padicValRat.neg] at hvals
      omega
    rw [hx]
    exact ⟨hsum0, padicValRat.add_eq_of_lt hsum0 hrq0 hrem0 hlt⟩

/-- A `p^3`-accurate integral representation with a nonzero residue modulo
`p^3` proves the numerator condition required by Vandiver's finite channel. -/
theorem numerator_not_dvd_cube_of_representation
    {p r : ℕ} [Fact p.Prime] {x u : ℚ}
    (hr0 : r ≠ 0) (hrcube : ¬(p : ℤ) ^ 3 ∣ (r : ℤ))
    (hden : DenominatorPrimeTo p x) (hu : PIntegral p u)
    (hx : x = (r : ℚ) + (p : ℚ) ^ 3 * u) :
    ¬(p : ℤ) ^ 3 ∣ x.num := by
  have hrq0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have hdenr : DenominatorPrimeTo p (r : ℚ) := by
    simp [DenominatorPrimeTo, (Fact.out : p.Prime).ne_one]
  have hrlt : padicValRat p (r : ℚ) < 3 := by
    by_contra hnotlt
    have hle : (3 : ℤ) ≤ padicValRat p (r : ℚ) := by omega
    have hdvd :=
      (numerator_pow_dvd_iff_le_padicValRat (p := p) (n := 3)
        hrq0 hdenr).mpr hle
    apply hrcube
    simpa using hdvd
  obtain ⟨hx0, hval⟩ :=
    representation_ne_zero_and_padicValRat_eq hr0 hu hx hrlt
  apply numerator_not_dvd_pow_of_padicValRat_lt hx0 hden
  rw [hval]
  exact hrlt

/-- The reusable regular-`j` Faulhaber endpoint.  All exponent-specific
work is reduced to the finite power-sum residue, the top choose quotient,
the preceding Bernoulli denominator check, and the nonzero residue. -/
theorem bernoulli_numerator_not_dvd_cube_of_faulhaber
    {p n c r : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 6 ≤ n) (heven : Even n)
    (hdenNext : ¬p ∣ n + 1)
    (hprev : PIntegral p (bernoulli (n - 2)))
    (hchoose : (n + 1).choose (n - 2) = p * c)
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * r)
    (hr0 : r ≠ 0) (hrcube : ¬(p : ℤ) ^ 3 ∣ (r : ℤ))
    (htarget : DenominatorPrimeTo p (bernoulli n)) :
    ¬(p : ℤ) ^ 3 ∣ (bernoulli n).num := by
  obtain ⟨u, hu, hB⟩ := bernoulli_representation_of_faulhaber
    hp5 hn heven hdenNext hprev hchoose hmod
  exact numerator_not_dvd_cube_of_representation hr0 hrcube htarget hu hB

end Fermat.Irregular.DirectBernoulli
