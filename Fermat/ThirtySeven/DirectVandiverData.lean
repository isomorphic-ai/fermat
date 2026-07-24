import Fermat.Irregular.VandiverData

/-!
# Direct Vandiver Bernoulli data for exponent thirty-seven

This module proves every Bernoulli-numerator condition in Vandiver's
second-case criterion for `p = 37` directly from finite power sums.  It does
not assume Kummer's congruence.

For `n = 37 * j` with even `4 ≤ j ≤ 34`, Faulhaber's formula modulo
`37 ^ 4` determines `B_n` modulo `37 ^ 3`; von Staudt--Clausen controls the
discarded denominators.  The case `j = 2` is exceptional because the nearby
number `B_72` has a denominator divisible by `37`.  We first determine
`37 * B_72` modulo `37`, then retain its contribution in the calculation of
`B_74`.
-/

namespace Fermat.ThirtySeven.DirectVandiverData

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

private def PIntegral (x : ℚ) : Prop :=
  0 ≤ padicValRat 37 x

private theorem pIntegral_zero : PIntegral 0 := by
  simp [PIntegral]

private theorem pIntegral_nat (n : ℕ) : PIntegral (n : ℚ) := by
  simp only [PIntegral, padicValRat.of_nat]
  exact_mod_cast Nat.zero_le (padicValNat 37 n)

private theorem pIntegral_int (z : ℤ) : PIntegral (z : ℚ) := by
  simp only [PIntegral, padicValRat.of_int]
  exact_mod_cast Nat.zero_le (padicValInt 37 z)

private theorem pIntegral_neg {x : ℚ} (hx : PIntegral x) : PIntegral (-x) := by
  simpa only [PIntegral, padicValRat.neg] using hx

private theorem pIntegral_add {x y : ℚ}
    (hx : PIntegral x) (hy : PIntegral y) : PIntegral (x + y) := by
  by_cases hxy : x + y = 0
  · simpa [hxy] using pIntegral_zero
  · exact (le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy)

private theorem pIntegral_sub {x y : ℚ}
    (hx : PIntegral x) (hy : PIntegral y) : PIntegral (x - y) := by
  rw [sub_eq_add_neg]
  exact pIntegral_add hx (pIntegral_neg hy)

private theorem pIntegral_mul {x y : ℚ}
    (hx : PIntegral x) (hy : PIntegral y) : PIntegral (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0, PIntegral]
  by_cases hy0 : y = 0
  · simp [hy0, PIntegral]
  change 0 ≤ padicValRat 37 x at hx
  change 0 ≤ padicValRat 37 y at hy
  rw [PIntegral, padicValRat.mul hx0 hy0]
  exact add_nonneg hx hy

private theorem pIntegral_sum {s : Finset ℕ} {f : ℕ → ℚ}
    (hf : ∀ i ∈ s, PIntegral (f i)) : PIntegral (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [pIntegral_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact pIntegral_add (hf a (by simp)) (ih fun i hi ↦ hf i (by simp [hi]))

private theorem pIntegral_of_denominatorPrimeTo {x : ℚ}
    (hx : DenominatorPrimeTo 37 x) : PIntegral x := by
  rw [PIntegral, padicValRat_eq_numeratorVal hx]
  exact_mod_cast Nat.zero_le (padicValInt 37 x.num)

private theorem pIntegral_div_nat {x : ℚ} {d : ℕ}
    (hx : PIntegral x) (hd0 : d ≠ 0) (hd : ¬37 ∣ d) : PIntegral (x / (d : ℚ)) := by
  by_cases hx0 : x = 0
  · simp [hx0, PIntegral]
  rw [PIntegral, padicValRat.div hx0 (Nat.cast_ne_zero.mpr hd0),
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
  simpa [PIntegral] using hx

private theorem pIntegral_thirtySeven_div_prime {q : ℕ} (hq : q.Prime) :
    PIntegral ((37 : ℚ) / q) := by
  by_cases hq37 : q = 37
  · subst q
    norm_num [PIntegral]
  · have hnot : ¬37 ∣ q := by
      intro hdvd
      rcases (Nat.dvd_prime hq).mp hdvd with h | h
      · norm_num at h
      · exact hq37 h.symm
    have h37 : (37 : ℚ) ≠ 0 := by norm_num
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    rw [PIntegral, padicValRat.div h37 hq0]
    have hval37 : padicValRat 37 (37 : ℚ) = 1 := by
      norm_num [padicValRat_def, padicValInt, padicValNat]
    rw [hval37, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hnot]
    norm_num

/-- Von Staudt--Clausen in the uniform form used below: multiplying any
Bernoulli number by `37` clears its possible `37`-denominator. -/
private theorem pIntegral_thirtySeven_mul_bernoulli_even (k : ℕ) :
    PIntegral ((37 : ℚ) * bernoulli (2 * k)) := by
  let primes :=
    (Finset.range (2 * k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k
  let correction : ℚ := ∑ q ∈ primes, (1 : ℚ) / q
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hz' : bernoulli (2 * k) + correction = (z : ℚ) := by
    simpa [primes, correction] using hz.symm
  have hcorrection : PIntegral ((37 : ℚ) * correction) := by
    rw [Finset.mul_sum]
    apply pIntegral_sum
    intro q hq
    have hq' : q.Prime ∧ (q - 1) ∣ 2 * k := by
      change q ∈ (Finset.range (2 * k + 2)).filter
        (fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k) at hq
      exact (Finset.mem_filter.mp hq).2
    simpa [div_eq_mul_inv, mul_assoc] using
      pIntegral_thirtySeven_div_prime hq'.1
  have hscaled : (37 : ℚ) * bernoulli (2 * k) =
      (37 : ℚ) * (z : ℚ) - 37 * correction := by
    rw [← hz']
    ring
  rw [hscaled]
  exact pIntegral_sub (pIntegral_mul (pIntegral_nat 37) (pIntegral_int z)) hcorrection

private theorem pIntegral_thirtySeven_mul_bernoulli (n : ℕ) :
    PIntegral ((37 : ℚ) * bernoulli n) := by
  rcases n.even_or_odd with heven | hodd
  · obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp heven
    exact pIntegral_thirtySeven_mul_bernoulli_even k
  · by_cases hn : n = 1
    · subst n
      rw [bernoulli_one]
      have heq : (37 : ℚ) * (-1 / 2) = -(37 : ℚ) / 2 := by ring
      rw [heq]
      exact pIntegral_div_nat (x := -(37 : ℚ)) (d := 2)
        (pIntegral_neg (pIntegral_nat 37)) (by norm_num) (by norm_num)
    · have hn1 : 1 < n := by
        have hn0 : n ≠ 0 := by
          intro hzero
          subst n
          norm_num at hodd
        omega
      rw [bernoulli_eq_zero_of_odd hodd hn1, mul_zero]
      exact pIntegral_zero

/-! ## Generic Faulhaber certificates -/

private def faulhaberTerm (n i : ℕ) : ℚ :=
  bernoulli i * ((n + 1).choose i : ℚ) * (37 : ℚ) ^ (n + 1 - i) / (n + 1)

private def lowQuotient (n i : ℕ) : ℚ :=
  ((37 : ℚ) * bernoulli i) * ((n + 1).choose i : ℚ) *
    (37 : ℚ) ^ (n - 4 - i) / (n + 1)

private theorem pIntegral_lowQuotient {n i : ℕ}
    (hden : ¬37 ∣ n + 1) : PIntegral (lowQuotient n i) := by
  unfold lowQuotient
  have hnum : PIntegral
      (((37 : ℚ) * bernoulli i) * ((n + 1).choose i : ℚ) *
        (37 : ℚ) ^ (n - 4 - i)) := by
    apply pIntegral_mul
    · exact pIntegral_mul (pIntegral_thirtySeven_mul_bernoulli i)
        (pIntegral_nat ((n + 1).choose i))
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        pIntegral_nat (37 ^ (n - 4 - i))
  simpa only [Nat.cast_add, Nat.cast_one] using
    pIntegral_div_nat (d := n + 1) hnum (by omega) hden

private theorem faulhaberTerm_eq_pow_four_mul_lowQuotient {n i : ℕ}
    (hn : 4 ≤ n) (hi : i < n - 3) :
    faulhaberTerm n i = (37 : ℚ) ^ 4 * lowQuotient n i := by
  have hexp : n + 1 - i = 4 + 1 + (n - 4 - i) := by omega
  rw [faulhaberTerm, lowQuotient, hexp, pow_add, pow_add]
  ring

private theorem lowRemainder_eq {n : ℕ} (hn : 4 ≤ n) :
    (∑ i ∈ Finset.range (n - 3), faulhaberTerm n i) =
      (37 : ℚ) ^ 4 * ∑ i ∈ Finset.range (n - 3), lowQuotient n i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact faulhaberTerm_eq_pow_four_mul_lowQuotient hn (Finset.mem_range.mp hi)

private theorem pIntegral_lowQuotient_sum {n : ℕ}
    (hden : ¬37 ∣ n + 1) :
    PIntegral (∑ i ∈ Finset.range (n - 3), lowQuotient n i) := by
  exact pIntegral_sum fun i _ ↦ pIntegral_lowQuotient hden

private def topQuotient (n c : ℕ) : ℚ :=
  bernoulli (n - 2) * (c : ℚ) / (n + 1)

private theorem pIntegral_topQuotient {n c : ℕ}
    (hden : ¬37 ∣ n + 1) (hprev : PIntegral (bernoulli (n - 2))) :
    PIntegral (topQuotient n c) := by
  unfold topQuotient
  have hnum : PIntegral (bernoulli (n - 2) * (c : ℚ)) :=
    pIntegral_mul hprev (pIntegral_nat c)
  simpa only [Nat.cast_add, Nat.cast_one] using
    pIntegral_div_nat (d := n + 1) hnum (by omega) hden

private theorem faulhaberTerm_top_eq {n c : ℕ} (hn : 4 ≤ n)
    (hchoose : (n + 1).choose (n - 2) = 37 * c) :
    faulhaberTerm n (n - 2) = (37 : ℚ) ^ 4 * topQuotient n c := by
  rw [faulhaberTerm, topQuotient, hchoose]
  have hexp : n + 1 - (n - 2) = 3 := by omega
  rw [hexp]
  push_cast
  ring

private theorem faulhaberTerm_last_eq {n : ℕ} :
    faulhaberTerm n n = (37 : ℚ) * bernoulli n := by
  rw [faulhaberTerm, Nat.choose_succ_self_right]
  have hexp : n + 1 - n = 1 := by omega
  rw [hexp, pow_one]
  field_simp
  push_cast
  rfl

private theorem faulhaberTerm_odd_eq_zero {n i : ℕ}
    (hi : Odd i) (hi1 : 1 < i) : faulhaberTerm n i = 0 := by
  rw [faulhaberTerm, bernoulli_eq_zero_of_odd hi hi1]
  ring

private theorem faulhaber_decomposition {n c : ℕ}
    (hn : 6 ≤ n) (heven : Even n)
    (hchoose : (n + 1).choose (n - 2) = 37 * c) :
    (∑ a ∈ Finset.range 37, (a : ℚ) ^ n) =
      (37 : ℚ) ^ 4 *
          ((∑ i ∈ Finset.range (n - 3), lowQuotient n i) + topQuotient n c) +
        37 * bernoulli n := by
  have hfaulhaber :
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ n) =
        ∑ i ∈ Finset.range (n + 1), faulhaberTerm n i := by
    simpa [faulhaberTerm] using sum_range_pow 37 n
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp heven
  have hodd3 : Odd (n - 3) := by
    refine ⟨k - 2, ?_⟩
    omega
  have hodd1 : Odd (n - 1) := by
    refine ⟨k - 1, ?_⟩
    omega
  have hsplit1 :
      (∑ i ∈ Finset.range n, faulhaberTerm n i) =
        (∑ i ∈ Finset.range (n - 1), faulhaberTerm n i) +
          faulhaberTerm n (n - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      (Finset.sum_range_succ (f := fun i ↦ faulhaberTerm n i) (n - 1))
  have hsplit2 :
      (∑ i ∈ Finset.range (n - 1), faulhaberTerm n i) =
        (∑ i ∈ Finset.range (n - 2), faulhaberTerm n i) +
          faulhaberTerm n (n - 2) := by
    have h := Finset.sum_range_succ (f := fun i ↦ faulhaberTerm n i) (n - 2)
    have heq : n - 2 + 1 = n - 1 := by omega
    simpa only [heq] using h
  have hsplit3 :
      (∑ i ∈ Finset.range (n - 2), faulhaberTerm n i) =
        (∑ i ∈ Finset.range (n - 3), faulhaberTerm n i) +
          faulhaberTerm n (n - 3) := by
    have h := Finset.sum_range_succ (f := fun i ↦ faulhaberTerm n i) (n - 3)
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

private def powerSumInt (n : ℕ) : ℤ :=
  ∑ a ∈ Finset.range 37, (a : ℤ) ^ n

private theorem powerSumRat_eq {n r : ℕ}
    (hmod : (∑ a ∈ Finset.range 37,
      (a : ZMod (37 ^ 4)) ^ n) = 37 * r) :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ n) =
        37 * (r : ℚ) + (37 : ℚ) ^ 4 * (t : ℚ) := by
  have hcast :
      ((powerSumInt n - 37 * r : ℤ) : ZMod (37 ^ 4)) = 0 := by
    rw [Int.cast_sub]
    have hsum :
        (powerSumInt n : ZMod (37 ^ 4)) =
          ∑ a ∈ Finset.range 37, (a : ZMod (37 ^ 4)) ^ n := by
      simp [powerSumInt]
    rw [hsum, hmod]
    push_cast
    ring
  have hdvd : ((37 ^ 4 : ℕ) : ℤ) ∣ powerSumInt n - 37 * r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  have ht' : powerSumInt n = 37 * r + (37 : ℤ) ^ 4 * t := by
    norm_num at ht ⊢
    omega
  have htRat := congrArg (fun z : ℤ ↦ (z : ℚ)) ht'
  push_cast at htRat
  rw [show (37 : ℚ) ^ 4 = 1874161 by norm_num]
  simpa [powerSumInt] using htRat

/-! ## The finite residue table -/

private def powerSumQuotient : ℕ → ℕ
  | 4 => 30710
  | 6 => 25197
  | 8 => 11544
  | 10 => 9731
  | 12 => 17057
  | 14 => 9398
  | 16 => 41884
  | 18 => 2516
  | 20 => 41625
  | 22 => 27935
  | 24 => 11581
  | 26 => 18241
  | 28 => 29822
  | 30 => 37037
  | 32 => 2738
  | 34 => 2812
  | _ => 0

private def topCoefficient : ℕ → ℕ
  | 4 => 14602
  | 6 => 49283
  | 8 => 116820
  | 10 => 228165
  | 12 => 394270
  | 14 => 626087
  | 16 => 934568
  | 18 => 1330665
  | 20 => 1825330
  | 22 => 2429515
  | 24 => 3154172
  | 26 => 4010253
  | 28 => 5008710
  | 30 => 6160495
  | 32 => 7476560
  | 34 => 8967857
  | _ => 0

private theorem powerSum_mod_table {j : ℕ}
    (hj4 : 4 ≤ j) (hj34 : j ≤ 34) (heven : Even j) :
    (∑ a ∈ Finset.range 37,
      (a : ZMod (37 ^ 4)) ^ (j * 37)) = 37 * powerSumQuotient j := by
  interval_cases j <;> norm_num at heven
  all_goals decide

private theorem choose_top_table {j : ℕ}
    (hj4 : 4 ≤ j) (hj34 : j ≤ 34) (heven : Even j) :
    (j * 37 + 1).choose (j * 37 - 2) = 37 * topCoefficient j := by
  have hle : j * 37 - 2 ≤ j * 37 + 1 := by omega
  rw [← Nat.choose_symm hle]
  have hsub : j * 37 + 1 - (j * 37 - 2) = 3 := by omega
  rw [hsub]
  interval_cases j <;> norm_num at heven
  all_goals norm_num [topCoefficient, Nat.choose]

private theorem regular_index_representation {j : ℕ}
    (hj4 : 4 ≤ j) (hj34 : j ≤ 34) (heven : Even j) :
    ∃ u : ℚ, PIntegral u ∧
      bernoulli (j * 37) =
        (powerSumQuotient j : ℚ) + (37 : ℚ) ^ 3 * u := by
  have hn6 : 6 ≤ j * 37 := by omega
  have hneven : Even (j * 37) := heven.mul_right 37
  have hdenNext : ¬37 ∣ j * 37 + 1 := by
    intro hdvd
    obtain ⟨d, hd⟩ := hdvd
    omega
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp heven
  have hevenPrev : Even (j * 37 - 2) := by
    refine ⟨37 * k - 1, ?_⟩
    omega
  have hnotPrev : ¬36 ∣ j * 37 - 2 := by
    intro hdvd
    obtain ⟨d, hd⟩ := hdvd
    omega
  have hdenPrev : DenominatorPrimeTo 37 (bernoulli (j * 37 - 2)) :=
    bernoulli_denominatorPrimeTo hevenPrev hnotPrev
  have hprev : PIntegral (bernoulli (j * 37 - 2)) :=
    pIntegral_of_denominatorPrimeTo hdenPrev
  have hchoose :
      (j * 37 + 1).choose (j * 37 - 2) = 37 * topCoefficient j :=
    choose_top_table hj4 hj34 heven
  have hmod := powerSum_mod_table hj4 hj34 heven
  obtain ⟨t, ht⟩ := powerSumRat_eq hmod
  have hdecomp := faulhaber_decomposition hn6 hneven hchoose
  rw [hdecomp] at ht
  let remainder : ℚ :=
    (∑ i ∈ Finset.range (j * 37 - 3), lowQuotient (j * 37) i) +
      topQuotient (j * 37) (topCoefficient j)
  have hrem : PIntegral remainder := by
    apply pIntegral_add
    · exact pIntegral_lowQuotient_sum hdenNext
    · exact pIntegral_topQuotient hdenNext hprev
  refine ⟨(t : ℚ) - remainder, pIntegral_sub (pIntegral_int t) hrem, ?_⟩
  change (37 : ℚ) ^ 4 * remainder + 37 * bernoulli (j * 37) =
    37 * (powerSumQuotient j : ℚ) + (37 : ℚ) ^ 4 * (t : ℚ) at ht
  linarith

/-! ## The exceptional adjacent number `B_72` -/

private def quotient72 (i : ℕ) : ℚ :=
  ((37 : ℚ) * bernoulli i) * ((73).choose i : ℚ) *
    (37 : ℚ) ^ (71 - i) / 73

private theorem pIntegral_quotient72 (i : ℕ) : PIntegral (quotient72 i) := by
  unfold quotient72
  apply pIntegral_div_nat
  · apply pIntegral_mul
    · exact pIntegral_mul (pIntegral_thirtySeven_mul_bernoulli i)
        (pIntegral_nat ((73).choose i))
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        pIntegral_nat (37 ^ (71 - i))
  · norm_num
  · norm_num

private theorem faulhaberTerm72_eq {i : ℕ} (hi : i < 72) :
    faulhaberTerm 72 i = (37 : ℚ) * quotient72 i := by
  have hexp : 73 - i = 1 + 1 + (71 - i) := by omega
  rw [faulhaberTerm, quotient72]
  norm_num only [Nat.reduceAdd]
  rw [hexp, pow_add, pow_add]
  ring

private theorem faulhaber72_decomposition :
    (∑ a ∈ Finset.range 37, (a : ℚ) ^ 72) =
      (37 : ℚ) *
        ((∑ i ∈ Finset.range 72, quotient72 i) + bernoulli 72) := by
  have hfaulhaber :
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ 72) =
        ∑ i ∈ Finset.range 73, faulhaberTerm 72 i := by
    simpa [faulhaberTerm] using sum_range_pow 37 72
  rw [hfaulhaber, show 73 = 72 + 1 by norm_num, Finset.sum_range_succ,
    faulhaberTerm_last_eq]
  have hlow :
      (∑ i ∈ Finset.range 72, faulhaberTerm 72 i) =
        (37 : ℚ) * ∑ i ∈ Finset.range 72, quotient72 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact faulhaberTerm72_eq (Finset.mem_range.mp hi)
  rw [hlow]
  ring

private theorem powerSum72Rat_eq :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ 72) =
        36 + 37 * (t : ℚ) := by
  have hmod :
      (∑ a ∈ Finset.range 37, (a : ZMod 37) ^ 72) = 36 := by
    decide
  have hcast : ((powerSumInt 72 - 36 : ℤ) : ZMod 37) = 0 := by
    rw [Int.cast_sub]
    have hsum :
        (powerSumInt 72 : ZMod 37) =
          ∑ a ∈ Finset.range 37, (a : ZMod 37) ^ 72 := by
      simp [powerSumInt]
    rw [hsum, hmod]
    decide
  have hdvd : (37 : ℤ) ∣ powerSumInt 72 - 36 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  have ht' : powerSumInt 72 = 36 + 37 * t := by omega
  have htRat := congrArg (fun z : ℤ ↦ (z : ℚ)) ht'
  push_cast at htRat
  simpa [powerSumInt] using htRat

/-- The exceptional denominator is handled in normalized form:
`37 * B_72 = -1 (mod 37)`. -/
private theorem thirtySeven_mul_bernoulli72_representation :
    ∃ u : ℚ, PIntegral u ∧
      (37 : ℚ) * bernoulli 72 = -1 + 37 * u := by
  obtain ⟨t, ht⟩ := powerSum72Rat_eq
  rw [faulhaber72_decomposition] at ht
  let remainder : ℚ := ∑ i ∈ Finset.range 72, quotient72 i
  have hrem : PIntegral remainder :=
    pIntegral_sum fun i _ ↦ pIntegral_quotient72 i
  refine ⟨1 + (t : ℚ) - remainder, ?_, ?_⟩
  · exact pIntegral_sub (pIntegral_add (pIntegral_nat 1) (pIntegral_int t)) hrem
  · change (37 : ℚ) * (remainder + bernoulli 72) = 36 + 37 * (t : ℚ) at ht
    linarith

/-! ## The exceptional target `B_74` -/

private def quotient74 : ℚ :=
  ((37 : ℚ) * bernoulli 72) * 1825 / 75

private theorem pIntegral_quotient74 : PIntegral quotient74 := by
  unfold quotient74
  apply pIntegral_div_nat
  · exact pIntegral_mul (pIntegral_thirtySeven_mul_bernoulli 72)
      (pIntegral_nat 1825)
  · norm_num
  · norm_num

private theorem choose_75_72 : (75).choose 72 = 37 * 1825 := by
  rw [← Nat.choose_symm (by norm_num : 72 ≤ 75)]
  norm_num [Nat.choose]

private theorem faulhaberTerm74_72_eq :
    faulhaberTerm 74 72 = (37 : ℚ) ^ 3 * quotient74 := by
  rw [faulhaberTerm, quotient74, choose_75_72]
  norm_num only [Nat.reduceAdd, Nat.reduceSubDiff, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

private theorem faulhaber74_decomposition :
    (∑ a ∈ Finset.range 37, (a : ℚ) ^ 74) =
      (37 : ℚ) ^ 4 *
          (∑ i ∈ Finset.range 71, lowQuotient 74 i) +
        (37 : ℚ) ^ 3 * quotient74 + 37 * bernoulli 74 := by
  have hfaulhaber :
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ 74) =
        ∑ i ∈ Finset.range 75, faulhaberTerm 74 i := by
    simpa [faulhaberTerm] using sum_range_pow 37 74
  rw [hfaulhaber,
    show 75 = 74 + 1 by norm_num, Finset.sum_range_succ,
    show 74 = 73 + 1 by norm_num, Finset.sum_range_succ,
    show 73 = 72 + 1 by norm_num, Finset.sum_range_succ,
    show 72 = 71 + 1 by norm_num, Finset.sum_range_succ,
    lowRemainder_eq (n := 74) (by norm_num),
    faulhaberTerm_odd_eq_zero (by decide : Odd 71) (by norm_num),
    faulhaberTerm74_72_eq,
    faulhaberTerm_odd_eq_zero (by decide : Odd 73) (by norm_num),
    faulhaberTerm_last_eq]
  ring

private theorem powerSum74Rat_eq :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ 74) =
        37 * 38110 + (37 : ℚ) ^ 4 * (t : ℚ) := by
  apply powerSumRat_eq
  decide

private theorem bernoulli74_representation :
    ∃ u : ℚ, PIntegral u ∧
      bernoulli 74 = 3885 + (37 : ℚ) ^ 3 * u := by
  obtain ⟨u72, hu72, h72⟩ := thirtySeven_mul_bernoulli72_representation
  let v : ℚ := u72 * 1825 / 75
  have hv : PIntegral v := by
    apply pIntegral_div_nat
    · exact pIntegral_mul hu72 (pIntegral_nat 1825)
    · norm_num
    · norm_num
  have hq : quotient74 = -(1825 : ℚ) / 75 + 37 * v := by
    rw [quotient74, h72]
    dsimp only [v]
    ring
  obtain ⟨t, ht⟩ := powerSum74Rat_eq
  rw [faulhaber74_decomposition, hq] at ht
  let low : ℚ := ∑ i ∈ Finset.range 71, lowQuotient 74 i
  have hlow : PIntegral low :=
    pIntegral_lowQuotient_sum (n := 74) (by norm_num)
  refine ⟨4 / 3 + (t : ℚ) - low - v, ?_, ?_⟩
  · apply pIntegral_sub
    · apply pIntegral_sub
      · exact pIntegral_add
          (pIntegral_div_nat (x := (4 : ℚ)) (d := 3)
            (pIntegral_nat 4) (by norm_num) (by norm_num))
          (pIntegral_int t)
      · exact hlow
    · exact hv
  · change (37 : ℚ) ^ 4 * low +
      (37 : ℚ) ^ 3 * (-(1825 : ℚ) / 75 + 37 * v) +
        37 * bernoulli 74 =
      37 * 38110 + (37 : ℚ) ^ 4 * (t : ℚ) at ht
    linarith

/-! ## From a residue representation to numerator nondivisibility -/

private theorem padicValRat_thirtySeven_cube :
    padicValRat 37 ((37 : ℚ) ^ 3) = 3 := by
  have h37 : (37 : ℚ) ≠ 0 := by norm_num
  have hval37 : padicValRat 37 (37 : ℚ) = 1 := by
    norm_num [padicValRat_def, padicValInt, padicValNat]
  rw [padicValRat.pow h37, hval37]
  norm_num

private theorem representation_ne_zero_and_padicValRat_eq
    {x u : ℚ} {r : ℕ} (hr0 : r ≠ 0) (hu : PIntegral u)
    (hx : x = (r : ℚ) + (37 : ℚ) ^ 3 * u)
    (hrlt : padicValRat 37 (r : ℚ) < 3) :
    x ≠ 0 ∧ padicValRat 37 x = padicValRat 37 (r : ℚ) := by
  have hq0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  by_cases hu0 : u = 0
  · rw [hx, hu0, mul_zero, add_zero]
    exact ⟨hq0, rfl⟩
  · have hpow0 : (37 : ℚ) ^ 3 ≠ 0 := by norm_num
    have hrem0 : (37 : ℚ) ^ 3 * u ≠ 0 := mul_ne_zero hpow0 hu0
    have hremval : 3 ≤ padicValRat 37 ((37 : ℚ) ^ 3 * u) := by
      change 0 ≤ padicValRat 37 u at hu
      rw [padicValRat.mul hpow0 hu0, padicValRat_thirtySeven_cube]
      omega
    have hlt :
        padicValRat 37 (r : ℚ) <
          padicValRat 37 ((37 : ℚ) ^ 3 * u) := hrlt.trans_le hremval
    have hsum0 : (r : ℚ) + (37 : ℚ) ^ 3 * u ≠ 0 := by
      intro hzero
      have heq : (r : ℚ) = -((37 : ℚ) ^ 3 * u) := by linarith
      have hvals := congrArg (padicValRat 37) heq
      rw [padicValRat.neg] at hvals
      omega
    rw [hx]
    exact ⟨hsum0, padicValRat.add_eq_of_lt hsum0 hq0 hrem0 hlt⟩

private theorem numerator_not_dvd_cube_of_representation
    {x u : ℚ} {r : ℕ} (hr0 : r ≠ 0)
    (hrcube : ¬(37 : ℤ) ^ 3 ∣ (r : ℤ))
    (hden : DenominatorPrimeTo 37 x) (hu : PIntegral u)
    (hx : x = (r : ℚ) + (37 : ℚ) ^ 3 * u) :
    ¬(37 : ℤ) ^ 3 ∣ x.num := by
  have hrq0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have hdenr : DenominatorPrimeTo 37 (r : ℚ) := by
    norm_num [DenominatorPrimeTo]
  have hrlt : padicValRat 37 (r : ℚ) < 3 := by
    by_contra hnotlt
    have hle : (3 : ℤ) ≤ padicValRat 37 (r : ℚ) := by omega
    have hdvd :=
      (numerator_pow_dvd_iff_le_padicValRat (p := 37) (n := 3) hrq0 hdenr).mpr hle
    apply hrcube
    simpa using hdvd
  obtain ⟨hx0, hval⟩ :=
    representation_ne_zero_and_padicValRat_eq hr0 hu hx hrlt
  apply numerator_not_dvd_pow_of_padicValRat_lt hx0 hden
  rw [hval]
  exact hrlt

private theorem powerSumQuotient_not_dvd_cube {j : ℕ}
    (hj4 : 4 ≤ j) (hj34 : j ≤ 34) (heven : Even j) :
    ¬(37 : ℤ) ^ 3 ∣ (powerSumQuotient j : ℤ) := by
  interval_cases j <;> norm_num [powerSumQuotient] at *

private theorem powerSumQuotient_ne_zero {j : ℕ}
    (hj4 : 4 ≤ j) (hj34 : j ≤ 34) (heven : Even j) :
    powerSumQuotient j ≠ 0 := by
  interval_cases j <;> norm_num [powerSumQuotient] at *

private theorem target_denominator_prime_to {j : ℕ}
    (hj2 : 2 ≤ j) (hj34 : j ≤ 34) (heven : Even j) :
    DenominatorPrimeTo 37 (bernoulli (j * 37)) := by
  apply bernoulli_denominatorPrimeTo (p := 37)
  · exact heven.mul_right 37
  · intro hdvd
    obtain ⟨d, hd⟩ := hdvd
    omega

private theorem bernoulli74_numerator_not_dvd_cube :
    ¬(37 : ℤ) ^ 3 ∣ (bernoulli 74).num := by
  obtain ⟨u, hu, hB⟩ := bernoulli74_representation
  apply numerator_not_dvd_cube_of_representation (r := 3885) (u := u)
  · norm_num
  · norm_num
  · apply bernoulli_denominatorPrimeTo (p := 37)
    · decide
    · norm_num
  · exact hu
  · exact hB

/-- Every Bernoulli-numerator condition in Vandiver's criterion at `37`,
proved directly by finite Faulhaber computations and without a Kummer
congruence hypothesis. -/
theorem bernoulliCubeCondition_thirtySeven_direct :
    BernoulliCubeCondition 37 := by
  intro j hj
  have hj' : 2 ≤ j ∧ j ≤ 34 ∧ Even j := by
    simpa [indices, and_assoc] using hj
  by_cases hj2eq : j = 2
  · subst j
    simpa using bernoulli74_numerator_not_dvd_cube
  · obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hj'.2.2
    have hj4 : 4 ≤ j := by omega
    obtain ⟨u, hu, hB⟩ :=
      regular_index_representation hj4 hj'.2.1 hj'.2.2
    apply numerator_not_dvd_cube_of_representation
      (r := powerSumQuotient j) (u := u)
    · exact powerSumQuotient_ne_zero hj4 hj'.2.1 hj'.2.2
    · exact powerSumQuotient_not_dvd_cube hj4 hj'.2.1 hj'.2.2
    · exact target_denominator_prime_to hj'.1 hj'.2.1 hj'.2.2
    · exact hu
    · exact hB

end Fermat.ThirtySeven.DirectVandiverData
