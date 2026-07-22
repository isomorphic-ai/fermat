import Fermat.Irregular.BernoulliData
import Fermat.Irregular.DirectBernoulli

/-!
# The high Bernoulli certificate for exponent thirty-seven

Vandiver's second-case criterion at the unique irregular index for `37`
needs the fact that `37 ^ 3` does not divide the reduced numerator of
`B_1184`.  Computing that Bernoulli number outright would require hundreds of
large rational recurrence steps.  This module instead uses Faulhaber's
formula at `37`: the power sum modulo `37 ^ 4` determines `B_1184` modulo
`37 ^ 3`, while von Staudt--Clausen controls every denominator in the
discarded terms.
-/

namespace Fermat.ThirtySeven.HighBernoulli

open Fermat.Irregular.BernoulliData

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

/-! ## The discarded Faulhaber terms -/

private def faulhaberTerm (i : ℕ) : ℚ :=
  bernoulli i * ((1185).choose i : ℚ) * (37 : ℚ) ^ (1185 - i) / 1185

/-- After taking `37 ^ 4` out of the terms through index `1180`, one
factor of `37` remains beside the Bernoulli number.  Von Staudt--Clausen
says that this is integral at `37`. -/
private def lowQuotient (i : ℕ) : ℚ :=
  ((37 : ℚ) * bernoulli i) * ((1185).choose i : ℚ) *
    (37 : ℚ) ^ (1180 - i) / 1185

private theorem pIntegral_lowQuotient (i : ℕ) : PIntegral (lowQuotient i) := by
  unfold lowQuotient
  apply pIntegral_div_nat
  · apply pIntegral_mul
    · exact pIntegral_mul (pIntegral_thirtySeven_mul_bernoulli i)
        (pIntegral_nat ((1185).choose i))
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        pIntegral_nat (37 ^ (1180 - i))
  · norm_num
  · norm_num

private theorem faulhaberTerm_eq_pow_four_mul_lowQuotient {i : ℕ}
    (hi : i < 1181) :
    faulhaberTerm i = (37 : ℚ) ^ 4 * lowQuotient i := by
  have hexp : 1185 - i = 4 + 1 + (1180 - i) := by omega
  rw [faulhaberTerm, lowQuotient, hexp, pow_add, pow_add]
  ring

private theorem lowRemainder_eq :
    (∑ i ∈ Finset.range 1181, faulhaberTerm i) =
      (37 : ℚ) ^ 4 * ∑ i ∈ Finset.range 1181, lowQuotient i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact faulhaberTerm_eq_pow_four_mul_lowQuotient (Finset.mem_range.mp hi)

private theorem pIntegral_lowQuotient_sum :
    PIntegral (∑ i ∈ Finset.range 1181, lowQuotient i) := by
  exact pIntegral_sum fun i _ ↦ pIntegral_lowQuotient i

private theorem pIntegral_bernoulli_1182 : PIntegral (bernoulli 1182) := by
  apply pIntegral_of_denominatorPrimeTo
  apply bernoulli_denominatorPrimeTo (p := 37)
  · decide
  · norm_num

private def index1182Quotient : ℚ :=
  bernoulli 1182 * 7476560 / 1185

private theorem pIntegral_index1182Quotient : PIntegral index1182Quotient := by
  unfold index1182Quotient
  apply pIntegral_div_nat
  · exact pIntegral_mul pIntegral_bernoulli_1182 (pIntegral_nat 7476560)
  · norm_num
  · norm_num

private theorem choose_1185_1182 : (1185).choose 1182 = 37 * 7476560 := by
  rw [← Nat.choose_symm (by norm_num : 1182 ≤ 1185)]
  norm_num [Nat.choose]

private theorem faulhaberTerm_1182_eq :
    faulhaberTerm 1182 = (37 : ℚ) ^ 4 * index1182Quotient := by
  rw [faulhaberTerm, index1182Quotient, choose_1185_1182]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceSubDiff, pow_succ,
    pow_zero, mul_one]
  ring

private theorem faulhaberTerm_1181_eq_zero : faulhaberTerm 1181 = 0 := by
  rw [faulhaberTerm, bernoulli_eq_zero_of_odd (by decide) (by norm_num)]
  ring

private theorem faulhaberTerm_1183_eq_zero : faulhaberTerm 1183 = 0 := by
  rw [faulhaberTerm, bernoulli_eq_zero_of_odd (by decide) (by norm_num)]
  ring

private theorem faulhaberTerm_1184_eq :
    faulhaberTerm 1184 = (37 : ℚ) * bernoulli 1184 := by
  rw [faulhaberTerm, Nat.choose_succ_self_right]
  norm_num
  ring

/-! ## The power-sum certificate -/

private def powerSumInt : ℤ :=
  ∑ a ∈ Finset.range 37, (a : ℤ) ^ 1184

/-- This is the only large finite computation in the certificate.  It takes
place in the 32-bit ring `ZMod (37 ^ 4)`, rather than constructing the
roughly 2200-digit numerator of `B_1184`. -/
private theorem powerSum_mod_thirtySeven_pow_four :
    (∑ a ∈ Finset.range 37, (a : ZMod (37 ^ 4)) ^ 1184) = 101306 := by
  decide

private theorem powerSumInt_sub_dvd :
    ((37 : ℤ) ^ 4) ∣ powerSumInt - 101306 := by
  have hcast : ((powerSumInt - 101306 : ℤ) : ZMod (37 ^ 4)) = 0 := by
    rw [Int.cast_sub]
    have hsum :
        (powerSumInt : ZMod (37 ^ 4)) =
          ∑ a ∈ Finset.range 37, (a : ZMod (37 ^ 4)) ^ 1184 := by
      simp [powerSumInt]
    rw [hsum, powerSum_mod_thirtySeven_pow_four]
    decide
  have hdvd : ((37 ^ 4 : ℕ) : ℤ) ∣ powerSumInt - 101306 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  norm_num at hdvd ⊢
  exact hdvd

private theorem powerSumRat_eq :
    ∃ t : ℤ,
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ 1184) =
        2 * (37 : ℚ) ^ 3 + (37 : ℚ) ^ 4 * (t : ℚ) := by
  obtain ⟨t, ht⟩ := powerSumInt_sub_dvd
  refine ⟨t, ?_⟩
  have ht' : powerSumInt = 101306 + (37 : ℤ) ^ 4 * t := by omega
  have htRat := congrArg (fun z : ℤ ↦ (z : ℚ)) ht'
  norm_num at htRat ⊢
  simpa [powerSumInt] using htRat

private theorem faulhaber_decomposition :
    (∑ a ∈ Finset.range 37, (a : ℚ) ^ 1184) =
      (37 : ℚ) ^ 4 *
          ((∑ i ∈ Finset.range 1181, lowQuotient i) + index1182Quotient) +
        37 * bernoulli 1184 := by
  have hfaulhaber :
      (∑ a ∈ Finset.range 37, (a : ℚ) ^ 1184) =
        ∑ i ∈ Finset.range 1185, faulhaberTerm i := by
    have h := sum_range_pow 37 1184
    norm_num at h ⊢
    simpa [faulhaberTerm] using h
  rw [hfaulhaber]
  rw [show 1185 = 1184 + 1 by norm_num, Finset.sum_range_succ,
    show 1184 = 1183 + 1 by norm_num, Finset.sum_range_succ,
    show 1183 = 1182 + 1 by norm_num, Finset.sum_range_succ,
    show 1182 = 1181 + 1 by norm_num, Finset.sum_range_succ,
    lowRemainder_eq, faulhaberTerm_1181_eq_zero,
    faulhaberTerm_1182_eq, faulhaberTerm_1183_eq_zero,
    faulhaberTerm_1184_eq]
  ring

/-! ## The sharp `37`-adic conclusion -/

private def remainderQuotient : ℚ :=
  (∑ i ∈ Finset.range 1181, lowQuotient i) + index1182Quotient

private theorem pIntegral_remainderQuotient : PIntegral remainderQuotient := by
  exact pIntegral_add pIntegral_lowQuotient_sum pIntegral_index1182Quotient

/-- Faulhaber's identity and the finite power-sum computation give the
congruence `B_1184 = 2 * 37^2 (mod 37^3)`.  The witness is retained as a
rational known to be integral at `37`, so no illicit reduction of a rational
with a divisible denominator is hidden in the notation. -/
private theorem bernoulli_1184_eq_two_mul_sq_add_cube :
    ∃ u : ℚ, PIntegral u ∧
      bernoulli 1184 = 2 * (37 : ℚ) ^ 2 + (37 : ℚ) ^ 3 * u := by
  obtain ⟨t, ht⟩ := powerSumRat_eq
  refine ⟨(t : ℚ) - remainderQuotient, ?_, ?_⟩
  · exact pIntegral_sub (pIntegral_int t) pIntegral_remainderQuotient
  · rw [faulhaber_decomposition] at ht
    change (37 : ℚ) ^ 4 * remainderQuotient + 37 * bernoulli 1184 =
      2 * (37 : ℚ) ^ 3 + (37 : ℚ) ^ 4 * (t : ℚ) at ht
    linarith

private theorem padicValRat_two_mul_thirtySeven_sq :
    padicValRat 37 (2 * (37 : ℚ) ^ 2) = 2 := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have h37 : (37 : ℚ) ≠ 0 := by norm_num
  have hval2 : padicValRat 37 (2 : ℚ) = 0 := by
    exact padicValRat_eq_zero_of_numerator_not_dvd
      (by norm_num [DenominatorPrimeTo]) (by norm_num)
  have hval37 : padicValRat 37 (37 : ℚ) = 1 := by
    norm_num [padicValRat_def, padicValInt, padicValNat]
  rw [padicValRat.mul h2 (pow_ne_zero 2 h37), hval2,
    padicValRat.pow h37, hval37]
  norm_num

private theorem padicValRat_thirtySeven_cube :
    padicValRat 37 ((37 : ℚ) ^ 3) = 3 := by
  have h37 : (37 : ℚ) ≠ 0 := by norm_num
  have hval37 : padicValRat 37 (37 : ℚ) = 1 := by
    norm_num [padicValRat_def, padicValInt, padicValNat]
  rw [padicValRat.pow h37, hval37]
  norm_num

/-- The package's high Bernoulli certificate, proved without expanding the
2190-digit reduced numerator: `B_1184` has exactly two factors of `37`. -/
theorem bernoulli_1184_padicValRat :
    padicValRat 37 (bernoulli 1184) = 2 := by
  obtain ⟨u, hu, hB⟩ := bernoulli_1184_eq_two_mul_sq_add_cube
  by_cases hu0 : u = 0
  · rw [hB, hu0, mul_zero, add_zero]
    exact padicValRat_two_mul_thirtySeven_sq
  · have hpow0 : (37 : ℚ) ^ 3 ≠ 0 := by norm_num
    have hr0 : (37 : ℚ) ^ 3 * u ≠ 0 := mul_ne_zero hpow0 hu0
    have hq0 : 2 * (37 : ℚ) ^ 2 ≠ 0 := by norm_num
    have hrval : 3 ≤ padicValRat 37 ((37 : ℚ) ^ 3 * u) := by
      change 0 ≤ padicValRat 37 u at hu
      rw [padicValRat.mul hpow0 hu0, padicValRat_thirtySeven_cube]
      omega
    have hlt :
        padicValRat 37 (2 * (37 : ℚ) ^ 2) <
          padicValRat 37 ((37 : ℚ) ^ 3 * u) := by
      rw [padicValRat_two_mul_thirtySeven_sq]
      omega
    have hsum0 :
        2 * (37 : ℚ) ^ 2 + (37 : ℚ) ^ 3 * u ≠ 0 := by
      intro hzero
      have heq : 2 * (37 : ℚ) ^ 2 = -((37 : ℚ) ^ 3 * u) := by
        linarith
      have hvals := congrArg (padicValRat 37) heq
      rw [padicValRat.neg] at hvals
      omega
    rw [hB]
    rw [padicValRat.add_eq_of_lt hsum0 hq0 hr0 hlt]
    exact padicValRat_two_mul_thirtySeven_sq

/-- The exact numerator form needed in Vandiver's second-case criterion. -/
theorem bernoulli_1184_numerator_not_dvd_cube :
    ¬(37 : ℤ) ^ 3 ∣ (bernoulli 1184).num := by
  have hden : DenominatorPrimeTo 37 (bernoulli 1184) := by
    apply bernoulli_denominatorPrimeTo (p := 37)
    · decide
    · norm_num
  have hB0 : bernoulli 1184 ≠ 0 := by
    intro hzero
    have hval := bernoulli_1184_padicValRat
    rw [hzero, padicValRat.zero] at hval
    norm_num at hval
  apply numerator_not_dvd_pow_of_padicValRat_lt hB0 hden
  rw [bernoulli_1184_padicValRat]
  norm_num

/-- The same numerator condition through the prime-independent Faulhaber
endpoint.  This theorem checks that the generic engine retains the exact
finite certificate first developed in this exponent-specific file. -/
theorem bernoulli_1184_numerator_not_dvd_cube_via_generic_faulhaber :
    ¬(37 : ℤ) ^ 3 ∣ (bernoulli 1184).num := by
  apply Fermat.Irregular.DirectBernoulli.bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 37) (n := 1184) (c := 7476560) (r := 2738)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply Fermat.Irregular.DirectBernoulli.pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 37)
    · decide
    · norm_num
  · exact choose_1185_1182
  · simpa using powerSum_mod_thirtySeven_pow_four
  · norm_num
  · norm_num
  · apply bernoulli_denominatorPrimeTo (p := 37)
    · decide
    · norm_num

end Fermat.ThirtySeven.HighBernoulli
