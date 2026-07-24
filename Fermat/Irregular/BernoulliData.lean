import Fermat.Basic

/-!
# Rational numerator certificates for irregular-prime arguments

The classical criteria used for the irregular exponents are phrased in terms
of divisibility of Bernoulli numerators.  Kummer congruences are most naturally
phrased using the rational `p`-adic valuation.  This file supplies the small,
generic bridge between those two formulations when the reduced denominator is
prime to `p`.
-/

namespace Fermat.Irregular.BernoulliData

/-- A rational number is `p`-integral when its reduced denominator is prime to
`p`.  This deliberately uses the concrete numerator/denominator representation
needed by the historical Bernoulli criteria. -/
def DenominatorPrimeTo (p : ℕ) (q : ℚ) : Prop := ¬p ∣ q.den

/-- The von Staudt--Clausen theorem implies that a prime `p` can occur in
the denominator of `B₂ₖ` only when `p - 1` divides `2 * k`.

This is proved from Mathlib's public theorem rather than from its private
implementation lemmas. -/
theorem bernoulli_denominatorPrimeTo_of_not_dvd_sub_one {p k : ℕ}
    [Fact p.Prime] (hnot : ¬(p - 1) ∣ 2 * k) :
    DenominatorPrimeTo p (bernoulli (2 * k)) := by
  let primes :=
    (Finset.range (2 * k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k
  let correction : ℚ := ∑ q ∈ primes, (1 : ℚ) / q
  have hprod :
      (∏ q ∈ primes, ((1 : ℚ) / q).den).Coprime p := by
    refine Nat.Coprime.prod_left fun q hq ↦ ?_
    have hq' : q ∈ Finset.range (2 * k + 2) ∧ q.Prime ∧ (q - 1) ∣ 2 * k := by
      simpa [primes] using hq
    have hne : q ≠ p := fun h ↦ hnot (h ▸ hq'.2.2)
    rw [show ((1 : ℚ) / q).den = q by simp [hq'.2.1.ne_zero]]
    exact (Nat.coprime_primes hq'.2.1 Fact.out).mpr hne
  have hcorrection : correction.den.Coprime p := by
    refine Nat.Coprime.of_dvd_left ?_ hprod
    exact Finset.Rat.den_sum_dvd_prod_den primes fun q ↦ (1 : ℚ) / q
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hsum :
      (∑ q ∈ Finset.range (2 * k + 2) with
        q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q) = correction := by
    rfl
  rw [hsum] at hz
  have hbernoulli : bernoulli (2 * k) = (z : ℚ) - correction := by
    linarith
  rw [hbernoulli]
  change ¬p ∣ ((z : ℚ) - correction).den
  rw [Rat.intCast_sub_den]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcorrection.symm

/-- Index-form version of
`bernoulli_denominatorPrimeTo_of_not_dvd_sub_one`. -/
theorem bernoulli_denominatorPrimeTo {p n : ℕ} [Fact p.Prime]
    (heven : Even n) (hnot : ¬(p - 1) ∣ n) :
    DenominatorPrimeTo p (bernoulli n) := by
  obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp heven
  exact bernoulli_denominatorPrimeTo_of_not_dvd_sub_one hnot

theorem padicValRat_eq_numeratorVal {p : ℕ} {q : ℚ}
    (hden : DenominatorPrimeTo p q) :
    padicValRat p q = padicValInt p q.num := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden]
  simp

/-- A `p`-integral rational whose numerator is prime to `p` is a
`p`-adic unit. -/
theorem padicValRat_eq_zero_of_numerator_not_dvd {p : ℕ} {q : ℚ}
    (hden : DenominatorPrimeTo p q) (hnum : ¬(p : ℤ) ∣ q.num) :
    padicValRat p q = 0 := by
  rw [padicValRat_eq_numeratorVal hden]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd hnum

/-- Dividing a `p`-adic unit by a natural number prime to `p` preserves
valuation zero. -/
theorem padicValRat_div_nat_eq_zero {p j : ℕ} {q : ℚ}
    [Fact p.Prime] (hq : q ≠ 0) (hden : DenominatorPrimeTo p q)
    (hnum : ¬(p : ℤ) ∣ q.num) (hj : ¬p ∣ j) :
    padicValRat p (q / (j : ℚ)) = 0 := by
  have hj0 : j ≠ 0 := fun hjzero ↦ hj (hjzero ▸ dvd_zero p)
  rw [padicValRat.div hq (Nat.cast_ne_zero.mpr hj0),
    padicValRat_eq_zero_of_numerator_not_dvd hden hnum,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hj]
  simp

/-- For a nonzero `p`-integral rational, divisibility of its numerator by
`p ^ n` is equivalent to the corresponding lower bound on its valuation. -/
theorem numerator_pow_dvd_iff_le_padicValRat {p n : ℕ} {q : ℚ}
    [Fact p.Prime] (hq : q ≠ 0) (hden : DenominatorPrimeTo p q) :
    (p : ℤ) ^ n ∣ q.num ↔ (n : ℤ) ≤ padicValRat p q := by
  rw [padicValRat_eq_numeratorVal hden, padicValInt_dvd_iff]
  simp [Rat.num_ne_zero.mpr hq]

/-- Valuation one is exactly one factor of `p` in the reduced numerator. -/
theorem padicValRat_eq_one_iff {p : ℕ} {q : ℚ} [Fact p.Prime]
    (hq : q ≠ 0) (hden : DenominatorPrimeTo p q) :
    padicValRat p q = 1 ↔
      (p : ℤ) ∣ q.num ∧ ¬(p : ℤ) ^ 2 ∣ q.num := by
  constructor
  · intro hval
    constructor
    · simpa using
        (numerator_pow_dvd_iff_le_padicValRat (p := p) (n := 1) hq hden).mpr (by omega)
    · intro htwo
      have hle :=
        (numerator_pow_dvd_iff_le_padicValRat (p := p) (n := 2) hq hden).mp htwo
      omega
  · rintro ⟨hone, htwo⟩
    have hone' : (1 : ℤ) ≤ padicValRat p q :=
      (numerator_pow_dvd_iff_le_padicValRat (p := p) (n := 1) hq hden).mp (by simpa)
    have htwo' : ¬(2 : ℤ) ≤ padicValRat p q := fun hle ↦
      htwo ((numerator_pow_dvd_iff_le_padicValRat (p := p) (n := 2) hq hden).mpr hle)
    omega

/-- A strict valuation bound excludes the corresponding prime power from the
reduced numerator. -/
theorem numerator_not_dvd_pow_of_padicValRat_lt {p n : ℕ} {q : ℚ}
    [Fact p.Prime] (hq : q ≠ 0) (hden : DenominatorPrimeTo p q)
    (hval : padicValRat p q < n) :
    ¬(p : ℤ) ^ n ∣ q.num := by
  intro hdvd
  exact (not_le_of_gt hval)
    ((numerator_pow_dvd_iff_le_padicValRat (p := p) (n := n) hq hden).mp hdvd)

/-- In particular, valuation one excludes the cube of `p` from the reduced
numerator, which is the shape required by Vandiver's Case-II criterion. -/
theorem numerator_not_dvd_cube_of_padicValRat_eq_one {p : ℕ} {q : ℚ}
    [Fact p.Prime] (hq : q ≠ 0) (hden : DenominatorPrimeTo p q)
    (hval : padicValRat p q = 1) :
    ¬(p : ℤ) ^ 3 ∣ q.num := by
  apply numerator_not_dvd_pow_of_padicValRat_lt hq hden
  omega

end Fermat.Irregular.BernoulliData
