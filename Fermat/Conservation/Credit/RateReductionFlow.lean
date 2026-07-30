/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Reduction of the generator-derived logarithmic rate

This module connects the exact rational logarithmic rate of a generated
real relation to the nonlinear prime-square Euler-jet flow.  It constructs
the quotient source and its rate from the generator, reduces their rational
recurrences canonically, and proves that the
moment-ready corrected and scaled relation forces the selected rate jet to
vanish modulo `p²`.

The folding-monomial constants are also cancelled generically at every
positive jet index, identifying the full quotient rate with the compact
generator-derived rate from `LogRateFlow`.
-/
import Fermat.Conservation.Credit.LogRateFlow
import Fermat.Conservation.Credit.RationalReduction
import Fermat.Conservation.Credit.RelationDepthFlow

open scoped BigOperators

namespace Fermat.Conservation.Credit.RateFlow

open PowerSeries

namespace FormalJets

/-- Formal derivatives at zero satisfy the binomial Leibniz rule. -/
theorem formalDerivativeAtZero_mul
    (n : ℕ) (f g : PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (f * g) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) *
          Flow.formalDerivativeAtZero k f *
          Flow.formalDerivativeAtZero (n - k) g := by
  rw [Flow.formalDerivativeAtZero, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  simp only [Flow.formalDerivativeAtZero]
  have hfac := Nat.choose_mul_factorial_mul_factorial hkn
  have hfacQ :
      (n.factorial : ℚ) =
        (n.choose k : ℚ) * (k.factorial : ℚ) *
          ((n - k).factorial : ℚ) := by
    exact_mod_cast hfac.symm
  rw [hfacQ]
  ring

@[simp]
theorem formalDerivativeAtZero_zero (f : PowerSeries ℚ) :
    Flow.formalDerivativeAtZero 0 f =
      PowerSeries.constantCoeff f := by
  rw [Flow.formalDerivativeAtZero]
  simp

theorem formalDerivativeAtZero_derivative
    (n : ℕ) (f : PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (d⁄dX ℚ f) =
      Flow.formalDerivativeAtZero (n + 1) f := by
  simp only [Flow.formalDerivativeAtZero,
    PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

/-- A power-series product supplies the quotient-jet recurrence after
exponential normalization. -/
theorem isQuotientJetRecurrence_of_eq_mul
    {numerator denominator quotient : PowerSeries ℚ}
    (h : numerator = denominator * quotient) :
    Flow.IsQuotientJetRecurrence
      (fun n ↦ Flow.formalDerivativeAtZero n numerator)
      (fun n ↦ Flow.formalDerivativeAtZero n denominator)
      (fun n ↦ Flow.formalDerivativeAtZero n quotient) := by
  intro n
  change Flow.formalDerivativeAtZero n numerator = _
  rw [h, mul_comm, formalDerivativeAtZero_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A formal logarithmic-rate equation supplies the abstract logarithmic
jet recurrence used by `NonlinearFlow`. -/
theorem isLogDerivativeJetRecurrence_of_isLogRate
    {source rate : PowerSeries ℚ}
    (h : LogRate.Formal.IsLogRate source rate) :
    Flow.IsLogDerivativeJetRecurrence
      (fun n ↦ Flow.formalDerivativeAtZero n source)
      (fun n ↦ Flow.formalDerivativeAtZero n rate) := by
  intro n
  change Flow.formalDerivativeAtZero (n + 1) source = _
  rw [← formalDerivativeAtZero_derivative, h,
    mul_comm, formalDerivativeAtZero_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end FormalJets

namespace PolynomialExp

open Polynomial
open LogRate.Formal

/-- Formal exponential substitution for an integral polynomial. -/
noncomputable def series (P : ℤ[X]) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

theorem algebraMap_int_eq_C (z : ℤ) :
    algebraMap ℤ (PowerSeries ℚ) z =
      PowerSeries.C (z : ℚ) := by
  ext (_ | n) <;> simp

@[simp]
theorem series_add (P Q : ℤ[X]) :
    series (P + Q) = series P + series Q := by
  simp [series]

@[simp]
theorem series_sub (P Q : ℤ[X]) :
    series (P - Q) = series P - series Q := by
  simp [series]

@[simp]
theorem series_mul (P Q : ℤ[X]) :
    series (P * Q) = series P * series Q := by
  simp [series]

@[simp]
theorem series_pow (P : ℤ[X]) (e : ℕ) :
    series (P ^ e) = series P ^ e := by
  simp [series]

@[simp]
theorem series_C (z : ℤ) :
    series (Polynomial.C z) = PowerSeries.C (z : ℚ) := by
  rw [series, Polynomial.eval₂_C, algebraMap_int_eq_C]

theorem formalDerivativeAtZero_series
    (P : ℤ[X]) (n : ℕ) :
    Flow.formalDerivativeAtZero n (series P) =
      (Flow.exponentialMoment n P : ℚ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [series_add, LogRate.Formal.formalDerivativeAtZero_add,
        Flow.exponentialMoment_add, Int.cast_add, hP, hQ]
  | monomial i a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        series_mul, series_C]
      simp only [series, Polynomial.eval₂_pow,
        Polynomial.eval₂_X]
      rw [PowerSeries.exp_pow_eq_rescale_exp]
      rw [Flow.formalDerivativeAtZero,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
        PowerSeries.coeff_exp,
        Flow.exponentialMoment_C_mul_X_pow]
      push_cast
      have hfac : (n.factorial : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp

theorem series_geometricPolynomial (r : ℕ) :
    series (RealFlow.geometricPolynomial r) =
      geometricExp r := by
  rw [RealFlow.geometricPolynomial, series,
    Polynomial.eval₂_finsetSum]
  simp_rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rfl

theorem series_foldedTeichNodePolynomial
    (p : ℕ) (a : (ZMod p)ˣ) :
    series (RealFlow.foldedTeichNodePolynomial p a) =
      foldedExp (p + 1 - (a : ZMod p).val)
        (RealFlow.teichLift p a) := by
  rw [RealFlow.foldedTeichNodePolynomial, series_mul,
    series_pow Polynomial.X,
    series_pow (RealFlow.geometricPolynomial (RealFlow.teichLift p a)),
    series_geometricPolynomial]
  simp only [series, Polynomial.eval₂_X]
  rw [PowerSeries.exp_pow_eq_rescale_exp]
  rfl

theorem series_normalizedFoldedNodePolynomial
    (p : ℕ) (a : (ZMod p)ˣ) :
    series (RealFlow.normalizedFoldedNodePolynomial p a) =
      foldedExp (p + 1 - (a : ZMod p).val)
          (RealFlow.teichLift p a) ^ (p - 1) := by
  rw [RealFlow.normalizedFoldedNodePolynomial, series_pow,
    series_foldedTeichNodePolynomial]

theorem series_normalizedNodePolynomial
    {p : ℕ} (data : RealGauge.RealGaugeData p) (i : ℕ) :
    series (RealFlow.normalizedNodePolynomial data i) =
      foldedExp
          (p + 1 - (data.nodeLift i : ZMod p).val)
          (RealFlow.teichLift p (data.nodeLift i)) ^ (p - 1) := by
  rw [RealFlow.normalizedNodePolynomial,
    series_normalizedFoldedNodePolynomial]

end PolynomialExp

namespace GeneratedRelation

open Polynomial
open LogRate.Formal

/-- Exponential series of one normalized generated node. -/
noncomputable def nodeSeries {p : ℕ}
    (data : RealGauge.RealGaugeData p) (i : ℕ) :
    PowerSeries ℚ :=
  foldedExp
      (p + 1 - (data.nodeLift i : ZMod p).val)
      (RealFlow.teichLift p (data.nodeLift i)) ^ (p - 1)

/-- Full logarithmic rate of one normalized node, including its constant
folding monomial contribution. -/
noncomputable def nodeRate {p : ℕ}
    (data : RealGauge.RealGaugeData p) (i : ℕ) :
    PowerSeries ℚ :=
  PowerSeries.C ((p - 1 : ℕ) : ℚ) *
    foldedRate
      (p + 1 - (data.nodeLift i : ZMod p).val)
      (RealFlow.teichLift p (data.nodeLift i))

theorem series_normalizedNodePolynomial_eq_nodeSeries
    {p : ℕ} (data : RealGauge.RealGaugeData p) (i : ℕ) :
    PolynomialExp.series (RealFlow.normalizedNodePolynomial data i) =
      nodeSeries data i := by
  unfold nodeSeries
  exact PolynomialExp.series_normalizedNodePolynomial data i

theorem isLogRate_nodeSeries
    {p : ℕ} (data : RealGauge.RealGaugeData p) (i : ℕ) :
    IsLogRate (nodeSeries data i) (nodeRate data i) := by
  unfold nodeSeries nodeRate
  exact normalized_folded_logRate
    (p + 1 - (data.nodeLift i : ZMod p).val)
    (RealFlow.teichLift p (data.nodeLift i)) (p - 1)

theorem IsLogRate.finset_prod
    {ι : Type*} (s : Finset ι)
    (source rate : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, IsLogRate (source i) (rate i)) :
    IsLogRate (∏ i ∈ s, source i) (∑ i ∈ s, rate i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [IsLogRate]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (h a (by simp)).mul
        (ih fun i hi ↦ h i (by simp [hi]))

/-- Full numerator rate before cancellation of constant monomial terms. -/
noncomputable def numeratorRate {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  ∑ i,
    (PowerSeries.C
        (RealFlow.positiveExponent (raw i) : ℚ) *
      nodeRate data (i.val + 1) +
    PowerSeries.C
        (RealFlow.negativeExponent (raw i) : ℚ) *
      nodeRate data i.val)

/-- Full denominator rate before cancellation of constant monomial terms. -/
noncomputable def denominatorRate {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  ∑ i,
    (PowerSeries.C
        (RealFlow.positiveExponent (raw i) : ℚ) *
      nodeRate data i.val +
    PowerSeries.C
        (RealFlow.negativeExponent (raw i) : ℚ) *
      nodeRate data (i.val + 1))

/-- Exponential source represented by the generated relation numerator. -/
noncomputable def numeratorSource {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  ∏ i,
    nodeSeries data (i.val + 1) ^
        RealFlow.positiveExponent (raw i) *
      nodeSeries data i.val ^
        RealFlow.negativeExponent (raw i)

/-- Exponential source represented by the generated relation denominator. -/
noncomputable def denominatorSource {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  ∏ i,
    nodeSeries data i.val ^
        RealFlow.positiveExponent (raw i) *
      nodeSeries data (i.val + 1) ^
        RealFlow.negativeExponent (raw i)

theorem series_relationNumerator
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    PolynomialExp.series (RealFlow.relationNumerator data raw) =
      numeratorSource data raw := by
  rw [RealFlow.relationNumerator, PolynomialExp.series,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_pow]
  change
    PolynomialExp.series
          (RealFlow.normalizedNodePolynomial data (i.val + 1)) ^
        RealFlow.positiveExponent (raw i) *
      PolynomialExp.series
          (RealFlow.normalizedNodePolynomial data i.val) ^
        RealFlow.negativeExponent (raw i) = _
  rw [series_normalizedNodePolynomial_eq_nodeSeries,
    series_normalizedNodePolynomial_eq_nodeSeries]

theorem series_relationDenominator
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    PolynomialExp.series (RealFlow.relationDenominator data raw) =
      denominatorSource data raw := by
  rw [RealFlow.relationDenominator, PolynomialExp.series,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_pow]
  change
    PolynomialExp.series
          (RealFlow.normalizedNodePolynomial data i.val) ^
        RealFlow.positiveExponent (raw i) *
      PolynomialExp.series
          (RealFlow.normalizedNodePolynomial data (i.val + 1)) ^
        RealFlow.negativeExponent (raw i) = _
  rw [series_normalizedNodePolynomial_eq_nodeSeries,
    series_normalizedNodePolynomial_eq_nodeSeries]

theorem isLogRate_numeratorSource
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    IsLogRate (numeratorSource data raw)
      (numeratorRate data raw) := by
  rw [numeratorSource, numeratorRate]
  apply IsLogRate.finset_prod
  intro i _
  exact
    ((isLogRate_nodeSeries data (i.val + 1)).pow
      (RealFlow.positiveExponent (raw i))).mul
    ((isLogRate_nodeSeries data i.val).pow
      (RealFlow.negativeExponent (raw i)))

theorem isLogRate_denominatorSource
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    IsLogRate (denominatorSource data raw)
      (denominatorRate data raw) := by
  rw [denominatorSource, denominatorRate]
  apply IsLogRate.finset_prod
  intro i _
  exact
    ((isLogRate_nodeSeries data i.val).pow
      (RealFlow.positiveExponent (raw i))).mul
    ((isLogRate_nodeSeries data (i.val + 1)).pow
      (RealFlow.negativeExponent (raw i)))

/-- Full rational rate of the generated numerator/denominator quotient. -/
noncomputable def fullRelationRate {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  numeratorRate data raw - denominatorRate data raw

/-- Rational quotient source for the uncorrected generated relation. -/
noncomputable def relationSource {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : PowerSeries ℚ :=
  numeratorSource data raw * (denominatorSource data raw)⁻¹

theorem denominatorSource_constantCoeff_ne_zero
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    PowerSeries.constantCoeff (denominatorSource data raw) ≠ 0 := by
  rw [← series_relationDenominator]
  rw [← FormalJets.formalDerivativeAtZero_zero,
    PolynomialExp.formalDerivativeAtZero_series,
    Flow.exponentialMoment_zero_eq_eval_one]
  intro hzero
  letI : Fact (1 < p ^ 2) :=
    ⟨by nlinarith [data.prime.two_le]⟩
  have hunit :=
    RealFlow.relationDenominator_moment_zero_isUnit data raw
  rw [Flow.momentModPrimeSq,
    Flow.exponentialMoment_zero_eq_eval_one] at hunit
  have hzeroInt :
      (RealFlow.relationDenominator data raw).eval 1 = 0 := by
    exact_mod_cast hzero
  rw [hzeroInt, Int.cast_zero] at hunit
  exact not_isUnit_zero hunit

theorem denominatorSource_ne_zero
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    denominatorSource data raw ≠ 0 := by
  intro hzero
  apply denominatorSource_constantCoeff_ne_zero data raw
  rw [hzero]
  simp

theorem isLogRate_relationSource
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    IsLogRate (relationSource data raw)
      (fullRelationRate data raw) := by
  apply (isLogRate_numeratorSource data raw).quotient
    (isLogRate_denominatorSource data raw)
  · rw [relationSource, mul_assoc,
      PowerSeries.inv_mul_cancel
        (denominatorSource data raw)
        (denominatorSource_constantCoeff_ne_zero data raw),
      mul_one]
  · exact denominatorSource_ne_zero data raw

/-- A prime-square congruence to one makes an integer a prime unit. -/
theorem not_prime_dvd_of_prime_sq_dvd_sub_one
    {p : ℕ} (hp : p.Prime) {z : ℤ}
    (h : (p : ℤ) ^ 2 ∣ z - 1) :
    ¬(p : ℤ) ∣ z := by
  intro hz
  have hpSq : (p : ℤ) ∣ (p : ℤ) ^ 2 := by
    simp [pow_two]
  have hdiff : (p : ℤ) ∣ z - 1 := hpSq.trans h
  have hone : (p : ℤ) ∣ 1 := by
    convert hz.sub hdiff using 1
    ring
  have honeNat : p ∣ 1 := by
    exact_mod_cast hone
  exact hp.not_dvd_one honeNat

theorem prime_not_dvd_relationNumerator_eval_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ¬(p : ℤ) ∣ (RealFlow.relationNumerator data raw).eval 1 :=
  not_prime_dvd_of_prime_sq_dvd_sub_one data.prime
    (RealFlow.prime_sq_dvd_relationNumerator_eval_one_sub_one data raw)

theorem prime_not_dvd_relationDenominator_eval_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ¬(p : ℤ) ∣ (RealFlow.relationDenominator data raw).eval 1 :=
  not_prime_dvd_of_prime_sq_dvd_sub_one data.prime
    (RealFlow.prime_sq_dvd_relationDenominator_eval_one_sub_one data raw)

theorem intCast_ne_zero_of_not_prime_dvd
    {p : ℕ} {z : ℤ} (h : ¬(p : ℤ) ∣ z) :
    (z : ℚ) ≠ 0 := by
  intro hz
  have hzInt : z = 0 := by
    exact_mod_cast hz
  subst z
  exact h (dvd_zero (p : ℤ))

private theorem denominatorPrimeTo_inv_intCast
    {p : ℕ} {z : ℤ}
    (hz : ¬(p : ℤ) ∣ z) :
    Bernoulli.DenominatorPrimeTo p ((z : ℚ)⁻¹) := by
  apply RationalFlow.denominatorPrimeTo_inv_of_num_not_dvd
  · exact intCast_ne_zero_of_not_prime_dvd hz
  · simpa using hz

/-- Rational Euler jets of the generated numerator, denominator, quotient,
and full logarithmic rate. -/
noncomputable def numeratorJet {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) : ℚ :=
  Flow.formalDerivativeAtZero n (numeratorSource data raw)

noncomputable def denominatorJet {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) : ℚ :=
  Flow.formalDerivativeAtZero n (denominatorSource data raw)

noncomputable def sourceJet {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) : ℚ :=
  Flow.formalDerivativeAtZero n (relationSource data raw)

noncomputable def rateJet {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) : ℚ :=
  Flow.formalDerivativeAtZero n (fullRelationRate data raw)

theorem numeratorJet_eq_moment
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) :
    numeratorJet data raw n =
      (Flow.exponentialMoment n
        (RealFlow.relationNumerator data raw) : ℚ) := by
  rw [numeratorJet, ← series_relationNumerator,
    PolynomialExp.formalDerivativeAtZero_series]

theorem denominatorJet_eq_moment
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) :
    denominatorJet data raw n =
      (Flow.exponentialMoment n
        (RealFlow.relationDenominator data raw) : ℚ) := by
  rw [denominatorJet, ← series_relationDenominator,
    PolynomialExp.formalDerivativeAtZero_series]

theorem denominatorJet_zero_eq_eval_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    denominatorJet data raw 0 =
      (((RealFlow.relationDenominator data raw).eval (1 : ℤ) : ℤ) :
        ℚ) := by
  rw [denominatorJet_eq_moment,
    Flow.exponentialMoment_zero_eq_eval_one]

theorem numeratorJet_zero_eq_eval_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    numeratorJet data raw 0 =
      (((RealFlow.relationNumerator data raw).eval (1 : ℤ) : ℤ) :
        ℚ) := by
  rw [numeratorJet_eq_moment,
    Flow.exponentialMoment_zero_eq_eval_one]

theorem quotientJetRecurrence_relation
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Flow.IsQuotientJetRecurrence
      (numeratorJet data raw) (denominatorJet data raw)
      (sourceJet data raw) := by
  apply FormalJets.isQuotientJetRecurrence_of_eq_mul
  rw [relationSource]
  calc
    numeratorSource data raw =
        numeratorSource data raw * 1 := by rw [mul_one]
    _ = numeratorSource data raw *
        ((denominatorSource data raw)⁻¹ *
          denominatorSource data raw) := by
      rw [PowerSeries.inv_mul_cancel
        (denominatorSource data raw)
        (denominatorSource_constantCoeff_ne_zero data raw)]
    _ = denominatorSource data raw *
        (numeratorSource data raw *
          (denominatorSource data raw)⁻¹) := by ac_rfl

theorem logDerivativeJetRecurrence_relation
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Flow.IsLogDerivativeJetRecurrence
      (sourceJet data raw) (rateJet data raw) :=
  FormalJets.isLogDerivativeJetRecurrence_of_isLogRate
    (isLogRate_relationSource data raw)

theorem denominatorPrimeTo_numeratorJet
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ∀ n, Bernoulli.DenominatorPrimeTo p
      (numeratorJet data raw n) := by
  intro n
  rw [numeratorJet_eq_moment]
  exact RationalFlow.denominatorPrimeTo_intCast data.prime _

theorem denominatorPrimeTo_denominatorJet
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ∀ n, Bernoulli.DenominatorPrimeTo p
      (denominatorJet data raw n) := by
  intro n
  rw [denominatorJet_eq_moment]
  exact RationalFlow.denominatorPrimeTo_intCast data.prime _

theorem denominatorPrimeTo_sourceJet
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ∀ n, Bernoulli.DenominatorPrimeTo p
      (sourceJet data raw n) := by
  apply RationalFlow.denominatorPrimeTo_quotient_of_recurrence
    data.prime
    (quotientJetRecurrence_relation data raw)
    (denominatorPrimeTo_numeratorJet data raw)
    (denominatorPrimeTo_denominatorJet data raw)
  · rw [denominatorJet_zero_eq_eval_one]
    exact intCast_ne_zero_of_not_prime_dvd
      (prime_not_dvd_relationDenominator_eval_one data raw)
  · rw [denominatorJet_zero_eq_eval_one]
    exact denominatorPrimeTo_inv_intCast
      (prime_not_dvd_relationDenominator_eval_one data raw)

theorem sourceJet_zero_ne_zero
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    sourceJet data raw 0 ≠ 0 := by
  rw [sourceJet, FormalJets.formalDerivativeAtZero_zero,
    relationSource, map_mul, PowerSeries.constantCoeff_inv]
  apply mul_ne_zero
  · rw [← FormalJets.formalDerivativeAtZero_zero,
      ← numeratorJet, numeratorJet_zero_eq_eval_one]
    exact intCast_ne_zero_of_not_prime_dvd
      (prime_not_dvd_relationNumerator_eval_one data raw)
  · exact inv_ne_zero
      (denominatorSource_constantCoeff_ne_zero data raw)

theorem denominatorPrimeTo_sourceJet_zero_inv
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Bernoulli.DenominatorPrimeTo p
      ((sourceJet data raw 0)⁻¹) := by
  have hquot := quotientJetRecurrence_relation data raw 0
  simp at hquot
  have hsource :
      (sourceJet data raw 0)⁻¹ =
        denominatorJet data raw 0 *
          (numeratorJet data raw 0)⁻¹ := by
    have hnum0 : numeratorJet data raw 0 ≠ 0 := by
      rw [numeratorJet_zero_eq_eval_one]
      exact intCast_ne_zero_of_not_prime_dvd
        (prime_not_dvd_relationNumerator_eval_one data raw)
    field_simp [sourceJet_zero_ne_zero data raw, hnum0]
    simpa [mul_comm] using hquot
  rw [hsource]
  apply RationalFlow.denominatorPrimeTo_mul data.prime
    (denominatorPrimeTo_denominatorJet data raw 0)
  rw [numeratorJet_zero_eq_eval_one]
  exact denominatorPrimeTo_inv_intCast
    (prime_not_dvd_relationNumerator_eval_one data raw)

theorem denominatorPrimeTo_rateJet
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ∀ n, Bernoulli.DenominatorPrimeTo p
      (rateJet data raw n) :=
  RationalFlow.denominatorPrimeTo_logDerivative_of_recurrence
    data.prime
    (logDerivativeJetRecurrence_relation data raw)
    (denominatorPrimeTo_sourceJet data raw)
    (sourceJet_zero_ne_zero data raw)
    (denominatorPrimeTo_sourceJet_zero_inv data raw)

/-- Numerator-minus-denominator jet before quotient division. -/
noncomputable def differenceJet {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) : ℚ :=
  Flow.formalDerivativeAtZero n
    (numeratorSource data raw - denominatorSource data raw)

/-- Jet of the normalized quotient minus one. -/
noncomputable def quotientJet {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) : ℚ :=
  Flow.formalDerivativeAtZero n
    (relationSource data raw - 1)

theorem differenceJet_eq_moment
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) :
    differenceJet data raw n =
      (Flow.exponentialMoment n
        (RealFlow.relationNumerator data raw -
          RealFlow.relationDenominator data raw) : ℚ) := by
  rw [differenceJet, ← series_relationNumerator,
    ← series_relationDenominator, ← PolynomialExp.series_sub,
    PolynomialExp.formalDerivativeAtZero_series]

theorem quotientJetRecurrence_difference
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Flow.IsQuotientJetRecurrence
      (differenceJet data raw) (denominatorJet data raw)
      (quotientJet data raw) := by
  apply FormalJets.isQuotientJetRecurrence_of_eq_mul
  have hsource :
      numeratorSource data raw =
        denominatorSource data raw * relationSource data raw := by
    rw [relationSource]
    calc
      numeratorSource data raw =
          numeratorSource data raw * 1 := by rw [mul_one]
      _ = numeratorSource data raw *
          ((denominatorSource data raw)⁻¹ *
            denominatorSource data raw) := by
        rw [PowerSeries.inv_mul_cancel
          (denominatorSource data raw)
          (denominatorSource_constantCoeff_ne_zero data raw)]
      _ = denominatorSource data raw *
          (numeratorSource data raw *
            (denominatorSource data raw)⁻¹) := by ac_rfl
  change
    numeratorSource data raw - denominatorSource data raw =
      denominatorSource data raw *
        (relationSource data raw - 1)
  rw [hsource]
  ring

theorem denominatorPrimeTo_differenceJet
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ∀ n, Bernoulli.DenominatorPrimeTo p
      (differenceJet data raw n) := by
  intro n
  rw [differenceJet_eq_moment]
  exact RationalFlow.denominatorPrimeTo_intCast data.prime _

theorem denominatorPrimeTo_quotientJet
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ∀ n, Bernoulli.DenominatorPrimeTo p
      (quotientJet data raw n) := by
  intro n
  rw [quotientJet, LogRate.Formal.formalDerivativeAtZero_sub]
  apply RationalFlow.denominatorPrimeTo_sub data.prime
    (denominatorPrimeTo_sourceJet data raw n)
  rcases n with _ | n
  · simpa [Flow.formalDerivativeAtZero] using
      RationalFlow.denominatorPrimeTo_one
        (p := p) data.prime
  · simpa [Flow.formalDerivativeAtZero] using
      RationalFlow.denominatorPrimeTo_zero
        (p := p) data.prime

theorem sourceJet_zero_eq_quotientJet_add_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    sourceJet data raw 0 = quotientJet data raw 0 + 1 := by
  rw [quotientJet, LogRate.Formal.formalDerivativeAtZero_sub]
  simp [sourceJet, Flow.formalDerivativeAtZero]

theorem sourceJet_eq_quotientJet_of_pos
    {p n : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (hn : 0 < n) :
    sourceJet data raw n = quotientJet data raw n := by
  rw [quotientJet, LogRate.Formal.formalDerivativeAtZero_sub]
  simp [sourceJet, Flow.formalDerivativeAtZero, hn.ne']

private theorem formalDerivativeAtZero_C_of_pos
    (q : ℚ) (n : ℕ) (hn : 0 < n) :
    Flow.formalDerivativeAtZero n (PowerSeries.C q) = 0 := by
  rw [Flow.formalDerivativeAtZero, PowerSeries.coeff_C, if_neg hn.ne']
  simp

private theorem formalDerivativeAtZero_fintype_sum
    {ι : Type*} [Fintype ι] (n : ℕ)
    (f : ι → PowerSeries ℚ) :
    Flow.formalDerivativeAtZero n (∑ i, f i) =
      ∑ i, Flow.formalDerivativeAtZero n (f i) := by
  simp [Flow.formalDerivativeAtZero, Finset.mul_sum]

private theorem positive_sub_negative_cast (z : ℤ) :
    ((RealFlow.positiveExponent z : ℕ) : ℚ) -
        ((RealFlow.negativeExponent z : ℕ) : ℚ) =
      (z : ℚ) := by
  cases z with
  | ofNat n =>
      simp [RealFlow.positiveExponent, RealFlow.negativeExponent]
  | negSucc n =>
      simp [RealFlow.positiveExponent, RealFlow.negativeExponent]

private theorem formalDerivativeAtZero_nodeRate_of_pos
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (i n : ℕ) (hn : 0 < n) :
    Flow.formalDerivativeAtZero n (nodeRate data i) =
      2 * (((p - 1 : ℕ) : ℚ)) *
        Flow.formalDerivativeAtZero n
          (LogRate.Formal.geometricRate
            (RealFlow.teichLift p (data.nodeLift i))) := by
  rw [nodeRate, LogRate.Formal.formalDerivativeAtZero_C_mul,
    LogRate.Formal.foldedRate,
    LogRate.Formal.formalDerivativeAtZero_add,
    LogRate.Formal.formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_C_of_pos _ n hn]
  simp only [zero_add]
  ring

/-- At every positive index, the folding-monomial constants cancel from
the full numerator-minus-denominator rate. -/
theorem formalDerivativeAtZero_fullRelationRate_eq_generatedRelationRate
    {p n : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (hn : 0 < n) :
    Flow.formalDerivativeAtZero n (fullRelationRate data raw) =
      Flow.formalDerivativeAtZero n
        (LogRate.Relation.generatedRelationRate data raw) := by
  rw [fullRelationRate, LogRate.Formal.formalDerivativeAtZero_sub,
    numeratorRate, denominatorRate,
    formalDerivativeAtZero_fintype_sum,
    formalDerivativeAtZero_fintype_sum,
    LogRate.Relation.generatedRelationRate,
    LogRate.Formal.formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_fintype_sum]
  simp_rw [LogRate.Formal.formalDerivativeAtZero_add,
    LogRate.Formal.formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_nodeRate_of_pos data _ n hn,
    LogRate.Formal.formalDerivativeAtZero_sub]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpCast :
      (((p - 1 : ℕ) : ℚ)) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub data.prime.one_le]
    norm_num
  rw [← hpCast]
  rw [show
    (raw i : ℚ) =
      ((RealFlow.positiveExponent (raw i) : ℕ) : ℚ) -
        ((RealFlow.negativeExponent (raw i) : ℕ) : ℚ) by
      exact (positive_sub_negative_cast (raw i)).symm]
  ring

end GeneratedRelation

namespace Correction

open Polynomial

/-- Every exponential moment of a visibly prime-square-scaled correction
vanishes after reduction modulo `p²`. -/
theorem momentModPrimeSq_C_prime_sq_mul
    (p n : ℕ) (H : ℤ[X]) :
    Flow.momentModPrimeSq p n
        (Polynomial.C ((p : ℤ) ^ 2) * H) = 0 := by
  rw [Flow.momentModPrimeSq, Flow.exponentialMoment_C_mul]
  apply Flow.intCast_eq_zero_of_prime_sq_dvd
  exact dvd_mul_right ((p : ℤ) ^ 2) _

/-- Subtracting `p²·H` is invisible to every reduced exponential moment. -/
theorem momentModPrimeSq_sub_C_prime_sq_mul
    (p n : ℕ) (P H : ℤ[X]) :
    Flow.momentModPrimeSq p n
        (P - Polynomial.C ((p : ℤ) ^ 2) * H) =
      Flow.momentModPrimeSq p n P := by
  change
    ((Flow.exponentialMoment n
      (P - Polynomial.C ((p : ℤ) ^ 2) * H) : ℤ) :
        ZMod (p ^ 2)) =
      ((Flow.exponentialMoment n P : ℤ) : ZMod (p ^ 2))
  rw [Flow.exponentialMoment_sub,
    Flow.exponentialMoment_C_mul]
  push_cast
  have hp2Int :
      ((((p : ℤ) ^ 2 : ℤ)) : ZMod (p ^ 2)) = 0 :=
    Flow.intCast_eq_zero_of_prime_sq_dvd (dvd_refl ((p : ℤ) ^ 2))
  have hp2 :
      (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    simpa only [Int.cast_pow, Int.cast_natCast] using hp2Int
  rw [hp2, zero_mul, sub_zero]

/-- Multiplication by a scalar congruent to one modulo `p²` is invisible
to every reduced exponential moment. -/
theorem momentModPrimeSq_C_mul_eq_of_prime_sq_dvd_sub_one
    (p n : ℕ) (s : ℤ) (Q : ℤ[X])
    (hs : ((p : ℤ) ^ 2) ∣ s - 1) :
    Flow.momentModPrimeSq p n (Polynomial.C s * Q) =
      Flow.momentModPrimeSq p n Q := by
  have hsZero :
      ((s - 1 : ℤ) : ZMod (p ^ 2)) = 0 :=
    Flow.intCast_eq_zero_of_prime_sq_dvd hs
  have hsOne : (s : ZMod (p ^ 2)) = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_one] using hsZero
  change
    ((Flow.exponentialMoment n (Polynomial.C s * Q) : ℤ) :
        ZMod (p ^ 2)) =
      ((Flow.exponentialMoment n Q : ℤ) : ZMod (p ^ 2))
  rw [Flow.exponentialMoment_C_mul]
  push_cast
  rw [hsOne, one_mul]

/-- A scalar congruent to one modulo `p²` does not change a reduced
numerator-minus-denominator moment. -/
theorem momentModPrimeSq_sub_C_mul_eq_of_prime_sq_dvd_sub_one
    (p n : ℕ) (s : ℤ) (P Q : ℤ[X])
    (hs : ((p : ℤ) ^ 2) ∣ s - 1) :
    Flow.momentModPrimeSq p n (P - Polynomial.C s * Q) =
      Flow.momentModPrimeSq p n (P - Q) := by
  have hsZero :
      ((s - 1 : ℤ) : ZMod (p ^ 2)) = 0 :=
    Flow.intCast_eq_zero_of_prime_sq_dvd hs
  have hsOne : (s : ZMod (p ^ 2)) = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_one] using hsZero
  change
    ((Flow.exponentialMoment n
      (P - Polynomial.C s * Q) : ℤ) : ZMod (p ^ 2)) =
      ((Flow.exponentialMoment n (P - Q) : ℤ) :
        ZMod (p ^ 2))
  rw [Flow.exponentialMoment_sub, Flow.exponentialMoment_C_mul,
    Flow.exponentialMoment_sub]
  push_cast
  rw [hsOne, one_mul]

/-- Both the visible `p²` correction and a scalar congruent to one are
invisible to the reduced relation-difference moments. -/
theorem momentModPrimeSq_corrected_scaled_sub_eq
    (p n : ℕ) (s : ℤ) (P Q H : ℤ[X])
    (hs : ((p : ℤ) ^ 2) ∣ s - 1) :
    Flow.momentModPrimeSq p n
        ((P - Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C s * Q) =
      Flow.momentModPrimeSq p n (P - Q) := by
  have hpoly :
      (P - Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C s * Q =
        (P - Polynomial.C s * Q) -
          Polynomial.C ((p : ℤ) ^ 2) * H := by
    ring
  rw [hpoly, momentModPrimeSq_sub_C_prime_sq_mul]
  exact momentModPrimeSq_sub_C_mul_eq_of_prime_sq_dvd_sub_one
    p n s P Q hs

end Correction

namespace Composition

open Polynomial

theorem reduce_differenceJet_eq_momentModPrimeSq
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) :
    RationalFlow.reduce p
        (GeneratedRelation.differenceJet data raw n) =
      Flow.momentModPrimeSq p n
        (RealFlow.relationNumerator data raw -
          RealFlow.relationDenominator data raw) := by
  rw [GeneratedRelation.differenceJet_eq_moment,
    RationalFlow.reduce_intCast, Flow.momentModPrimeSq]

theorem reduce_denominatorJet_eq_momentModPrimeSq
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (n : ℕ) :
    RationalFlow.reduce p
        (GeneratedRelation.denominatorJet data raw n) =
      Flow.momentModPrimeSq p n
        (RealFlow.relationDenominator data raw) := by
  rw [GeneratedRelation.denominatorJet_eq_moment,
    RationalFlow.reduce_intCast, Flow.momentModPrimeSq]

/-- The exact rational quotient recurrence reduces to the uncorrected
polynomial moment recurrence. -/
theorem relation_polynomial_quotientJetRecurrence
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Flow.IsPolynomialQuotientJetRecurrence p
      (RealFlow.relationNumerator data raw -
        RealFlow.relationDenominator data raw)
      (RealFlow.relationDenominator data raw)
      (fun n ↦ RationalFlow.reduce p
        (GeneratedRelation.quotientJet data raw n)) := by
  have hrec :=
    RationalFlow.reduce_quotientJetRecurrence
      data.prime
      (GeneratedRelation.denominatorPrimeTo_denominatorJet data raw)
      (GeneratedRelation.denominatorPrimeTo_quotientJet data raw)
      (GeneratedRelation.quotientJetRecurrence_difference data raw)
  intro n
  simpa only [reduce_differenceJet_eq_momentModPrimeSq,
    reduce_denominatorJet_eq_momentModPrimeSq] using hrec n

/-- The moment-ready correction and retained scalar reuse the same
modular quotient sequence as the uncorrected generated relation. -/
theorem corrected_scaled_polynomial_quotientJetRecurrence
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (s : ℤ) (H : ℤ[X])
    (hs : ((p : ℤ) ^ 2) ∣ s - 1) :
    Flow.IsPolynomialQuotientJetRecurrence p
      ((RealFlow.relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
        Polynomial.C s *
          RealFlow.relationDenominator data raw)
      (Polynomial.C s *
        RealFlow.relationDenominator data raw)
      (fun n ↦ RationalFlow.reduce p
        (GeneratedRelation.quotientJet data raw n)) := by
  have hrec := relation_polynomial_quotientJetRecurrence data raw
  intro n
  simpa only [
    Correction.momentModPrimeSq_corrected_scaled_sub_eq
      p _ s (RealFlow.relationNumerator data raw)
        (RealFlow.relationDenominator data raw) H hs,
    Correction.momentModPrimeSq_C_mul_eq_of_prime_sq_dvd_sub_one
      p _ s (RealFlow.relationDenominator data raw) hs] using hrec n

theorem corrected_scaled_denominator_moment_zero_isUnit
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (s : ℤ)
    (hs : ((p : ℤ) ^ 2) ∣ s - 1) :
    IsUnit
      (Flow.momentModPrimeSq p 0
        (Polynomial.C s *
          RealFlow.relationDenominator data raw)) := by
  rw [Correction.momentModPrimeSq_C_mul_eq_of_prime_sq_dvd_sub_one
    p 0 s (RealFlow.relationDenominator data raw) hs]
  exact RealFlow.relationDenominator_moment_zero_isUnit data raw

theorem reduced_quotientJet_zero
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    RationalFlow.reduce p
        (GeneratedRelation.quotientJet data raw 0) = 0 := by
  have hrec := relation_polynomial_quotientJetRecurrence data raw
  have hnumZero :
      Flow.momentModPrimeSq p 0
        (RealFlow.relationNumerator data raw -
          RealFlow.relationDenominator data raw) = 0 := by
    change
      ((Flow.exponentialMoment 0
        (RealFlow.relationNumerator data raw -
          RealFlow.relationDenominator data raw) : ℤ) :
            ZMod (p ^ 2)) = 0
    apply Flow.intCast_eq_zero_of_prime_sq_dvd
    rw [Flow.exponentialMoment_zero_eq_eval_one]
    exact RealFlow.prime_sq_dvd_relation_difference_eval_one data raw
  have hlayers :=
    Flow.quotientJet_prime_layers data.prime hrec
      (RealFlow.relationDenominator_moment_zero_isUnit data raw)
      hnumZero
      (N := 0)
      (by intro n hn hnle; omega)
      (by intro n hn hnle _; omega)
  exact hlayers.1

theorem reduced_sourceJet_zero
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    RationalFlow.reduce p
        (GeneratedRelation.sourceJet data raw 0) = 1 := by
  rw [GeneratedRelation.sourceJet_zero_eq_quotientJet_add_one]
  rw [RationalFlow.reduce_add data.prime
    (GeneratedRelation.denominatorPrimeTo_quotientJet data raw 0)
    (RationalFlow.denominatorPrimeTo_one data.prime)]
  rw [reduced_quotientJet_zero data raw, RationalFlow.reduce_one]
  simp

theorem reduced_sourceJet_eq_quotientJet_of_pos
    {p n : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (hn : 0 < n) :
    RationalFlow.reduce p
        (GeneratedRelation.sourceJet data raw n) =
      RationalFlow.reduce p
        (GeneratedRelation.quotientJet data raw n) := by
  rw [GeneratedRelation.sourceJet_eq_quotientJet_of_pos data raw hn]

theorem reduced_logDerivativeJetRecurrence
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    Flow.IsLogDerivativeJetRecurrence
      (fun n ↦ RationalFlow.reduce p
        (GeneratedRelation.sourceJet data raw n))
      (fun n ↦ RationalFlow.reduce p
        (GeneratedRelation.rateJet data raw n)) :=
  RationalFlow.reduce_logDerivativeJetRecurrence
    data.prime
    (GeneratedRelation.denominatorPrimeTo_sourceJet data raw)
    (GeneratedRelation.denominatorPrimeTo_rateJet data raw)
    (GeneratedRelation.logDerivativeJetRecurrence_relation data raw)

/-- A moment-ready corrected relation forces the selected reduced
logarithmic-rate jet to vanish. -/
theorem rateJet_selected_prime_sq
    {p M : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (s : ℤ) (H B : ℤ[X])
    (hs : ((p : ℤ) ^ 2) ∣ s - 1)
    (hfactor :
      (RealFlow.relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C s *
            RealFlow.relationDenominator data raw =
        Polynomial.cyclotomic p ℤ * B)
    (heval :
      ((p : ℤ) ^ 2) ∣
        ((RealFlow.relationNumerator data raw -
            Polynomial.C ((p : ℤ) ^ 2) * H) -
            Polynomial.C s *
              RealFlow.relationDenominator data raw).eval 1)
    (hMpos : 0 < M) (hMlt : M < p - 1) :
    RationalFlow.reduce p
        (GeneratedRelation.rateJet data raw (p * M - 1)) = 0 := by
  apply Flow.polynomial_quotient_logDerivative_selected_prime_sq
    data.prime hMpos hMlt
    (RealFlow.relationNumerator data raw -
      Polynomial.C ((p : ℤ) ^ 2) * H)
    (RealFlow.relationDenominator data raw) B s
    hfactor heval
    (corrected_scaled_polynomial_quotientJetRecurrence
      data raw s H hs)
    (corrected_scaled_denominator_moment_zero_isUnit
      data raw s hs)
    (reduced_sourceJet_zero data raw)
    (fun n hn _ ↦
      reduced_sourceJet_eq_quotientJet_of_pos data raw hn)
    (reduced_logDerivativeJetRecurrence data raw)

/-- The same selected jet has prime-integral denominator and
prime-square-divisible rational numerator. -/
theorem rateJet_selected_prime_integral_and_num_sq
    {p M : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) (s : ℤ) (H B : ℤ[X])
    (hs : ((p : ℤ) ^ 2) ∣ s - 1)
    (hfactor :
      (RealFlow.relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C s *
            RealFlow.relationDenominator data raw =
        Polynomial.cyclotomic p ℤ * B)
    (heval :
      ((p : ℤ) ^ 2) ∣
        ((RealFlow.relationNumerator data raw -
            Polynomial.C ((p : ℤ) ^ 2) * H) -
            Polynomial.C s *
              RealFlow.relationDenominator data raw).eval 1)
    (hMpos : 0 < M) (hMlt : M < p - 1) :
    Bernoulli.DenominatorPrimeTo p
        (GeneratedRelation.rateJet data raw (p * M - 1)) ∧
      (p : ℤ) ^ 2 ∣
        (GeneratedRelation.rateJet data raw (p * M - 1)).num := by
  have hprimeTo :=
    GeneratedRelation.denominatorPrimeTo_rateJet data raw (p * M - 1)
  exact ⟨hprimeTo,
    (RationalFlow.reduce_eq_zero_iff data.prime hprimeTo).mp
      (rateJet_selected_prime_sq data raw s H B hs hfactor heval
        hMpos hMlt)⟩

end Composition

end Fermat.Conservation.Credit.RateFlow
