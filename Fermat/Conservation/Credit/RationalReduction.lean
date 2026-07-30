/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Prime-square reduction of rational flow jets

This file reduces rational numbers whose reduced denominators are prime to
`p` into `ZMod (p²)`.  It proves the ring-operation laws needed to carry
rational quotient and logarithmic-derivative Euler-jet recurrences into the
nonlinear modular flow, together with uniqueness lemmas that identify the
resulting solutions.

The construction is generic over the prime and reuses the pole-safe
denominator predicate from the Bernoulli layer.
-/
import Fermat.Conservation.Credit.Bernoulli
import Fermat.Conservation.Credit.NonlinearFlow

open scoped BigOperators

namespace Fermat.Conservation.Credit.RationalFlow

open Bernoulli
open Fermat.Conservation.Credit.Flow

/-! ## Prime-integral denominators -/

theorem denominatorPrimeTo_zero {p : ℕ} (hp : p.Prime) :
    DenominatorPrimeTo p 0 := by
  simp [DenominatorPrimeTo, hp.ne_one]

theorem denominatorPrimeTo_one {p : ℕ} (hp : p.Prime) :
    DenominatorPrimeTo p 1 := by
  simp [DenominatorPrimeTo, hp.ne_one]

theorem denominatorPrimeTo_neg {p : ℕ} {q : ℚ}
    (hq : DenominatorPrimeTo p q) :
    DenominatorPrimeTo p (-q) := by
  simpa [DenominatorPrimeTo] using hq

theorem denominatorPrimeTo_add {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr : DenominatorPrimeTo p r) :
    DenominatorPrimeTo p (q + r) := by
  intro hsum
  have hprod : p ∣ q.den * r.den :=
    dvd_trans hsum (Rat.add_den_dvd q r)
  exact (hp.dvd_mul.mp hprod).elim hq hr

theorem denominatorPrimeTo_mul {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr : DenominatorPrimeTo p r) :
    DenominatorPrimeTo p (q * r) := by
  intro hmul
  have hprod : p ∣ q.den * r.den :=
    dvd_trans hmul (Rat.mul_den_dvd q r)
  exact (hp.dvd_mul.mp hprod).elim hq hr

theorem denominatorPrimeTo_sub {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr : DenominatorPrimeTo p r) :
    DenominatorPrimeTo p (q - r) := by
  simpa [sub_eq_add_neg] using
    denominatorPrimeTo_add hp hq (denominatorPrimeTo_neg hr)

theorem denominatorPrimeTo_natCast {p : ℕ} (hp : p.Prime)
    (n : ℕ) :
    DenominatorPrimeTo p (n : ℚ) := by
  simp [DenominatorPrimeTo, hp.ne_one]

theorem denominatorPrimeTo_intCast {p : ℕ} (hp : p.Prime)
    (z : ℤ) :
    DenominatorPrimeTo p (z : ℚ) := by
  simp [DenominatorPrimeTo, hp.ne_one]

/-- The inverse of a nonzero rational has denominator prime to `p` when
the original reduced numerator is prime to `p`. -/
theorem denominatorPrimeTo_inv_of_num_not_dvd
    {p : ℕ} {q : ℚ}
    (hq0 : q ≠ 0) (hnum : ¬(p : ℤ) ∣ q.num) :
    DenominatorPrimeTo p q⁻¹ := by
  rw [DenominatorPrimeTo, Rat.den_inv_of_ne_zero hq0,
    ← Int.natCast_dvd]
  exact hnum

/-- Division preserves prime-to-`p` denominators when the divisor's inverse
has a prime-to-`p` denominator. -/
theorem denominatorPrimeTo_div {p : ℕ} (hp : p.Prime)
    {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hrInv : DenominatorPrimeTo p r⁻¹) :
    DenominatorPrimeTo p (q / r) := by
  rw [div_eq_mul_inv]
  exact denominatorPrimeTo_mul hp hq hrInv

/-- Numerator form of denominator closure under division. -/
theorem denominatorPrimeTo_div_of_num_not_dvd
    {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr0 : r ≠ 0) (hrNum : ¬(p : ℤ) ∣ r.num) :
    DenominatorPrimeTo p (q / r) :=
  denominatorPrimeTo_div hp hq
    (denominatorPrimeTo_inv_of_num_not_dvd hr0 hrNum)

/-- A finite sum of rationals with prime-to-`p` denominators again has a
prime-to-`p` denominator. -/
theorem denominatorPrimeTo_finsetSum {p : ℕ} (hp : p.Prime)
    {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, DenominatorPrimeTo p (f i)) :
    DenominatorPrimeTo p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using denominatorPrimeTo_zero hp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact denominatorPrimeTo_add hp
        (hf a (by simp))
        (ih fun i hi ↦ hf i (by simp [hi]))

/-! ## Canonical reduction modulo `p²` -/

/-- The reduced denominator is a unit modulo `p²`. -/
theorem denominator_isUnit {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : DenominatorPrimeTo p q) :
    IsUnit (q.den : ZMod (p ^ 2)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hq

/-- Canonical reduction of a rational into `ZMod (p²)`.

The definition is total; its ring laws require a proof that the relevant
reduced denominators are prime to `p`.
-/
def reduce (p : ℕ) (q : ℚ) : ZMod (p ^ 2) :=
  (q.num : ZMod (p ^ 2)) * (q.den : ZMod (p ^ 2))⁻¹

/-- Clearing the unit denominator characterizes rational reduction. -/
theorem denominator_mul_reduce {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : DenominatorPrimeTo p q) :
    (q.den : ZMod (p ^ 2)) * reduce p q =
      (q.num : ZMod (p ^ 2)) := by
  have hu := denominator_isUnit hp hq
  rw [reduce]
  calc
    (q.den : ZMod (p ^ 2)) *
          ((q.num : ZMod (p ^ 2)) *
            (q.den : ZMod (p ^ 2))⁻¹) =
        (q.num : ZMod (p ^ 2)) *
          ((q.den : ZMod (p ^ 2)) *
            (q.den : ZMod (p ^ 2))⁻¹) := by
              ring
    _ = q.num := by
      rw [ZMod.mul_inv_of_unit _ hu, mul_one]

/-- Uniqueness after clearing the reduced denominator. -/
theorem reduce_eq_of_denominator_mul_eq {p : ℕ} (hp : p.Prime)
    {q : ℚ} (hq : DenominatorPrimeTo p q)
    {x : ZMod (p ^ 2)}
    (hx : (q.den : ZMod (p ^ 2)) * x =
      (q.num : ZMod (p ^ 2))) :
    reduce p q = x := by
  apply (denominator_isUnit hp hq).mul_left_cancel
  calc
    (q.den : ZMod (p ^ 2)) * reduce p q =
        (q.num : ZMod (p ^ 2)) :=
      denominator_mul_reduce hp hq
    _ = (q.den : ZMod (p ^ 2)) * x := hx.symm

/-- A prime-integral rational vanishes modulo `p²` exactly when its reduced
numerator is divisible by `p²`. -/
theorem reduce_eq_zero_iff {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : DenominatorPrimeTo p q) :
    reduce p q = 0 ↔ (p : ℤ) ^ 2 ∣ q.num := by
  constructor
  · intro hz
    have hnum : (q.num : ZMod (p ^ 2)) = 0 := by
      rw [← denominator_mul_reduce hp hq, hz, mul_zero]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hnum
    simpa using hnum
  · intro hnum
    apply reduce_eq_of_denominator_mul_eq hp hq
    rw [mul_zero]
    symm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using hnum

/-! ## Ring-operation compatibility -/

theorem reduce_neg {p : ℕ} (q : ℚ) :
    reduce p (-q) = -reduce p q := by
  simp [reduce]

theorem reduce_intCast {p : ℕ} (z : ℤ) :
    reduce p (z : ℚ) = (z : ZMod (p ^ 2)) := by
  simp [reduce]

theorem reduce_natCast {p : ℕ} (n : ℕ) :
    reduce p (n : ℚ) = (n : ZMod (p ^ 2)) := by
  simp [reduce]

theorem reduce_zero {p : ℕ} :
    reduce p 0 = 0 := by
  simpa using reduce_intCast (p := p) 0

theorem reduce_one {p : ℕ} :
    reduce p 1 = 1 := by
  simpa using reduce_intCast (p := p) 1

theorem reduce_add {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr : DenominatorPrimeTo p r) :
    reduce p (q + r) = reduce p q + reduce p r := by
  have hsum := denominatorPrimeTo_add hp hq hr
  apply reduce_eq_of_denominator_mul_eq hp hsum
  have hqspec := denominator_mul_reduce hp hq
  have hrspec := denominator_mul_reduce hp hr
  have hcross := congrArg
    (fun z : ℤ ↦ (z : ZMod (p ^ 2)))
    (Rat.add_num_den' q r)
  push_cast at hcross
  have hu :
      IsUnit ((q.den : ZMod (p ^ 2)) *
        (r.den : ZMod (p ^ 2))) :=
    (denominator_isUnit hp hq).mul
      (denominator_isUnit hp hr)
  apply hu.mul_left_cancel
  calc
    ((q.den : ZMod (p ^ 2)) *
        (r.den : ZMod (p ^ 2))) *
          (((q + r).den : ZMod (p ^ 2)) *
            (reduce p q + reduce p r)) =
        ((q + r).den : ZMod (p ^ 2)) *
          ((r.den : ZMod (p ^ 2)) *
              ((q.den : ZMod (p ^ 2)) * reduce p q) +
            (q.den : ZMod (p ^ 2)) *
              ((r.den : ZMod (p ^ 2)) * reduce p r)) := by
                ring
    _ = ((q + r).den : ZMod (p ^ 2)) *
          ((r.den : ZMod (p ^ 2)) *
              (q.num : ZMod (p ^ 2)) +
            (q.den : ZMod (p ^ 2)) *
              (r.num : ZMod (p ^ 2))) := by
                rw [hqspec, hrspec]
    _ = ((q + r).num : ZMod (p ^ 2)) *
          (q.den : ZMod (p ^ 2)) *
          (r.den : ZMod (p ^ 2)) := by
            linear_combination -hcross
    _ = ((q.den : ZMod (p ^ 2)) *
          (r.den : ZMod (p ^ 2))) * (q + r).num := by
            ring

theorem reduce_mul {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr : DenominatorPrimeTo p r) :
    reduce p (q * r) = reduce p q * reduce p r := by
  have hmul := denominatorPrimeTo_mul hp hq hr
  apply reduce_eq_of_denominator_mul_eq hp hmul
  have hqspec := denominator_mul_reduce hp hq
  have hrspec := denominator_mul_reduce hp hr
  have hcross := congrArg
    (fun z : ℤ ↦ (z : ZMod (p ^ 2)))
    (Rat.mul_num_den' q r)
  push_cast at hcross
  have hu :
      IsUnit ((q.den : ZMod (p ^ 2)) *
        (r.den : ZMod (p ^ 2))) :=
    (denominator_isUnit hp hq).mul
      (denominator_isUnit hp hr)
  apply hu.mul_left_cancel
  calc
    ((q.den : ZMod (p ^ 2)) *
        (r.den : ZMod (p ^ 2))) *
          (((q * r).den : ZMod (p ^ 2)) *
            (reduce p q * reduce p r)) =
        ((q * r).den : ZMod (p ^ 2)) *
          (((q.den : ZMod (p ^ 2)) * reduce p q) *
            ((r.den : ZMod (p ^ 2)) * reduce p r)) := by
              ring
    _ = ((q * r).den : ZMod (p ^ 2)) *
          ((q.num : ZMod (p ^ 2)) *
            (r.num : ZMod (p ^ 2))) := by
          rw [hqspec, hrspec]
    _ = ((q * r).num : ZMod (p ^ 2)) *
          (q.den : ZMod (p ^ 2)) *
          (r.den : ZMod (p ^ 2)) := by
            linear_combination -hcross
    _ = ((q.den : ZMod (p ^ 2)) *
          (r.den : ZMod (p ^ 2))) * (q * r).num := by
            ring

theorem reduce_sub {p : ℕ} (hp : p.Prime) {q r : ℚ}
    (hq : DenominatorPrimeTo p q)
    (hr : DenominatorPrimeTo p r) :
    reduce p (q - r) = reduce p q - reduce p r := by
  simpa [sub_eq_add_neg, reduce_neg] using
    reduce_add hp hq (denominatorPrimeTo_neg hr)

theorem reduce_finsetSum {p : ℕ} (hp : p.Prime)
    {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, DenominatorPrimeTo p (f i)) :
    reduce p (∑ i ∈ s, f i) =
      ∑ i ∈ s, reduce p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [reduce_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [reduce_add hp (hf a (by simp))
        (denominatorPrimeTo_finsetSum hp s f
          fun i hi ↦ hf i (by simp [hi]))]
      rw [ih fun i hi ↦ hf i (by simp [hi])]

/-! ## Reduction of nonlinear Euler-jet recurrences -/

/-- A quotient-jet recurrence preserves prime-to-`p` denominators.

The inverse hypothesis is stated directly because it is often immediate
from normalization; `denominatorPrimeTo_inv_of_num_not_dvd` supplies it
from a numerator certificate when needed.
-/
theorem denominatorPrimeTo_quotient_of_recurrence
    {p : ℕ} (hp : p.Prime)
    {numerator denominator quotient : ℕ → ℚ}
    (hrec :
      IsQuotientJetRecurrence numerator denominator quotient)
    (hnum : ∀ n, DenominatorPrimeTo p (numerator n))
    (hden : ∀ n, DenominatorPrimeTo p (denominator n))
    (hdenZero : denominator 0 ≠ 0)
    (hdenInv : DenominatorPrimeTo p (denominator 0)⁻¹) :
    ∀ n, DenominatorPrimeTo p (quotient n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hrecn := hrec n
      rw [Finset.sum_range_succ] at hrecn
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
        one_mul] at hrecn
      have hrest :
          DenominatorPrimeTo p
            (∑ k ∈ Finset.range n,
              (n.choose k : ℚ) *
                denominator (n - k) * quotient k) := by
        apply denominatorPrimeTo_finsetSum hp
        intro k hk
        exact
          denominatorPrimeTo_mul hp
            (denominatorPrimeTo_mul hp
              (denominatorPrimeTo_natCast hp (n.choose k))
              (hden (n - k)))
            (ih k (Finset.mem_range.mp hk))
      have hdiff :
          DenominatorPrimeTo p
            (numerator n -
              ∑ k ∈ Finset.range n,
                (n.choose k : ℚ) *
                  denominator (n - k) * quotient k) :=
        denominatorPrimeTo_sub hp (hnum n) hrest
      have hsolve :
          denominator 0 * quotient n =
            numerator n -
              ∑ k ∈ Finset.range n,
                (n.choose k : ℚ) *
                  denominator (n - k) * quotient k := by
        linear_combination -hrecn
      have hformula :
          quotient n =
            (denominator 0)⁻¹ *
              (numerator n -
                ∑ k ∈ Finset.range n,
                  (n.choose k : ℚ) *
                    denominator (n - k) * quotient k) := by
        calc
          quotient n =
              (denominator 0)⁻¹ *
                (denominator 0 * quotient n) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hdenZero,
                    one_mul]
          _ = (denominator 0)⁻¹ *
                (numerator n -
                  ∑ k ∈ Finset.range n,
                    (n.choose k : ℚ) *
                      denominator (n - k) * quotient k) := by
                rw [hsolve]
      rw [hformula]
      exact denominatorPrimeTo_mul hp hdenInv hdiff

/-- A logarithmic-derivative recurrence preserves prime-to-`p`
denominators when the source and the inverse of its constant jet do. -/
theorem denominatorPrimeTo_logDerivative_of_recurrence
    {p : ℕ} (hp : p.Prime)
    {source logDerivative : ℕ → ℚ}
    (hrec :
      IsLogDerivativeJetRecurrence source logDerivative)
    (hsource : ∀ n, DenominatorPrimeTo p (source n))
    (hsourceZero : source 0 ≠ 0)
    (hsourceInv : DenominatorPrimeTo p (source 0)⁻¹) :
    ∀ n, DenominatorPrimeTo p (logDerivative n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hrecn := hrec n
      rw [Finset.sum_range_succ] at hrecn
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
        one_mul] at hrecn
      have hrest :
          DenominatorPrimeTo p
            (∑ k ∈ Finset.range n,
              (n.choose k : ℚ) *
                source (n - k) * logDerivative k) := by
        apply denominatorPrimeTo_finsetSum hp
        intro k hk
        exact
          denominatorPrimeTo_mul hp
            (denominatorPrimeTo_mul hp
              (denominatorPrimeTo_natCast hp (n.choose k))
              (hsource (n - k)))
            (ih k (Finset.mem_range.mp hk))
      have hdiff :
          DenominatorPrimeTo p
            (source (n + 1) -
              ∑ k ∈ Finset.range n,
                (n.choose k : ℚ) *
                  source (n - k) * logDerivative k) :=
        denominatorPrimeTo_sub hp (hsource (n + 1)) hrest
      have hsolve :
          source 0 * logDerivative n =
            source (n + 1) -
              ∑ k ∈ Finset.range n,
                (n.choose k : ℚ) *
                  source (n - k) * logDerivative k := by
        linear_combination -hrecn
      have hformula :
          logDerivative n =
            (source 0)⁻¹ *
              (source (n + 1) -
                ∑ k ∈ Finset.range n,
                  (n.choose k : ℚ) *
                    source (n - k) * logDerivative k) := by
        calc
          logDerivative n =
              (source 0)⁻¹ * (source 0 * logDerivative n) := by
                rw [← mul_assoc, inv_mul_cancel₀ hsourceZero,
                  one_mul]
          _ = (source 0)⁻¹ *
                (source (n + 1) -
                  ∑ k ∈ Finset.range n,
                    (n.choose k : ℚ) *
                      source (n - k) * logDerivative k) := by
                rw [hsolve]
      rw [hformula]
      exact denominatorPrimeTo_mul hp hsourceInv hdiff

/-- A rational quotient-jet recurrence reduces to the `ZMod (p²)`
recurrence used by the nonlinear flow. -/
theorem reduce_quotientJetRecurrence
    {p : ℕ} (hp : p.Prime)
    {numerator denominator quotient : ℕ → ℚ}
    (hden : ∀ n, DenominatorPrimeTo p (denominator n))
    (hquot : ∀ n, DenominatorPrimeTo p (quotient n))
    (hrec :
      IsQuotientJetRecurrence numerator denominator quotient) :
    IsQuotientJetRecurrence
      (fun n ↦ reduce p (numerator n))
      (fun n ↦ reduce p (denominator n))
      (fun n ↦ reduce p (quotient n)) := by
  intro n
  calc
    reduce p (numerator n) =
        reduce p
          (∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℚ) *
              denominator (n - k) * quotient k) := by
                rw [hrec n]
    _ = ∑ k ∈ Finset.range (n + 1),
          reduce p
            ((n.choose k : ℚ) *
              denominator (n - k) * quotient k) := by
          apply reduce_finsetSum hp
          intro k _
          exact
            denominatorPrimeTo_mul hp
              (denominatorPrimeTo_mul hp
                (denominatorPrimeTo_natCast hp (n.choose k))
                (hden (n - k)))
              (hquot k)
    _ = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ZMod (p ^ 2)) *
            reduce p (denominator (n - k)) *
            reduce p (quotient k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [reduce_mul hp
            (denominatorPrimeTo_mul hp
              (denominatorPrimeTo_natCast hp (n.choose k))
              (hden (n - k)))
            (hquot k)]
          rw [reduce_mul hp
            (denominatorPrimeTo_natCast hp (n.choose k))
            (hden (n - k))]
          rw [reduce_natCast]

/-- A rational logarithmic-derivative jet recurrence reduces to the
`ZMod (p²)` recurrence used by the nonlinear flow. -/
theorem reduce_logDerivativeJetRecurrence
    {p : ℕ} (hp : p.Prime)
    {source logDerivative : ℕ → ℚ}
    (hsource : ∀ n, DenominatorPrimeTo p (source n))
    (hlog : ∀ n, DenominatorPrimeTo p (logDerivative n))
    (hrec :
      IsLogDerivativeJetRecurrence source logDerivative) :
    IsLogDerivativeJetRecurrence
      (fun n ↦ reduce p (source n))
      (fun n ↦ reduce p (logDerivative n)) := by
  intro n
  calc
    reduce p (source (n + 1)) =
        reduce p
          (∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℚ) *
              source (n - k) * logDerivative k) := by
                rw [hrec n]
    _ = ∑ k ∈ Finset.range (n + 1),
          reduce p
            ((n.choose k : ℚ) *
              source (n - k) * logDerivative k) := by
          apply reduce_finsetSum hp
          intro k _
          exact
            denominatorPrimeTo_mul hp
              (denominatorPrimeTo_mul hp
                (denominatorPrimeTo_natCast hp (n.choose k))
                (hsource (n - k)))
              (hlog k)
    _ = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ZMod (p ^ 2)) *
            reduce p (source (n - k)) *
            reduce p (logDerivative k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [reduce_mul hp
            (denominatorPrimeTo_mul hp
              (denominatorPrimeTo_natCast hp (n.choose k))
              (hsource (n - k)))
            (hlog k)]
          rw [reduce_mul hp
            (denominatorPrimeTo_natCast hp (n.choose k))
            (hsource (n - k))]
          rw [reduce_natCast]

/-! ## Recurrence uniqueness and comparison -/

/-- Quotient Euler jets are unique when the denominator's constant jet is
a unit. -/
theorem quotientJetRecurrence_unique
    {R : Type*} [CommRing R]
    {numerator denominator quotient₁ quotient₂ : ℕ → R}
    (hunit : IsUnit (denominator 0))
    (hrec₁ :
      IsQuotientJetRecurrence numerator denominator quotient₁)
    (hrec₂ :
      IsQuotientJetRecurrence numerator denominator quotient₂) :
    quotient₁ = quotient₂ := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have h₁ := hrec₁ n
      have h₂ := hrec₂ n
      rw [Finset.sum_range_succ] at h₁ h₂
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
        one_mul] at h₁ h₂
      have hrest :
          (∑ k ∈ Finset.range n,
            (n.choose k : R) *
              denominator (n - k) * quotient₁ k) =
          ∑ k ∈ Finset.range n,
            (n.choose k : R) *
              denominator (n - k) * quotient₂ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      apply hunit.mul_left_cancel
      rw [hrest] at h₁
      linear_combination h₂ - h₁

/-- Logarithmic-derivative Euler jets are unique when the source's constant
jet is a unit. -/
theorem logDerivativeJetRecurrence_unique
    {R : Type*} [CommRing R]
    {source logDerivative₁ logDerivative₂ : ℕ → R}
    (hunit : IsUnit (source 0))
    (hrec₁ :
      IsLogDerivativeJetRecurrence source logDerivative₁)
    (hrec₂ :
      IsLogDerivativeJetRecurrence source logDerivative₂) :
    logDerivative₁ = logDerivative₂ := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have h₁ := hrec₁ n
      have h₂ := hrec₂ n
      rw [Finset.sum_range_succ] at h₁ h₂
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self,
        one_mul] at h₁ h₂
      have hrest :
          (∑ k ∈ Finset.range n,
            (n.choose k : R) * source (n - k) *
              logDerivative₁ k) =
          ∑ k ∈ Finset.range n,
            (n.choose k : R) * source (n - k) *
              logDerivative₂ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      apply hunit.mul_left_cancel
      rw [hrest] at h₁
      linear_combination h₂ - h₁

/-- Any modular quotient-jet solution equals the pointwise reduction of
the rational solution. -/
theorem reduced_quotient_eq_of_recurrence
    {p : ℕ} (hp : p.Prime)
    {numerator denominator quotient : ℕ → ℚ}
    {modularQuotient : ℕ → ZMod (p ^ 2)}
    (hden : ∀ n, DenominatorPrimeTo p (denominator n))
    (hquot : ∀ n, DenominatorPrimeTo p (quotient n))
    (hrat :
      IsQuotientJetRecurrence numerator denominator quotient)
    (hmod :
      IsQuotientJetRecurrence
        (fun n ↦ reduce p (numerator n))
        (fun n ↦ reduce p (denominator n))
        modularQuotient)
    (hunit : IsUnit (reduce p (denominator 0))) :
    (fun n ↦ reduce p (quotient n)) = modularQuotient :=
  quotientJetRecurrence_unique hunit
    (reduce_quotientJetRecurrence hp hden hquot hrat) hmod

/-- Any modular logarithmic-jet solution equals the pointwise reduction of
the rational logarithmic-jet solution. -/
theorem reduced_logDerivative_eq_of_recurrence
    {p : ℕ} (hp : p.Prime)
    {source logDerivative : ℕ → ℚ}
    {modularLogDerivative : ℕ → ZMod (p ^ 2)}
    (hsource : ∀ n, DenominatorPrimeTo p (source n))
    (hlog : ∀ n, DenominatorPrimeTo p (logDerivative n))
    (hrat :
      IsLogDerivativeJetRecurrence source logDerivative)
    (hmod :
      IsLogDerivativeJetRecurrence
        (fun n ↦ reduce p (source n))
        modularLogDerivative)
    (hunit : IsUnit (reduce p (source 0))) :
    (fun n ↦ reduce p (logDerivative n)) =
      modularLogDerivative :=
  logDerivativeJetRecurrence_unique hunit
    (reduce_logDerivativeJetRecurrence hp hsource hlog hrat) hmod

/-- Comparison specialized to a source normalized to constant jet one. -/
theorem reduced_logDerivative_eq_of_recurrence_of_source_zero_eq_one
    {p : ℕ} (hp : p.Prime)
    {source logDerivative : ℕ → ℚ}
    {modularLogDerivative : ℕ → ZMod (p ^ 2)}
    (hsource : ∀ n, DenominatorPrimeTo p (source n))
    (hlog : ∀ n, DenominatorPrimeTo p (logDerivative n))
    (hsourceZero : source 0 = 1)
    (hrat :
      IsLogDerivativeJetRecurrence source logDerivative)
    (hmod :
      IsLogDerivativeJetRecurrence
        (fun n ↦ reduce p (source n))
        modularLogDerivative) :
    (fun n ↦ reduce p (logDerivative n)) =
      modularLogDerivative := by
  apply reduced_logDerivative_eq_of_recurrence hp
    hsource hlog hrat hmod
  rw [hsourceZero, reduce_one]
  exact isUnit_one

end Fermat.Conservation.Credit.RationalFlow
