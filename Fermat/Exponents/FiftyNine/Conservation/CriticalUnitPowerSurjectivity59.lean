/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Deep principal units are 59th powers

This module proves the local analytic input needed to remove the harmless
`U_60` ambiguity from the critical norm quotient.  In the completed
cyclotomic integer ring, every element congruent to one modulo `lambda^60`
is a 59th power.

The proof is an explicit rescaled Hensel argument.  Exact ramification gives
`(59) = (lambda)^58`.  After writing

`u - 1 = 59 * lambda^2 * b`

and substituting `x = 1 + lambda^2 * z`, division of `x^59 - u` by
`59 * lambda^2` leaves a polynomial whose linear coefficient is one and
whose other nonconstant coefficients lie in the lambda ideal.  A
monic-free form of the standard adic Newton proof then supplies its root.

No local reciprocity, norm-filtration theorem, or non-norm assertion is used.
-/
import Fermat.Exponents.FiftyNine.Conservation.AdicCompleteValuedInteger59
import Fermat.Exponents.FiftyNine.Conservation.CriticalUnitQuotient59
import Fermat.Exponents.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic

open scoped NumberField Ring Topology Valued WithZero
open Polynomial

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

namespace Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59

open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59
open Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

/-! ## A monic-free adic Newton lemma

Mathlib's construction of `IsAdicComplete.henselianRing` proves the following
statement internally and never uses its public `Monic` parameter.  We expose
exactly that stronger Newton statement here because the rescaled polynomial
has unit linear coefficient and nonunit leading coefficient.
-/

/-- A simple approximate root of an arbitrary polynomial over an adically
complete ring lifts to an exact root. -/
theorem exists_isRoot_of_isAdicComplete
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (hvalue : f.eval a₀ ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b =>
    b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) =
      c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at hvalue ⊢
      exact (ih.eval f).trans hvalue
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I
      (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! hderiv using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! hvalue
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum,
        sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, taylor_coeff_zero,
          taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one,
          add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have hpow : n + 2 ≤ i * (n + 1) := by
          trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hpow ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow
          ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have hcauchy : ∀ m n, m ≤ n →
      c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (hcauchy _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one,
      sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ hvalue

/-! ## The rescaled 59th-root polynomial -/

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

private abbrev R59 := ValuedIntegerRing 59 K
private abbrev I59 : Ideal (R59 K) := lambdaIdeal 59 K
private abbrev pi59 : R59 K := valuedCyclotomicLambdaInteger 59 K

/-- The integral quotient `choose(59,k)/59`. -/
private def dividedChoose59 (k : ℕ) : ℕ := Nat.choose 59 k / 59

/-- The polynomial obtained from `(1 + lambda^2 X)^59-u` after dividing by
`59*lambda^2`.  The element `q` represents `lambda^116/59`, while `b`
represents `(u-1)/(59*lambda^2)`. -/
private def rootPolynomial59 (b q : R59 K) : (R59 K)[X] :=
  X +
    ∑ k ∈ Finset.Icc 2 58,
      C ((dividedChoose59 k : R59 K) * (pi59 K) ^ (2 * k - 2)) * X ^ k +
    C q * X ^ 59 - C b

private theorem rootPolynomial59_eval (b q z : R59 K) :
    (rootPolynomial59 K b q).eval z =
      z +
        ∑ k ∈ Finset.Icc 2 58,
          (dividedChoose59 k : R59 K) *
            (pi59 K) ^ (2 * k - 2) * z ^ k +
        q * z ^ 59 - b := by
  rw [rootPolynomial59, eval_sub, eval_add, eval_add, eval_X,
    eval_mul, eval_C, eval_X_pow, eval_C]
  have hsum :
      Polynomial.eval z
          (∑ k ∈ Finset.Icc 2 58,
            C ((dividedChoose59 k : R59 K) *
              (pi59 K) ^ (2 * k - 2)) * X ^ k) =
        ∑ k ∈ Finset.Icc 2 58,
          (dividedChoose59 k : R59 K) *
            (pi59 K) ^ (2 * k - 2) * z ^ k := by
    change (evalRingHom z)
        (∑ k ∈ Finset.Icc 2 58,
          C ((dividedChoose59 k : R59 K) *
            (pi59 K) ^ (2 * k - 2)) * X ^ k) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp
  rw [hsum]

private theorem rootPolynomial59_value_mem (b q : R59 K)
    (hq : q ∈ I59 K) :
    (rootPolynomial59 K b q).eval b ∈ I59 K := by
  rw [rootPolynomial59_eval]
  have hsum :
      (∑ k ∈ Finset.Icc 2 58,
        (dividedChoose59 k : R59 K) *
          (pi59 K) ^ (2 * k - 2) * b ^ k) ∈ I59 K := by
    refine Submodule.sum_mem _ ?_
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hpi : (pi59 K) ^ (2 * k - 2) ∈ I59 K := by
      have hpos : 0 < 2 * k - 2 := by omega
      exact Ideal.pow_le_self (Nat.ne_of_gt hpos)
        (Ideal.pow_mem_pow
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal
            (p := 59) (K := K)) _)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hpi)
  have hqterm : q * b ^ 59 ∈ I59 K :=
    Ideal.mul_mem_right _ _ hq
  convert Ideal.add_mem (I59 K) hsum hqterm using 1
  all_goals ring

private theorem rootPolynomial59_derivative_eval (b q : R59 K) :
    (rootPolynomial59 K b q).derivative.eval b =
      1 +
        ∑ k ∈ Finset.Icc 2 58,
          ((dividedChoose59 k : R59 K) *
            (pi59 K) ^ (2 * k - 2)) *
              ((k : R59 K) * b ^ (k - 1)) +
        q * ((59 : R59 K) * b ^ 58) := by
  rw [rootPolynomial59]
  simp only [derivative_add, derivative_sub, derivative_X,
    derivative_C, derivative_mul, derivative_X_pow, zero_mul,
    eval_add, eval_sub, eval_one, eval_zero, eval_mul, eval_C,
    eval_X_pow, Nat.reduceSubDiff]
  have hsum :
      Polynomial.eval b
          (derivative
            (∑ k ∈ Finset.Icc 2 58,
              C ((dividedChoose59 k : R59 K) *
                (pi59 K) ^ (2 * k - 2)) * X ^ k)) =
        ∑ k ∈ Finset.Icc 2 58,
          ((dividedChoose59 k : R59 K) *
            (pi59 K) ^ (2 * k - 2)) *
              ((k : R59 K) * b ^ (k - 1)) := by
    rw [map_sum]
    change (evalRingHom b) (∑ k ∈ Finset.Icc 2 58,
      derivative
        (C ((dividedChoose59 k : R59 K) *
          (pi59 K) ^ (2 * k - 2)) * X ^ k)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_X_pow]
    simp
  rw [hsum]
  ring

private theorem rootPolynomial59_derivative_eval_mod (b q : R59 K)
    (hq : q ∈ I59 K) :
    Ideal.Quotient.mk (I59 K)
        ((rootPolynomial59 K b q).derivative.eval b) = 1 := by
  rw [← sub_eq_zero]
  change Ideal.Quotient.mk (I59 K)
      ((rootPolynomial59 K b q).derivative.eval b) -
        Ideal.Quotient.mk (I59 K) 1 = 0
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  rw [rootPolynomial59_derivative_eval]
  have hsum :
      (∑ k ∈ Finset.Icc 2 58,
        ((dividedChoose59 k : R59 K) *
          (pi59 K) ^ (2 * k - 2)) *
            ((k : R59 K) * b ^ (k - 1))) ∈ I59 K := by
    refine Submodule.sum_mem _ ?_
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hpi : (pi59 K) ^ (2 * k - 2) ∈ I59 K := by
      have hpos : 0 < 2 * k - 2 := by omega
      exact Ideal.pow_le_self (Nat.ne_of_gt hpos)
        (Ideal.pow_mem_pow
          (valuedCyclotomicLambdaInteger_mem_lambdaIdeal
            (p := 59) (K := K)) _)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hpi)
  have hqterm : q * ((59 : R59 K) * b ^ 58) ∈ I59 K :=
    Ideal.mul_mem_right _ _ hq
  convert Ideal.add_mem (I59 K) hsum hqterm using 1
  all_goals ring

private theorem rootPolynomial59_derivative_isUnit (b q : R59 K)
    (hq : q ∈ I59 K) :
    IsUnit (Ideal.Quotient.mk (I59 K)
      ((rootPolynomial59 K b q).derivative.eval b)) := by
  rw [rootPolynomial59_derivative_eval_mod K b q hq]
  exact isUnit_one

/- The fixed finite binomial identity used after Hensel lifting. -/
private theorem rootPolynomial59_identity (b q z : R59 K)
    (hq : (59 : R59 K) * q = (pi59 K) ^ 116) :
    (59 : R59 K) * (pi59 K) ^ 2 *
        (rootPolynomial59 K b q).eval z =
      (1 + (pi59 K) ^ 2 * z) ^ 59 -
        (1 + (59 : R59 K) * (pi59 K) ^ 2 * b) := by
  rw [rootPolynomial59_eval]
  norm_num [dividedChoose59, Nat.choose, Finset.sum_Icc_succ_top]
  linear_combination ((pi59 K) ^ 2 * z ^ 59) * hq

/-- Every integer congruent to one modulo `lambda^60` is a 59th power in
the completed valuation integer ring. -/
theorem exists_pow59_eq_of_sub_one_mem_lambdaIdeal_pow_sixty
    (u : R59 K) (hu : u - 1 ∈ (I59 K) ^ 60) :
    ∃ x : R59 K, x ^ 59 = u := by
  have hu' : u - 1 ∈
      (I59 K) ^ (1 * (59 - 1) + 2) := by
    norm_num
    exact hu
  obtain ⟨y, hy, hpy⟩ :=
    exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
      (p := 59) (K := K) 1 2 hu'
  have hy' : y ∈ Ideal.span ({pi59 K} : Set (R59 K)) ^ 2 := by
    simpa [I59, lambdaIdeal] using hy
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy'
  obtain ⟨b, hb⟩ := hy'
  have hpi116 : (pi59 K) ^ 116 ∈
      (I59 K) ^ (1 * (59 - 1) + 58) := by
    norm_num
    exact valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow
      (p := 59) (K := K) 116
  obtain ⟨q, hqmem, hpq⟩ :=
    exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
      (p := 59) (K := K) 1 58 hpi116
  have hqI : q ∈ I59 K :=
    Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0) hqmem
  obtain ⟨z, hz, -⟩ := exists_isRoot_of_isAdicComplete
    (I59 K) (rootPolynomial59 K b q) b
    (rootPolynomial59_value_mem K b q hqI)
    (rootPolynomial59_derivative_isUnit K b q hqI)
  refine ⟨1 + (pi59 K) ^ 2 * z, ?_⟩
  have hid := rootPolynomial59_identity K b q z (by simpa using hpq)
  rw [hz] at hid
  have hu_eq : u = 1 + (59 : R59 K) * (pi59 K) ^ 2 * b := by
    have hpy' : (59 : R59 K) * y = u - 1 := by simpa using hpy
    rw [hb] at hpy'
    calc
      u = (u - 1) + 1 := by ring
      _ = (59 : R59 K) * ((pi59 K) ^ 2 * b) + 1 := by rw [← hpy']
      _ = 1 + (59 : R59 K) * (pi59 K) ^ 2 * b := by ring
  rw [hu_eq]
  have hid0 : 0 =
      (1 + (pi59 K) ^ 2 * z) ^ 59 -
        (1 + (59 : R59 K) * (pi59 K) ^ 2 * b) := by
    simpa only [mul_zero] using hid
  exact sub_eq_zero.mp hid0.symm

/-! ## Transfer to the field-unit filtration -/

/-- Unit-group form of the integral 59th-root theorem. -/
theorem exists_unit_pow59_eq_of_sub_one_mem_lambdaIdeal_pow_sixty
    (u : (R59 K)ˣ) (hu : (u : R59 K) - 1 ∈ (I59 K) ^ 60) :
    ∃ x : (R59 K)ˣ, x ^ 59 = u := by
  obtain ⟨x, hx⟩ :=
    exists_pow59_eq_of_sub_one_mem_lambdaIdeal_pow_sixty K (u : R59 K) hu
  have hxunit : IsUnit x :=
    (isUnit_pow_iff (by norm_num : (59 : ℕ) ≠ 0)).mp (by
      rw [hx]
      exact u.isUnit)
  refine ⟨hxunit.unit, ?_⟩
  apply Units.ext
  change x ^ 59 = (u : R59 K)
  simpa [hxunit.unit_spec] using hx

/-- The cast equivalence between the pinned KummerCriterion completion and
the Fermat-side completion name. -/
private def valuedCompletionEquivLambdaField59 :
    ValuedCompletion 59 K ≃+* LambdaField59 K :=
  RingEquiv.cast (lambdaPlace59_eq_kummerCriterion K).symm

@[simp]
private theorem valuedCompletionEquivLambdaField59_valuation
    (x : ValuedCompletion 59 K) :
    Valued.v (valuedCompletionEquivLambdaField59 K x) = Valued.v x := by
  unfold valuedCompletionEquivLambdaField59
  have hplace := lambdaPlace59_eq_kummerCriterion K
  cases hplace
  rfl

@[simp]
private theorem valuedCompletionEquivLambdaField59_symm_valuation
    (x : LambdaField59 K) :
    Valued.v ((valuedCompletionEquivLambdaField59 K).symm x) = Valued.v x := by
  have h := valuedCompletionEquivLambdaField59_valuation K
    ((valuedCompletionEquivLambdaField59 K).symm x)
  simpa using h.symm

/-- Package-model form of high-unit power surjectivity. -/
private theorem exists_valuedCompletionUnit_pow59_eq_of_depth60
    (u : (ValuedCompletion 59 K)ˣ)
    (hu : Valued.v ((u : ValuedCompletion 59 K) - 1) ≤
      WithZero.exp (-60 : ℤ)) :
    ∃ x : (ValuedCompletion 59 K)ˣ, x ^ 59 = u := by
  have hbound : WithZero.exp (-60 : ℤ) < (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have huval : Valued.v (u : ValuedCompletion 59 K) = 1 := by
    have hlt : Valued.v ((u : ValuedCompletion 59 K) - 1) < 1 :=
      hu.trans_lt hbound
    have hone := (Valued.v : Valuation (ValuedCompletion 59 K) ℤᵐ⁰)
      |>.map_one_add_of_lt hlt
    simpa using hone
  let uRVal : R59 K := ⟨(u : ValuedCompletion 59 K), huval.le⟩
  have huRUnit : IsUnit uRVal :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (a := uRVal)).mpr huval
  let uR : (R59 K)ˣ := huRUnit.unit
  have huRval : (uR : R59 K) = uRVal := huRUnit.unit_spec
  have huDeep : (uR : R59 K) - 1 ∈ (lambdaIdeal 59 K) ^ 60 := by
    rw [mem_lambdaIdeal_pow_iff_valuation_le K 60]
    change Valued.v ((((uR : R59 K) : ValuedCompletion 59 K)) - 1) ≤
      Valued.v
        ((((valuedCyclotomicLambdaInteger 59 K) ^ 60 : R59 K) :
          ValuedCompletion 59 K))
    rw [huRval]
    change Valued.v ((u : ValuedCompletion 59 K) - 1) ≤
      Valued.v ((valuedCyclotomicLambda 59 K) ^ 60)
    rw [map_pow, valuedCyclotomicLambda_valuation]
    simpa [← WithZero.exp_nsmul] using hu
  obtain ⟨xR, hxR⟩ :=
    exists_unit_pow59_eq_of_sub_one_mem_lambdaIdeal_pow_sixty K uR huDeep
  let inclusion : R59 K →+* ValuedCompletion 59 K :=
    (KummerCriterion.Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum
      59 K).adicCompletionIntegers K |>.subtype
  let xF : (ValuedCompletion 59 K)ˣ := Units.map inclusion.toMonoidHom xR
  refine ⟨xF, ?_⟩
  apply Units.ext
  change inclusion ((xR : R59 K) ^ 59) = (u : ValuedCompletion 59 K)
  rw [show (xR : R59 K) ^ 59 = (uR : R59 K) by
    exact congrArg Units.val hxR, huRval]
  rfl

/-- Every actual depth-60 lambda-adic field unit is a 59th power of a
field unit.  This is the precise high-unit surjectivity input needed to
remove the quotient ambiguity in `U_59/U_60`. -/
theorem exists_fieldUnit_pow59_eq_of_mem_U60
    (u : (LambdaField59 K)ˣ) (hu : u ∈ U60 K) :
    ∃ x : (LambdaField59 K)ˣ, x ^ 59 = u := by
  rw [mem_lambdaOneUnits] at hu
  let e := valuedCompletionEquivLambdaField59 K
  let u' : (ValuedCompletion 59 K)ˣ := Units.map e.symm.toMonoidHom u
  have hu' : Valued.v ((u' : ValuedCompletion 59 K) - 1) ≤
      WithZero.exp (-60 : ℤ) := by
    change Valued.v (e.symm (u : LambdaField59 K) - 1) ≤ _
    rw [← map_one e.symm, ← map_sub]
    rw [valuedCompletionEquivLambdaField59_symm_valuation]
    simpa using hu
  obtain ⟨x', hx'⟩ :=
    exists_valuedCompletionUnit_pow59_eq_of_depth60 K u' hu'
  refine ⟨Units.map e.toMonoidHom x', ?_⟩
  rw [← map_pow, hx']
  apply Units.ext
  rfl

/-! ## Exactness of the critical norm quotient

The preceding theorem is precisely what is needed to recover an actual norm
from a norm class modulo `U_60`: the quotient error is a 59th power in the
base field, hence the norm of its image in the degree-59 Kummer extension.
-/

/-- Membership of the correction class in the critical quotient norm image
already supplies an exact field-norm witness for the correction. -/
theorem exists_correction_norm_of_correctionClass59_mem_normImage
    (hmem : correctionClass59 K ∈ normImageCriticalUnitLayer59 K) :
    ∃ gamma : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) gamma =
        primitiveRootNormCorrection59 K := by
  rcases hmem with ⟨n, hn, hquot⟩
  have hnormRange :
      (((n : U59 K) : (LambdaField59 K)ˣ)) ∈
        (twistedLambdaNormUnits59 K).range :=
    (Subgroup.mem_subgroupOf).mp hn
  rcases hnormRange with ⟨gammaUnit, hgammaUnit⟩
  let ratio : U59 K := correctionInU59 K / n
  have hratioSub : ratio ∈ U60InU59 K := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change QuotientGroup.mk (correctionInU59 K) = QuotientGroup.mk n
    simpa [correctionClass59] using hquot.symm
  have hratio60 :
      (((ratio : U59 K) : (LambdaField59 K)ˣ)) ∈ U60 K :=
    (Subgroup.mem_subgroupOf).mp hratioSub
  obtain ⟨d, hd⟩ :=
    exists_fieldUnit_pow59_eq_of_mem_U60 K
      (((ratio : U59 K) : (LambdaField59 K)ˣ)) hratio60
  letI : Polynomial.IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (Fermat.Conservation.KummerCyclicQuotient59.kummerPolynomial59
        (LambdaField59 K) (twistedLambda59 K)) :=
    Fermat.Conservation.KummerCyclicQuotient59.kummerExtension59_isSplittingField
      (LambdaField59 K) (twistedLambda59 K)
  letI : FiniteDimensional (LambdaField59 K)
      (twistedLambdaKummerExtension59 K) :=
    Polynomial.IsSplittingField.finiteDimensional
      (twistedLambdaKummerExtension59 K)
      (Fermat.Conservation.KummerCyclicQuotient59.kummerPolynomial59
        (LambdaField59 K) (twistedLambda59 K))
  have hfinrank : Module.finrank (LambdaField59 K)
      (twistedLambdaKummerExtension59 K) = 59 := by
    exact finrank_of_isSplittingField_X_pow_sub_C
      ⟨lambdaLocalPrimitiveRoot59 K,
        (mem_primitiveRoots (by norm_num : 0 < 59)).2
          (lambdaLocalPrimitiveRoot59_isPrimitive K)⟩
      (twistedLambdaPolynomial59_irreducible K)
      (twistedLambdaKummerExtension59 K)
  have hgammaField :
      Algebra.norm (LambdaField59 K)
          (gammaUnit : twistedLambdaKummerExtension59 K) =
        ((((n : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K)) := by
    have h := congrArg Units.val hgammaUnit
    exact h
  have hdField :
      (d : LambdaField59 K) ^ 59 =
        ((((ratio : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K)) := by
    exact congrArg Units.val hd
  have hfactorU59 : n * ratio = correctionInU59 K := by
    dsimp [ratio]
    simp [div_eq_mul_inv]
  have hfactorField :
      ((((n : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K)) *
          ((((ratio : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K)) =
        primitiveRootNormCorrection59 K := by
    have h := congrArg
      (fun z : U59 K =>
        ((((z : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K)))
      hfactorU59
    simpa [correctionInU59, correctionFieldUnit59] using h
  refine ⟨(gammaUnit : twistedLambdaKummerExtension59 K) *
      algebraMap (LambdaField59 K) (twistedLambdaKummerExtension59 K)
        (d : LambdaField59 K), ?_⟩
  rw [map_mul, Algebra.norm_algebraMap, hfinrank, hgammaField, hdField]
  exact hfactorField

/-- The quotient norm test for the correction is exact, not merely a
necessary condition. -/
theorem correctionClass59_mem_normImage_iff_correction_is_norm :
    correctionClass59 K ∈ normImageCriticalUnitLayer59 K ↔
      ∃ gamma : twistedLambdaKummerExtension59 K,
        Algebra.norm (LambdaField59 K) gamma =
          primitiveRootNormCorrection59 K := by
  constructor
  · exact exists_correction_norm_of_correctionClass59_mem_normImage K
  · rintro ⟨gamma, hgamma⟩
    exact correctionClass59_mem_normImage_of_norm K gamma hgamma

/-- The primitive-root norm problem is exactly the critical quotient
membership problem. -/
theorem primitiveRoot_is_norm_iff_correctionClass59_mem_normImage :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      correctionClass59 K ∈ normImageCriticalUnitLayer59 K := by
  rw [TwistedLambdaNormCorrection59.primitiveRoot_is_norm_iff_correction_is_norm]
  exact (correctionClass59_mem_normImage_iff_correction_is_norm K).symm

/-- Equivalently, exclusion of the correction class is exactly the
primitive-root non-norm statement. -/
theorem primitiveRoot_not_norm_iff_correctionClass59_not_mem_normImage :
    (¬ ∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      correctionClass59 K ∉ normImageCriticalUnitLayer59 K := by
  exact not_congr (primitiveRoot_is_norm_iff_correctionClass59_mem_normImage K)

/-- The actual quotient norm image is the zero locus of the genuine Kummer
cup, specialized to the explicit correction class. -/
theorem correctionClass59_mem_normImage_iff_twistedLambdaKummerCup_eq_zero :
    correctionClass59 K ∈ normImageCriticalUnitLayer59 K ↔
      twistedLambdaKummerCupH2Class59 K = 0 := by
  exact
    (primitiveRoot_is_norm_iff_correctionClass59_mem_normImage K).symm.trans
      (primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero K)

/-- Thus the still-open quotient exclusion is exactly, rather than merely
implied by, nonvanishing of the genuine twisted-lambda Kummer cup. -/
theorem correctionClass59_not_mem_normImage_iff_twistedLambdaKummerCup_ne_zero :
    correctionClass59 K ∉ normImageCriticalUnitLayer59 K ↔
      twistedLambdaKummerCupH2Class59 K ≠ 0 := by
  exact not_congr
    (correctionClass59_mem_normImage_iff_twistedLambdaKummerCup_eq_zero K)

end Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59
