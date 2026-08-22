/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The 59th-power kernel on first one-units

Every local unit congruent to `1` modulo `lambda` has 59th power in `U_60`.
The two terms of apparent depth 59 cancel: the Dwork ramification quotient
has residue `-1`, while residue-field Frobenius sends `a ^ 59` to `a`.
All middle binomial terms have depth at least 60 because their binomial
coefficients are divisible by 59.
-/
import Fermat.Exponents.FiftyNine.Conservation.CriticalUnitCoefficient59

open scoped NumberField WithZero

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59

open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The two potentially critical binomial terms cancel one extra
lambda-adic digit. -/
theorem criticalPair59_valuation_le
    (a : LambdaIntegerRing59 K) :
    Valued.v
        ((59 : LambdaField59 K) * (a : LambdaField59 K) *
            canonicalLambda59 K +
          ((a : LambdaField59 K) * canonicalLambda59 K) ^ 59) ≤
      WithZero.exp (-60 : ℤ) := by
  let q : LambdaIntegerRing59 K →+* LambdaResidueRing59 K :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
  let b : LambdaIntegerRing59 K :=
    ramificationQuotientIntegral59 K * a + a ^ 59
  have hqb : q b = 0 := by
    change q (ramificationQuotientIntegral59 K * a + a ^ 59) = 0
    rw [map_add, map_mul, map_pow]
    rw [show q (ramificationQuotientIntegral59 K) =
        (-1 : LambdaResidueRing59 K) by
      exact ramificationQuotientIntegral59_residue_eq_neg_one K]
    rw [lambdaResidue_pow_fiftyNine]
    ring
  have hbmax : b ∈ IsLocalRing.maximalIdeal (LambdaIntegerRing59 K) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hqb
  have hbval : Valued.v (b : LambdaField59 K) < 1 :=
    (mem_lambdaMaximalIdeal59_iff K b).mp hbmax
  have hid :
      (59 : LambdaField59 K) * (a : LambdaField59 K) *
            canonicalLambda59 K +
          ((a : LambdaField59 K) * canonicalLambda59 K) ^ 59 =
        canonicalLambda59 K ^ 59 * (b : LambdaField59 K) := by
    dsimp [b]
    change
      (59 : LambdaField59 K) * (a : LambdaField59 K) *
            canonicalLambda59 K +
          ((a : LambdaField59 K) * canonicalLambda59 K) ^ 59 =
        canonicalLambda59 K ^ 59 *
          (((59 : LambdaField59 K) / canonicalLambda59 K ^ 58) *
            (a : LambdaField59 K) + (a : LambdaField59 K) ^ 59)
    field_simp [canonicalLambda59_ne_zero K]
  rw [hid, map_mul, map_pow, canonicalLambda59_valuation]
  apply (valuation_lt_depth59_iff_le_depth60 _).mp
  rw [show WithZero.exp (-1 : ℤ) ^ 59 = WithZero.exp (-59 : ℤ) by
    norm_num [← WithZero.exp_nsmul]]
  calc
    WithZero.exp (-59 : ℤ) * Valued.v (b : LambdaField59 K) <
        WithZero.exp (-59 : ℤ) * 1 := by
      exact (mul_lt_mul_iff_right₀ WithZero.exp_pos).mpr hbval
    _ = WithZero.exp (-59 : ℤ) := mul_one _

/-- Each middle binomial term has depth at least 60. -/
theorem middleBinomialTerm59_valuation_le
    (a : LambdaIntegerRing59 K) {j : ℕ} (hj : j ∈ Finset.range 57) :
    Valued.v
        ((Nat.choose 59 (j + 2) : LambdaField59 K) *
          ((a : LambdaField59 K) * canonicalLambda59 K) ^ (j + 2)) ≤
      WithZero.exp (-60 : ℤ) := by
  have hjlt : j < 57 := Finset.mem_range.mp hj
  have hk0 : j + 2 ≠ 0 := by omega
  have hklt : j + 2 < 59 := by omega
  obtain ⟨c, hc⟩ :=
    (show 59 ∣ Nat.choose 59 (j + 2) from
      Nat.Prime.dvd_choose_self (by decide) hk0 hklt)
  have hcval : Valued.v (c : LambdaField59 K) ≤ 1 := by
    exact (show LambdaIntegerRing59 K from (c : LambdaIntegerRing59 K)).property
  have hpval : Valued.v ((59 : ℕ) : LambdaField59 K) =
      WithZero.exp (-58 : ℤ) := by
    simpa using natCast59_valuation K
  rw [hc, Nat.cast_mul, map_mul, map_pow, map_mul]
  rw [map_mul, hpval, canonicalLambda59_valuation]
  calc
    WithZero.exp (-58 : ℤ) * Valued.v (c : LambdaField59 K) *
          (Valued.v (a : LambdaField59 K) * WithZero.exp (-1 : ℤ)) ^
            (j + 2) ≤
        WithZero.exp (-58 : ℤ) * 1 *
          (Valued.v (a : LambdaField59 K) * WithZero.exp (-1 : ℤ)) ^
            (j + 2) := by
      exact mul_le_mul_right'
        (mul_le_mul_left' hcval (WithZero.exp (-58 : ℤ))) _
    _ ≤
        WithZero.exp (-58 : ℤ) * 1 *
          (1 * WithZero.exp (-1 : ℤ)) ^ (j + 2) := by
      apply mul_le_mul_left'
      exact pow_le_pow_left'
        (mul_le_mul_right' a.property (WithZero.exp (-1 : ℤ))) (j + 2)
    _ ≤ WithZero.exp (-60 : ℤ) := by
      simp only [mul_one, one_mul]
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add,
        WithZero.exp_le_exp]
      simp only [nsmul_eq_mul]
      omega

theorem middleBinomialSum59_valuation_le
    (a : LambdaIntegerRing59 K) :
    Valued.v
        (∑ j ∈ Finset.range 57,
          (Nat.choose 59 (j + 2) : LambdaField59 K) *
            ((a : LambdaField59 K) * canonicalLambda59 K) ^ (j + 2)) ≤
      WithZero.exp (-60 : ℤ) := by
  exact (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_sum_le
    (fun j hj ↦ middleBinomialTerm59_valuation_le K a hj)

/-- The 59th binomial expansion with the two endpoint and linear terms
separated from the 57 middle terms. -/
theorem one_add_pow_fiftyNine_expansion
    {R : Type*} [CommRing R] (x : R) :
    (1 + x) ^ 59 - 1 =
      (59 : R) * x + x ^ 59 +
        ∑ j ∈ Finset.range 57,
          (Nat.choose 59 (j + 2) : R) * x ^ (j + 2) := by
  let f : ℕ → R := fun m =>
    x ^ m * 1 ^ (59 - m) * (Nat.choose 59 m : R)
  rw [show 1 + x = x + 1 by ring, add_pow]
  change (∑ m ∈ Finset.range 60, f m) - 1 = _
  rw [show 60 = 2 + 58 by norm_num, Finset.sum_range_add]
  have htail :
      (∑ j ∈ Finset.range 58, f (2 + j)) =
        (∑ j ∈ Finset.range 57, f (2 + j)) + f 59 := by
    simpa using Finset.sum_range_succ (fun j => f (2 + j)) 57
  rw [htail]
  have hhead : (∑ m ∈ Finset.range 2, f m) = 1 + (59 : R) * x := by
    norm_num [f, Finset.sum_range_succ]
    ring
  have hlast : f 59 = x ^ 59 := by simp [f]
  rw [hhead, hlast]
  have hmiddle :
      (∑ j ∈ Finset.range 57, f (2 + j)) =
        ∑ j ∈ Finset.range 57,
          (Nat.choose 59 (j + 2) : R) * x ^ (j + 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    change
      x ^ (2 + j) * 1 ^ (59 - (2 + j)) * (Nat.choose 59 (2 + j) : R) =
        (Nat.choose 59 (j + 2) : R) * x ^ (j + 2)
    simp only [one_pow, mul_one]
    rw [add_comm 2 j]
    ring
  rw [hmiddle]
  ring

theorem one_add_integral_mul_lambda_pow59_sub_one_valuation_le
    (a : LambdaIntegerRing59 K) :
    Valued.v
        ((1 + (a : LambdaField59 K) * canonicalLambda59 K) ^ 59 - 1) ≤
      WithZero.exp (-60 : ℤ) := by
  rw [one_add_pow_fiftyNine_expansion]
  apply le_trans (Valuation.map_add _ _ _)
  apply max_le
  · simpa only [mul_assoc] using criticalPair59_valuation_le K a
  · exact middleBinomialSum59_valuation_le K a

/-- Every local first one-unit has 59th power in `U_60`.  This is the
base-field 59th-power kernel used by the critical norm layer. -/
theorem pow_fiftyNine_mem_U60_of_mem_U1
    (u : (LambdaField59 K)ˣ)
    (hu : Valued.v ((u : LambdaField59 K) - 1) ≤
      WithZero.exp (-1 : ℤ)) :
    u ^ 59 ∈ U60 K := by
  let a : LambdaIntegerRing59 K :=
    ⟨((u : LambdaField59 K) - 1) / canonicalLambda59 K, by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      rw [div_eq_mul_inv, map_mul, map_inv₀, canonicalLambda59_valuation]
      calc
        Valued.v ((u : LambdaField59 K) - 1) *
            (WithZero.exp (-1 : ℤ))⁻¹ ≤
          WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by
            gcongr
        _ = 1 := by norm_num⟩
  have hua : (u : LambdaField59 K) =
      1 + (a : LambdaField59 K) * canonicalLambda59 K := by
    dsimp [a]
    field_simp [canonicalLambda59_ne_zero K]
    ring
  rw [mem_lambdaOneUnits]
  change Valued.v ((u : LambdaField59 K) ^ 59 - 1) ≤
    WithZero.exp (-60 : ℤ)
  rw [hua]
  exact one_add_integral_mul_lambda_pow59_sub_one_valuation_le K a

end Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
