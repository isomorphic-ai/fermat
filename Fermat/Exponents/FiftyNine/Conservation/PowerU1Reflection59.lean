/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Reflect first-unit membership through the 59th power

The lambda residue field has 59 elements, so Frobenius is the identity.
Consequently, if the 59th power of a local unit is congruent to one modulo
lambda, the unit itself is congruent to one modulo lambda.
-/
import Fermat.Exponents.FiftyNine.Conservation.CriticalUnitPowerKernel59
import Mathlib.Tactic

open scoped NumberField WithZero

noncomputable section

set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.PowerU1Reflection59

open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- First-unit membership reflects through the 59th-power map. -/
theorem mem_U1_of_pow_fiftyNine_mem_U1
    (u : (LambdaField59 K)ˣ)
    (huPow : u ^ 59 ∈ lambdaOneUnits K 1 (by norm_num)) :
    u ∈ lambdaOneUnits K 1 (by norm_num) := by
  rw [mem_lambdaOneUnits] at huPow ⊢
  have huPowLt :
      Valued.v ((u : LambdaField59 K) ^ 59 - 1) < 1 :=
    huPow.trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  have huValPow : (Valued.v (u : LambdaField59 K)) ^ 59 = (1 : ℤᵐ⁰) := by
    rw [← map_pow]
    have hone :=
      (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_one_add_of_lt huPowLt
    simpa only [add_sub_cancel] using hone
  have huValNe : Valued.v (u : LambdaField59 K) ≠ (0 : ℤᵐ⁰) :=
    (Valuation.ne_zero_iff
      (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰)).mpr u.ne_zero
  have huLog := congrArg WithZero.log huValPow
  simp only [WithZero.log_pow, WithZero.log_one] at huLog
  have huLogZero : WithZero.log (Valued.v (u : LambdaField59 K)) = 0 := by
    have hmul :
        (59 : ℤ) * WithZero.log (Valued.v (u : LambdaField59 K)) = 0 := by
      simpa [nsmul_eq_mul] using huLog
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have huVal : Valued.v (u : LambdaField59 K) = 1 := by
    have hexplog := WithZero.exp_log huValNe
    rw [huLogZero, WithZero.exp_zero] at hexplog
    exact hexplog.symm
  let a : LambdaIntegerRing59 K :=
    ⟨(u : LambdaField59 K), huVal.le⟩
  let q : LambdaIntegerRing59 K →+* LambdaResidueRing59 K :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
  have haPowSubMax :
      a ^ 59 - 1 ∈ IsLocalRing.maximalIdeal (LambdaIntegerRing59 K) := by
    rw [mem_lambdaMaximalIdeal59_iff]
    change Valued.v ((u : LambdaField59 K) ^ 59 - 1) < 1
    exact huPowLt
  have hqPow : (q a) ^ 59 = 1 := by
    have hzero : q (a ^ 59 - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr haPowSubMax
    rw [map_sub, map_pow, map_one, sub_eq_zero] at hzero
    exact hzero
  have hqa : q a = 1 := by
    calc
      q a = (q a) ^ 59 := (lambdaResidue_pow_fiftyNine K (q a)).symm
      _ = 1 := hqPow
  have haSubMax :
      a - 1 ∈ IsLocalRing.maximalIdeal (LambdaIntegerRing59 K) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hqa, map_one, sub_self]
  have huSubLt : Valued.v ((u : LambdaField59 K) - 1) < 1 := by
    have := (mem_lambdaMaximalIdeal59_iff K (a - 1)).mp haSubMax
    simpa [a] using this
  by_cases huSubZero : Valued.v ((u : LambdaField59 K) - 1) = 0
  · rw [huSubZero]
    exact bot_le
  · have huSubLogLt :
        WithZero.log (Valued.v ((u : LambdaField59 K) - 1)) < (0 : ℤ) := by
      rw [WithZero.log_lt_iff_lt_exp huSubZero]
      simpa using huSubLt
    have huSubLogLe :
        WithZero.log (Valued.v ((u : LambdaField59 K) - 1)) ≤ (-1 : ℤ) := by
      omega
    exact (WithZero.log_le_iff_le_exp huSubZero).mp huSubLogLe

end Fermat.FiftyNine.Conservation.PowerU1Reflection59
