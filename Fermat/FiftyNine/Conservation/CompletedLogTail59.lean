/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The divisible tail of the completed logarithm at 59

Stage 59 determines the completed logarithm modulo `lambda^59`.  Since
`lambda^58` generates the same ideal as `59`, its remaining error factors as
`59 * y` with `y` still in the principal lambda ideal.  This module carries
that cancellation through the local-field embedding and the genuine local
algebra trace.
-/
import Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Fermat.FiftyNine.Conservation.CompletedLogTail59

open KummerCriterion.Furtwaengler.DieudonneDwork
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59
open Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The stage-59 error contains one rational factor `59` and retains one
factor of the local uniformizer. -/
theorem completedLogUnit60ValuedInteger_sub_scaled_eq_prime_mul_lambda :
    ∃ y : ValuedIntegerRing 59 K,
      y ∈ lambdaIdeal 59 K ∧
      completedLogUnit60ValuedInteger K -
          rIntegralRatToValuedInteger 59 K
            scaledNormalizedFiniteLog59RIntegral = 59 * y := by
  have hx : completedLogUnit60ValuedInteger K -
        rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral ∈
      (lambdaIdeal 59 K) ^ (1 * (59 - 1) + 1) := by
    norm_num
    exact completedLogUnit60ValuedInteger_sub_scaled_mem K
  obtain ⟨y, hy, hmul⟩ :=
    exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
      (p := 59) (K := K) 1 1 hx
  refine ⟨y, ?_, ?_⟩
  · simpa using hy
  · simpa using hmul.symm

/-- Field-level form of the same cancellation: the entire tail is `59`
times an element still divisible by `lambda`. -/
theorem completedLogUnit60Lambda_eq_scaled_add_prime_mul_lambda_error :
    ∃ y : ValuedIntegerRing 59 K,
      y ∈ lambdaIdeal 59 K ∧
      completedLogUnit60Lambda K =
        algebraMap RationalCompletion59 (LambdaCompletion59 K)
          (algebraMap ℚ RationalCompletion59
            (scaledNormalizedFiniteLog59RIntegral : ℚ)) +
          algebraMap RationalCompletion59 (LambdaCompletion59 K)
              (algebraMap ℚ RationalCompletion59 59) *
            valuedIntegerToLambdaCompletion59 K y := by
  obtain ⟨y, hy, herr⟩ :=
    completedLogUnit60ValuedInteger_sub_scaled_eq_prime_mul_lambda K
  refine ⟨y, hy, ?_⟩
  rw [completedLogUnit60Lambda]
  have hsplit : completedLogUnit60ValuedInteger K =
      rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral + 59 * y := by
    rw [sub_eq_iff_eq_add] at herr
    rw [herr, add_comm]
  rw [hsplit, map_add, map_mul,
    valuedInteger_scaledNormalizedFiniteLog59_eq_algebraMap]
  congr 2
  rw [show valuedIntegerToLambdaCompletion59 K
      (59 : ValuedIntegerRing 59 K) = (59 : LambdaCompletion59 K) by
    exact map_natCast (valuedIntegerToLambdaCompletion59 K) 59]
  rw [algebraMap_rat_compat K]
  simp

/-- After taking the local trace, the entire completed logarithm carries an
explicit factor `59`; the residual tail still comes from `lambda`. -/
theorem trace_completedLogUnit60Lambda_eq_prime_mul_normalized_add_lambda_error :
    ∃ y : ValuedIntegerRing 59 K,
      y ∈ lambdaIdeal 59 K ∧
      Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (completedLogUnit60Lambda K) =
        algebraMap ℚ RationalCompletion59 59 *
          (normalizedLocalTraceFiniteLog59 K +
            Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
              (valuedIntegerToLambdaCompletion59 K y)) := by
  obtain ⟨y, hy, hlog⟩ :=
    completedLogUnit60Lambda_eq_scaled_add_prime_mul_lambda_error K
  refine ⟨y, hy, ?_⟩
  rw [hlog, map_add, localTrace_scaledNormalizedFiniteLog59]
  have htail :
      Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (algebraMap RationalCompletion59 (LambdaCompletion59 K)
              (algebraMap ℚ RationalCompletion59 59) *
            valuedIntegerToLambdaCompletion59 K y) =
        algebraMap ℚ RationalCompletion59 59 *
          Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
            (valuedIntegerToLambdaCompletion59 K y) := by
    change Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
        ((algebraMap ℚ RationalCompletion59 59) •
          valuedIntegerToLambdaCompletion59 K y) = _
    rw [LinearMap.map_smul, Algebra.smul_def]
    simp
  rw [htail]
  ring

end Fermat.FiftyNine.Conservation.CompletedLogTail59
