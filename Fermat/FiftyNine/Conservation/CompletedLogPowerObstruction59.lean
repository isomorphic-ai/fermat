/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# A completed-log power obstruction at 59

Every genuine completed logarithm lands in the lambda ideal of the actual
local integer ring.  If the distinguished completed-log unit `60` were a
59th power in the completed-log domain, linearity of the logarithm would
therefore force its normalized trace to be divisible by 59.  This contradicts
the previously computed canonical residue `-1`.

This is an unconditional analytic power obstruction.  It does not identify
the distinguished unit with the primitive-root Kummer class, nor does it
replace the still-needed Artin--Hasse/local-reciprocity comparison turning
that analytic obstruction into a local norm obstruction.
-/
import Fermat.FiftyNine.Conservation.CompletedLogResidue59

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59

open KummerCriterion.CyclotomicUnits
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CompletedLogResidue59
open Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.LocalIntegralTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The actual valuation-integer representative of the completed logarithm
of a principal unit in the formal Dwork completion. -/
def completedLogValuedInteger59
    (u : completedLogDomain (p := 59) (K := K)) :
    ValuedIntegerRing 59 K :=
  dworkCompleteToValuedInteger59 K
    (completedLog (p := 59) (K := K) u)

/-- Every genuine completed logarithm has positive lambda-adic valuation.
This is obtained directly from the zeroth finite logarithm approximation,
which vanishes modulo lambda. -/
theorem completedLogValuedInteger59_mem_lambda
    (u : completedLogDomain (p := 59) (K := K)) :
    completedLogValuedInteger59 K u ∈ lambdaIdeal 59 K := by
  rw [← pow_one (lambdaIdeal 59 K)]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 1)
      ((AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm
        (completedLog (p := 59) (K := K) u)) = 0
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  rw [completedLog_evalₐ_succ (u := u) 0]
  rw [samePrimeFiniteLog_eq_of_sub_mem (p := 59) (K := K) (N := 0)
    (x := completedLogArg (p := 59) (K := K) u) (y := 0)
    (completedLogArg_mem (p := 59) (K := K) u)
    (zero_mem (lambdaIdeal 59 K))]
  · exact samePrimeFiniteLog_arg_zero (p := 59) (K := K) 0
  · simpa using completedLogArg_mem (p := 59) (K := K) u

/-- The distinguished completed-log unit `60` is not a 59th power inside
the genuine completed-log principal-unit domain. -/
theorem completedLogUnit60_not_pow_in_completedLogDomain :
    ¬ ∃ u : completedLogDomain (p := 59) (K := K),
      u ^ 59 = completedLogUnit60 K := by
  rintro ⟨u, hu⟩
  let y : ValuedIntegerRing 59 K := completedLogValuedInteger59 K u
  have hy : y ∈ lambdaIdeal 59 K :=
    completedLogValuedInteger59_mem_lambda K u
  have hlog :
      completedLog (p := 59) (K := K) (completedLogUnit60 K) =
        59 • completedLog (p := 59) (K := K) u := by
    rw [← hu]
    exact completedLog_pow (p := 59) (K := K) u 59
  have hvalued :
      completedLogUnit60ValuedInteger K = 59 • y := by
    rw [completedLogUnit60ValuedInteger]
    dsimp [y, completedLogValuedInteger59]
    rw [← map_nsmul]
    exact congrArg (dworkCompleteToValuedInteger59 K) hlog
  have hfield :
      completedLogUnit60Lambda K =
        (59 : LambdaCompletion59 K) *
          valuedIntegerToLambdaCompletion59 K y := by
    rw [completedLogUnit60Lambda, hvalued, map_nsmul]
    simp [nsmul_eq_mul]
  have htrace :
      Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (completedLogUnit60Lambda K) =
        (59 : RationalCompletion59) *
          Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
            (valuedIntegerToLambdaCompletion59 K y) := by
    rw [hfield]
    have h59 : (59 : LambdaCompletion59 K) =
        algebraMap RationalCompletion59 (LambdaCompletion59 K)
          (59 : RationalCompletion59) := by
      exact (map_natCast
        (algebraMap RationalCompletion59 (LambdaCompletion59 K)) 59).symm
    rw [h59]
    rw [← Algebra.smul_def]
    rw [map_smul]
    rfl
  obtain ⟨t, ht⟩ :=
    exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda K hy
  have hnormalized :
      normalizedCompletedLogTrace59 K =
        (59 : RationalCompletion59) * (t : RationalCompletion59) := by
    rw [normalizedCompletedLogTrace59, htrace, ht]
    have h59map : algebraMap ℚ RationalCompletion59 (59 : ℚ) =
        (59 : RationalCompletion59) := by norm_num
    rw [h59map]
    have hp : (59 : RationalCompletion59) ≠ 0 := by
      intro hzero
      have hq : (59 : ℚ) = 0 :=
        (algebraMap ℚ RationalCompletion59).injective (by simpa using hzero)
      norm_num at hq
    field_simp
  have hcanonical :
      normalizedCompletedLogTrace59Integer K = 59 * t := by
    apply Subtype.ext
    rw [normalizedCompletedLogTrace59Integer_coe, hnormalized]
    exact (map_mul (algebraMap RationalIntegerRing59 RationalCompletion59)
      (59 : RationalIntegerRing59) t).symm
  have hres := normalizedCompletedLogTrace59Residue_eq_neg_one K
  rw [normalizedCompletedLogTrace59Residue, hcanonical, map_mul] at hres
  have hpmod : rationalPadicIntegerToZMod 59
      (59 : RationalIntegerRing59) = 0 := by
    exact (rationalPadicIntegerToZMod_natCast (p := 59) 59).trans (by
      decide)
  rw [hpmod, zero_mul] at hres
  norm_num at hres

end Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59
