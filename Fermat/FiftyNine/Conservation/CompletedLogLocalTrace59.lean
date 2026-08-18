/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The completed logarithm of the principal unit 60

This module puts the concrete principal unit `60 = 1 + 59` into the native
completed-logarithm domain.  Its additive coordinate is exactly the twist
coordinate used by the finite logarithm, so stage 59 of the completed
logarithm is the finite-log receipt already connected to the genuine local
trace.

The local integer ring is genuinely `lambda`-adically complete.  The
resulting canonical inverse to its redundant formal completion transports
the full logarithm into the local field.  Its local trace is exactly the
finite-log main term plus the trace of an explicitly `lambda^59`-deep error.
-/
import Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
import Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59
import KummerCriterion.CyclotomicUnits.LogDomain

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59

open KummerCriterion.Furtwaengler.DieudonneDwork
open KummerCriterion.CyclotomicUnits
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59
open Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
open Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The unit `60` in the ring of `59`-integral rationals. -/
def principalUnit60RIntegral :
    (KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59)ˣ where
  val := 60
  inv := ⟨(1 : ℚ) / 60, by
    change IsRIntegralRat 59 ((1 : ℚ) / 60)
    norm_num [IsRIntegralRat]⟩
  val_inv := by
    apply Subtype.ext
    change (60 : ℚ) * (1 / 60) = 1
    norm_num
  inv_val := by
    apply Subtype.ext
    change ((1 : ℚ) / 60) * 60 = 1
    norm_num

/-- The principal unit `60 = 1 + 59` in the native completed-log domain. -/
def completedLogUnit60 : completedLogDomain (p := 59) (K := K) := by
  let u : (ValuedIntegerRing 59 K)ˣ :=
    Units.map (rIntegralRatToValuedInteger 59 K).toMonoidHom
      principalUnit60RIntegral
  refine ⟨u, ?_⟩
  apply (KummerCriterion.Ideal.mem_oneUnitsSubgroup).2
  change (u : ValuedIntegerRing 59 K) - 1 ∈ lambdaIdeal 59 K
  have hu : (u : ValuedIntegerRing 59 K) = 60 := by
    change rIntegralRatToValuedInteger 59 K
        (principalUnit60RIntegral :
          KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    change rIntegralRatToValuedInteger 59 K
        (60 : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    exact map_natCast (rIntegralRatToValuedInteger 59 K) 60
  rw [hu]
  have hcoord : (60 : ValuedIntegerRing 59 K) - 1 = 59 := by norm_num
  rw [hcoord]
  exact Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
    (twistLogCoordinate59_mem K)

/-- Its additive principal-unit coordinate is exactly the twist coordinate
used in the finite-log computation. -/
theorem completedLogArg_unit60 :
    completedLogArg (p := 59) (K := K) (completedLogUnit60 K) =
      twistLogCoordinate59 K := by
  rw [completedLogArg]
  have hu : (((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
      ValuedIntegerRing 59 K) = 60 := by
    change rIntegralRatToValuedInteger 59 K
        (principalUnit60RIntegral :
          KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    change rIntegralRatToValuedInteger 59 K
        (60 : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    exact map_natCast (rIntegralRatToValuedInteger 59 K) 60
  rw [hu]
  norm_num [twistLogCoordinate59]

/-- Stage 59 of the completed logarithm is exactly the package finite-log
receipt already connected to the local algebra trace. -/
theorem completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59 :
    AdicCompletion.evalₐ (lambdaIdeal 59 K) 59
        (completedLog (p := 59) (K := K) (completedLogUnit60 K)) =
      Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
        (rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral) := by
  rw [completedLog_evalₐ_succ (u := completedLogUnit60 K) 58]
  rw [samePrimeFiniteLog_eq_of_eq (p := 59) (K := K) (N := 58)
    (completedLogArg_unit60 K)
    (completedLogArg_mem (p := 59) (K := K) (completedLogUnit60 K))
    (Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
      (twistLogCoordinate59_mem K))]
  exact samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59 K

/-! ## Comparing the formal completion with the complete integer ring -/

/-- The canonical inverse of the redundant adic-completion embedding. -/
def dworkCompleteToValuedInteger59 :
    DworkCompleteIntegerRing 59 K →+* ValuedIntegerRing 59 K :=
  (AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm.toRingHom

@[simp]
theorem dworkCompleteToValuedInteger59_algebraMap
    (x : ValuedIntegerRing 59 K) :
    dworkCompleteToValuedInteger59 K
        (algebraMap (ValuedIntegerRing 59 K)
          (DworkCompleteIntegerRing 59 K) x) = x := by
  exact AdicCompletion.ofAlgEquiv_symm_of (lambdaIdeal 59 K) x

/-- The completed logarithm of `60`, transported back into the already
complete valuation integer ring. -/
def completedLogUnit60ValuedInteger : ValuedIntegerRing 59 K :=
  dworkCompleteToValuedInteger59 K
    (completedLog (p := 59) (K := K) (completedLogUnit60 K))

/-- Its reduction modulo `lambda^59` is the exact finite-log receipt. -/
theorem completedLogUnit60ValuedInteger_mod_lambda59 :
    Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
        (completedLogUnit60ValuedInteger K) =
      Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
        (rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral) := by
  rw [completedLogUnit60ValuedInteger, dworkCompleteToValuedInteger59]
  change Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
      ((AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm
        (completedLog (p := 59) (K := K) (completedLogUnit60 K))) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  exact completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59 K

/-- Equivalently, the transported completed logarithm differs from the
finite-log scalar representative by an element of `lambda^59`. -/
theorem completedLogUnit60ValuedInteger_sub_scaled_mem :
    completedLogUnit60ValuedInteger K -
        rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral ∈
      (lambdaIdeal 59 K) ^ 59 := by
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := (lambdaIdeal 59 K) ^ 59) _ _).mp
      (completedLogUnit60ValuedInteger_mod_lambda59 K)

/-- Inclusion of the completed valuation integer ring in its fraction
field. -/
def valuedIntegerToLambdaCompletion59 :
    ValuedIntegerRing 59 K →+* LambdaCompletion59 K :=
  (KummerCriterion.Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum 59 K)
    |>.adicCompletionIntegers K |>.subtype

/-- The genuine completed logarithm of `60` as an element of the lambda-adic
field. -/
def completedLogUnit60Lambda : LambdaCompletion59 K :=
  valuedIntegerToLambdaCompletion59 K (completedLogUnit60ValuedInteger K)

/-- The scalar representative embeds compatibly through the rational and
cyclotomic completion towers. -/
theorem valuedInteger_scaledNormalizedFiniteLog59_eq_algebraMap :
    valuedIntegerToLambdaCompletion59 K
        (rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral) =
      algebraMap RationalCompletion59 (LambdaCompletion59 K)
        (algebraMap ℚ RationalCompletion59
          (scaledNormalizedFiniteLog59RIntegral : ℚ)) := by
  change algebraMap K (LambdaCompletion59 K)
      (algebraMap ℚ K (scaledNormalizedFiniteLog59RIntegral : ℚ)) =
    algebraMap RationalCompletion59 (LambdaCompletion59 K)
      (algebraMap ℚ RationalCompletion59
        (scaledNormalizedFiniteLog59RIntegral : ℚ))
  rw [algebraMap_rat_compat K]
  simp

/-- Exact field-level comparison: the completed logarithm equals the finite
receipt representative plus an error coming from `lambda^59`. -/
theorem completedLogUnit60Lambda_eq_scaled_add_deep_error :
    ∃ δ : ValuedIntegerRing 59 K,
      δ ∈ (lambdaIdeal 59 K) ^ 59 ∧
      completedLogUnit60Lambda K =
        algebraMap RationalCompletion59 (LambdaCompletion59 K)
          (algebraMap ℚ RationalCompletion59
            (scaledNormalizedFiniteLog59RIntegral : ℚ)) +
          valuedIntegerToLambdaCompletion59 K δ := by
  let δ := completedLogUnit60ValuedInteger K -
    rIntegralRatToValuedInteger 59 K scaledNormalizedFiniteLog59RIntegral
  refine ⟨δ, completedLogUnit60ValuedInteger_sub_scaled_mem K, ?_⟩
  rw [completedLogUnit60Lambda]
  dsimp [δ]
  rw [map_sub, valuedInteger_scaledNormalizedFiniteLog59_eq_algebraMap]
  ring

/-- Taking the genuine local algebra trace preserves the exact comparison:
the main term is the already-computed normalized finite-log trace, while the
only remaining term is the trace of an explicitly `lambda^59`-deep integer. -/
theorem trace_completedLogUnit60Lambda_eq_scaled_add_deep_error :
    ∃ δ : ValuedIntegerRing 59 K,
      δ ∈ (lambdaIdeal 59 K) ^ 59 ∧
      Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (completedLogUnit60Lambda K) =
        algebraMap ℚ RationalCompletion59 59 *
            normalizedLocalTraceFiniteLog59 K +
          Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
            (valuedIntegerToLambdaCompletion59 K δ) := by
  obtain ⟨δ, hδ, hlog⟩ :=
    completedLogUnit60Lambda_eq_scaled_add_deep_error K
  refine ⟨δ, hδ, ?_⟩
  rw [hlog, map_add, localTrace_scaledNormalizedFiniteLog59]

end Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
