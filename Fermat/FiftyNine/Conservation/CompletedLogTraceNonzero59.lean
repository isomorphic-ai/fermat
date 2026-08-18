/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Nonvanishing of the completed logarithm trace at 59

The completed logarithm trace is the previously computed finite logarithm
receipt plus a lambda-deep error.  Cancellation converts that error into a
rational factor `59`, while integrality of the local trace shows that the
remaining coefficient is a rational 59-adic integer.  Reduction modulo 59
therefore preserves the finite receipt `-1`, proving that the normalized
trace of the genuine infinite logarithm is nonzero.
-/
import Fermat.FiftyNine.Conservation.CompletedLogTail59
import Fermat.FiftyNine.Conservation.LocalIntegralTrace59

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59

open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CompletedLogTail59
open Fermat.FiftyNine.Conservation.LocalIntegralTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The genuine local trace of the full completed logarithm, normalized by
the rational prime 59. -/
def normalizedCompletedLogTrace59 : RationalCompletion59 :=
  (algebraMap ℚ RationalCompletion59 59)⁻¹ *
    Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
      (completedLogUnit60Lambda K)

/-- The normalized completed-log trace differs from the already computed
finite receipt by a multiple of 59 coming from a rational local integer. -/
theorem normalizedCompletedLogTrace59_eq_finite_add_prime_mul_integer :
    ∃ t : RationalIntegerRing59,
      normalizedCompletedLogTrace59 K =
        normalizedLocalTraceFiniteLog59 K +
          (59 : RationalCompletion59) * (t : RationalCompletion59) := by
  obtain ⟨y, hy, htrace⟩ :=
    trace_completedLogUnit60Lambda_eq_prime_mul_normalized_add_lambda_error K
  obtain ⟨t, hyt⟩ :=
    exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda K hy
  refine ⟨t, ?_⟩
  rw [normalizedCompletedLogTrace59, htrace, hyt]
  have hp : (algebraMap ℚ RationalCompletion59 59) ≠ 0 := by
    intro h
    have hq : (59 : ℚ) = 0 :=
      (algebraMap ℚ RationalCompletion59).injective (by simpa using h)
    norm_num at hq
  field_simp

/-- The full normalized completed-log trace is an actual rational local
integer and retains the exact residue `-1` modulo 59. -/
theorem exists_integer_normalizedCompletedLogTrace59_and_residue :
    ∃ z : RationalIntegerRing59,
      normalizedCompletedLogTrace59 K = (z : RationalCompletion59) ∧
      rationalPadicIntegerToZMod 59 z = (-1 : ZMod 59) := by
  obtain ⟨t, ht⟩ :=
    normalizedCompletedLogTrace59_eq_finite_add_prime_mul_integer K
  let z : RationalIntegerRing59 :=
    normalizedLocalTraceFiniteLog59Integer + 59 * t
  refine ⟨z, ?_, ?_⟩
  · rw [ht, normalizedLocalTraceFiniteLog59_eq_integer_coe K]
    change ((normalizedLocalTraceFiniteLog59Integer + 59 * t :
      RationalIntegerRing59) : RationalCompletion59) = _
    simp [z]
  · dsimp [z]
    rw [map_add, map_mul,
      normalizedLocalTraceFiniteLog59Integer_mod59]
    have hpmod : rationalPadicIntegerToZMod 59
        (59 : RationalIntegerRing59) = 0 := by
      exact (rationalPadicIntegerToZMod_natCast (p := 59) 59).trans (by
        decide)
    rw [hpmod]
    simp

/-- In particular, the normalized trace of the genuine infinite completed
logarithm is nonzero. -/
theorem normalizedCompletedLogTrace59_ne_zero :
    normalizedCompletedLogTrace59 K ≠ 0 := by
  obtain ⟨z, hz, hres⟩ :=
    exists_integer_normalizedCompletedLogTrace59_and_residue K
  intro hzero
  have hz0 : z = 0 := by
    apply Subtype.ext
    change (z : RationalCompletion59) = 0
    rw [← hz, hzero]
  rw [hz0, map_zero] at hres
  norm_num at hres

end Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59
