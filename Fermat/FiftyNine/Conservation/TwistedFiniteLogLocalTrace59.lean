/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# From the package finite logarithm receipt to the local trace at 59

`TwistedArtinHasse59` computed a rational finite logarithm, while
`TwistedArtinHasseLocalTrace59` embedded its normalized value into the honest
degree-58 local trace.  This file proves that the rational computation really
represents the existing KummerCriterion finite logarithm in its native
quotient.

The package theorem first reduces the finite logarithm of the twist
coordinate `59` to that coordinate modulo `lambda^59`.  Independently,

`normalizedFiniteLog59 = 1 (mod 59)`.

Consequently `59 * normalizedFiniteLog59 - 59` is `59^2` times a
`59`-integral rational.  Since `59^2` lies in `lambda^59`, both elements have
the same image in the package quotient.  The final theorem records that
exact quotient receipt together with the equation saying that the normalized
local trace is obtained by dividing the trace of its scalar representative
by `59`.

No completed-logarithm, Hilbert-symbol, or Artin--Hasse reciprocity comparison
is asserted here.
-/
import Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59

open scoped NumberField Topology Valued

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59

open KummerCriterion.Furtwaengler.DieudonneDwork
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The rational finite logarithm before division by its leading factor 59,
bundled with its 59-integrality proof. -/
def scaledNormalizedFiniteLog59RIntegral :
    KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59 :=
  ⟨59 * normalizedFiniteLog59, by
    exact (by norm_num [IsRIntegralRat] : IsRIntegralRat 59 (59 : ℚ)).mul
      normalizedFiniteLog59_isRIntegral⟩

theorem normalizedFiniteLog59_sub_one_eq_prime_mul :
    ∃ q : ℚ, IsRIntegralRat 59 q ∧
      normalizedFiniteLog59 - 1 = 59 * q := by
  have hOne : IsRIntegralRat 59 (1 : ℚ) := IsRIntegralRat.one 59
  have hDiff : IsRIntegralRat 59 (normalizedFiniteLog59 - 1) :=
    normalizedFiniteLog59_isRIntegral.sub hOne
  have hResidue :
      IsRIntegralRat.toZMod (normalizedFiniteLog59 - 1) hDiff =
        (0 : ZMod 59) := by
    rw [IsRIntegralRat.toZMod_sub
      normalizedFiniteLog59_isRIntegral hOne]
    rw [normalizedFiniteLog59_mod59]
    simp [IsRIntegralRat.toZMod_one]
  exact IsRIntegralRat.exists_eq_natCast_mul_of_toZMod_eq_zero hDiff hResidue

/-- The package coefficient representing the scaled rational finite
logarithm differs from the literal twist coordinate by an element of
`lambda^59`. -/
theorem scaledNormalizedFiniteLog59_sub_twistLogCoordinate59_mem :
    rIntegralRatToValuedInteger 59 K scaledNormalizedFiniteLog59RIntegral -
        twistLogCoordinate59 K ∈ (lambdaIdeal 59 K) ^ 59 := by
  obtain ⟨q, hq, hqeq⟩ := normalizedFiniteLog59_sub_one_eq_prime_mul
  let qR : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59 :=
    ⟨q, hq⟩
  let primeR : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59 :=
    (59 : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59)
  have hscaled :
      scaledNormalizedFiniteLog59RIntegral - primeR = primeR ^ 2 * qR := by
    apply Subtype.ext
    change (59 : ℚ) * normalizedFiniteLog59 - 59 = 59 ^ 2 * q
    rw [show (59 : ℚ) * normalizedFiniteLog59 - 59 =
        59 * (normalizedFiniteLog59 - 1) by ring]
    rw [hqeq]
    ring
  change rIntegralRatToValuedInteger 59 K scaledNormalizedFiniteLog59RIntegral -
      (59 : ValuedIntegerRing 59 K) ∈ (lambdaIdeal 59 K) ^ 59
  rw [show (59 : ValuedIntegerRing 59 K) =
      rIntegralRatToValuedInteger 59 K primeR by
        exact (map_natCast (rIntegralRatToValuedInteger 59 K) 59).symm]
  have hprimeMap :
      rIntegralRatToValuedInteger 59 K primeR =
        (59 : ValuedIntegerRing 59 K) :=
    map_natCast (rIntegralRatToValuedInteger 59 K) 59
  rw [← map_sub, hscaled, map_mul, map_pow]
  rw [hprimeMap]
  exact ((lambdaIdeal 59 K) ^ 59).mul_mem_right
    (rIntegralRatToValuedInteger 59 K qR)
    (natCast_prime_pow_mem_lambdaIdeal_pow (p := 59) (K := K)
      (M := 2) (N := 59) (by norm_num))

/-- The existing package finite logarithm is represented, in its actual
quotient, by the image of `59 * normalizedFiniteLog59`. -/
theorem samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59 :
    samePrimeFiniteLog (p := 59) (K := K) 58 (twistLogCoordinate59 K)
        (Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
          (twistLogCoordinate59_mem K)) =
      Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
        (rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral) := by
  rw [samePrimeFiniteLog_twist59_eq K]
  rw [← sub_eq_zero]
  rw [← map_sub]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simpa only [neg_sub] using
    ((lambdaIdeal 59 K) ^ 59).neg_mem
      (scaledNormalizedFiniteLog59_sub_twistLogCoordinate59_mem K)

/-- Tracing the scalar representative of the package receipt gives 59 times
the normalized local trace. -/
theorem localTrace_scaledNormalizedFiniteLog59 :
    Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
        (algebraMap RationalCompletion59 (LambdaCompletion59 K)
          (algebraMap ℚ RationalCompletion59
            (scaledNormalizedFiniteLog59RIntegral : ℚ))) =
      algebraMap ℚ RationalCompletion59 59 *
        normalizedLocalTraceFiniteLog59 K := by
  change Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
      (algebraMap RationalCompletion59 (LambdaCompletion59 K)
        (algebraMap ℚ RationalCompletion59
          (59 * normalizedFiniteLog59))) = _
  rw [localTrace59_algebraMap_rat]
  rw [normalizedLocalTraceFiniteLog59_eq]
  rw [← map_mul]
  congr 1
  simp only [normalizedTraceFiniteLog59]
  ring

/-- Equivalently, the normalized local trace is obtained by dividing the
trace of the package receipt's scalar representative by 59. -/
theorem normalizedLocalTraceFiniteLog59_eq_inv_prime_mul_trace_scaled :
    normalizedLocalTraceFiniteLog59 K =
      (algebraMap ℚ RationalCompletion59 59)⁻¹ *
        Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (algebraMap RationalCompletion59 (LambdaCompletion59 K)
            (algebraMap ℚ RationalCompletion59
              (scaledNormalizedFiniteLog59RIntegral : ℚ))) := by
  rw [localTrace_scaledNormalizedFiniteLog59]
  have hmap59 : algebraMap ℚ RationalCompletion59 (59 : ℚ) =
      (59 : RationalCompletion59) := by norm_num
  rw [hmap59]
  change normalizedLocalTraceFiniteLog59 K =
    (59 : RationalCompletion59)⁻¹ *
      ((59 : RationalCompletion59) * normalizedLocalTraceFiniteLog59 K)
  have h59 : (59 : RationalCompletion59) ≠ 0 := by
    rw [← hmap59]
    intro hzero
    have hq : (59 : ℚ) = 0 :=
      (algebraMap ℚ RationalCompletion59).injective (by simpa using hzero)
    norm_num at hq
  rw [← mul_assoc, inv_mul_cancel₀ h59, one_mul]

/-- The exact quotient receipt and its local-trace normalization, exposed as
one end-to-end bridge. -/
theorem packageFiniteLogReceipt59_and_localTraceNormalization :
    samePrimeFiniteLog (p := 59) (K := K) 58 (twistLogCoordinate59 K)
        (Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
          (twistLogCoordinate59_mem K)) =
        Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
          (rIntegralRatToValuedInteger 59 K
            scaledNormalizedFiniteLog59RIntegral) ∧
      normalizedLocalTraceFiniteLog59 K =
        (algebraMap ℚ RationalCompletion59 59)⁻¹ *
          Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
            (algebraMap RationalCompletion59 (LambdaCompletion59 K)
              (algebraMap ℚ RationalCompletion59
                (scaledNormalizedFiniteLog59RIntegral : ℚ))) :=
  ⟨samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59 K,
    normalizedLocalTraceFiniteLog59_eq_inv_prime_mul_trace_scaled K⟩

end Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
