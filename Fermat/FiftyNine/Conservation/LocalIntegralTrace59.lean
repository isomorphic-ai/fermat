/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Integrality of the local cyclotomic trace at 59

The formal Dwork completion has an explicit power basis over the rational
59-adic integers.  Since the actual local integer ring is already complete,
the canonical adic-completion equivalence transports this basis to the
valuation integer ring.  Localization of the resulting finite free algebra
then identifies its integral trace with the genuine local field trace.

Consequently, the local trace of every lambda-integral element lies in the
rational 59-adic integer ring.
-/
import Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
import KummerCriterion.CyclotomicUnits.DworkParameter.Part14
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Trace.Quotient

open scoped NumberField Topology Valued WithZero nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 120000

namespace Fermat.FiftyNine.Conservation.LocalIntegralTrace59

open KummerCriterion.Furtwaengler.DieudonneDwork
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The formal Dwork completion and actual complete local integer ring,
as algebras over the rational 59-adic integers. -/
noncomputable def dworkValuedAlgEquiv59 :
    DworkCompleteIntegerRing 59 K ≃ₐ[RationalIntegerRing59]
      ValuedIntegerRing 59 K where
  __ := (AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm.toRingEquiv
  commutes' r := by
    change dworkCompleteToValuedInteger59 K
      (algebraMap (ValuedIntegerRing 59 K) (DworkCompleteIntegerRing 59 K)
        (algebraMap RationalIntegerRing59 (ValuedIntegerRing 59 K) r)) =
      algebraMap RationalIntegerRing59 (ValuedIntegerRing 59 K) r
    exact dworkCompleteToValuedInteger59_algebraMap K _

/-- The transported Dwork power basis of the actual local integer ring. -/
noncomputable def valuedIntegerBasis59 :
    Module.Basis (Fin 58) RationalIntegerRing59 (ValuedIntegerRing 59 K) := by
  simpa using (dworkParameterPowerBasis 59 K).map
    (dworkValuedAlgEquiv59 K).toLinearEquiv

noncomputable instance instModuleFreeValuedInteger59 :
    Module.Free RationalIntegerRing59 (ValuedIntegerRing 59 K) :=
  Module.Free.of_basis (valuedIntegerBasis59 K)

noncomputable instance instModuleFiniteValuedInteger59 :
    Module.Finite RationalIntegerRing59 (ValuedIntegerRing 59 K) :=
  Module.Finite.of_basis (valuedIntegerBasis59 K)

/-- Extension of the rational maximal ideal to the local integer ring is
exactly the 58th power of the lambda ideal. -/
theorem map_rationalMaximalIdeal_eq_lambdaIdeal_pow_pred :
    Ideal.map
        (algebraMap RationalIntegerRing59 (ValuedIntegerRing 59 K))
        (IsLocalRing.maximalIdeal RationalIntegerRing59) =
      (lambdaIdeal 59 K) ^ 58 := by
  rw [← rationalPadicPrimeIdeal_eq_maximalIdeal (p := 59)]
  rw [rationalPadicPrimeIdeal, Ideal.map_span, Set.image_singleton]
  simpa only [map_natCast] using
    (span_natCast_prime_eq_lambdaIdeal_pow_pred (p := 59) (K := K))

/-- The integral trace of an element in the lambda ideal lies in the
rational maximal ideal.  The proof reduces modulo the rational maximal
ideal: lambda becomes nilpotent of exponent 58, so its quotient trace
vanishes. -/
theorem integerTrace_mem_maximalIdeal_of_mem_lambda
    {y : ValuedIntegerRing 59 K} (hy : y ∈ lambdaIdeal 59 K) :
    Algebra.trace RationalIntegerRing59 (ValuedIntegerRing 59 K) y ∈
      IsLocalRing.maximalIdeal RationalIntegerRing59 := by
  let pR : Ideal RationalIntegerRing59 :=
    IsLocalRing.maximalIdeal RationalIntegerRing59
  let pS : Ideal (ValuedIntegerRing 59 K) :=
    Ideal.map (algebraMap RationalIntegerRing59 (ValuedIntegerRing 59 K)) pR
  have hypow : y ^ 58 ∈ pS := by
    rw [show pS = (lambdaIdeal 59 K) ^ 58 by
      exact map_rationalMaximalIdeal_eq_lambdaIdeal_pow_pred K]
    exact Ideal.pow_mem_pow hy 58
  have hnil : IsNilpotent (Ideal.Quotient.mk pS y) := by
    refine ⟨58, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hypow
  have htraceZero :
      Algebra.trace (RationalIntegerRing59 ⧸ pR)
          (ValuedIntegerRing 59 K ⧸ pS)
          (Ideal.Quotient.mk pS y) = 0 :=
    (Algebra.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hcompat := Algebra.trace_quotient_mk (R := RationalIntegerRing59)
    (S := ValuedIntegerRing 59 K) y
  change Algebra.trace (RationalIntegerRing59 ⧸ pR)
      (ValuedIntegerRing 59 K ⧸ pS)
      (Ideal.Quotient.mk pS y) =
        Ideal.Quotient.mk pR
          (Algebra.trace RationalIntegerRing59 (ValuedIntegerRing 59 K) y)
    at hcompat
  rw [htraceZero] at hcompat
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcompat.symm

/-- The rational 59-adic integer action is compatible with inclusion in the
local cyclotomic field. -/
instance instIsScalarTowerRationalIntegerValuedIntegerLambda59 :
    IsScalarTower RationalIntegerRing59 (ValuedIntegerRing 59 K)
      (LambdaCompletion59 K) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def]
  change ((algebraMap RationalCompletion59 (LambdaCompletion59 K)
      (r : RationalCompletion59)) * (x : LambdaCompletion59 K)) * y =
    algebraMap RationalCompletion59 (LambdaCompletion59 K)
      (r : RationalCompletion59) * ((x : LambdaCompletion59 K) * y)
  exact mul_assoc _ _ _

/-- Localization identifies the integral trace with the genuine local field
trace on every element of the local integer ring. -/
theorem localTrace59_valuedInteger_eq_integerTrace
    (y : ValuedIntegerRing 59 K) :
    Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
        (valuedIntegerToLambdaCompletion59 K y) =
      algebraMap RationalIntegerRing59 RationalCompletion59
        (Algebra.trace RationalIntegerRing59 (ValuedIntegerRing 59 K) y) := by
  change Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
      (algebraMap (ValuedIntegerRing 59 K) (LambdaCompletion59 K) y) = _
  exact Algebra.trace_localization RationalIntegerRing59
    (nonZeroDivisors RationalIntegerRing59) y

/-- The local field trace of every local integer is a rational 59-adic
integer. -/
theorem exists_rationalInteger_eq_localTrace_valuedInteger59
    (y : ValuedIntegerRing 59 K) :
    ∃ t : RationalIntegerRing59,
      (t : RationalCompletion59) =
        Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (valuedIntegerToLambdaCompletion59 K y) := by
  refine ⟨Algebra.trace RationalIntegerRing59 (ValuedIntegerRing 59 K) y, ?_⟩
  exact (localTrace59_valuedInteger_eq_integerTrace K y).symm

/-- The local trace of a lambda-divisible integer is itself divisible by 59
inside the rational completed integer ring. -/
theorem exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda
    {y : ValuedIntegerRing 59 K} (hy : y ∈ lambdaIdeal 59 K) :
    ∃ t : RationalIntegerRing59,
      Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
          (valuedIntegerToLambdaCompletion59 K y) =
        (59 : RationalCompletion59) * (t : RationalCompletion59) := by
  have ht := integerTrace_mem_maximalIdeal_of_mem_lambda K hy
  rw [← rationalPadicPrimeIdeal_eq_maximalIdeal (p := 59)] at ht
  change Algebra.trace RationalIntegerRing59 (ValuedIntegerRing 59 K) y ∈
    Ideal.span ({(59 : RationalIntegerRing59)} : Set RationalIntegerRing59) at ht
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp ht
  refine ⟨t, ?_⟩
  rw [localTrace59_valuedInteger_eq_integerTrace K y, ← ht, map_mul]
  change (t : RationalCompletion59) *
      ((59 : RationalIntegerRing59) : RationalCompletion59) =
    59 * (t : RationalCompletion59)
  have h59 : ((59 : RationalIntegerRing59) : RationalCompletion59) = 59 := rfl
  rw [h59]
  ring

end Fermat.FiftyNine.Conservation.LocalIntegralTrace59
