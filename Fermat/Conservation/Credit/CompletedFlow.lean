/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W1: completed Kummer flow

Kummer's same-prime logarithm turns congruence of principal units into
equality in every finite lambda-adic quotient.  Vandiver's depth argument
uses this comparison at the exact depth `2 * p`.  This file records that
generic bridge directly against the pinned `KummerCriterion` completion;
it neither imports nor recreates the classical Vandiver assembly.

The comparison is stated first for arbitrary depth.  The `2 * p`
specializations are consequences, not per-prime certificates.  The final
theorem proves that the completed logarithm commutes with the cyclotomic
action, providing the arithmetic gauge functoriality needed downstream.
-/
import Fermat.Conservation.Credit.Flow
import KummerCriterion.CyclotomicUnits.LogDomain

open NumberField
open scoped NumberField

namespace Fermat.Conservation.Credit.Flow

open KummerCriterion.CyclotomicUnits
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter.Conjugation

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-! ## Depth comparison -/

/-- Kummer's completed same-prime logarithm respects congruence in every
lambda-adic quotient.

The hypothesis compares the underlying valued integers of two already
normalized principal units.  No vanishing conclusion or arithmetic
certificate is included in the interface. -/
theorem completedLog_evalₐ_eq_of_sub_mem
    (u v : completedLogDomain (p := p) (K := K)) (N : ℕ)
    (huv :
      (((u : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K) -
          ((v : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K)) ∈
        (lambdaIdeal p K) ^ N) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (completedLog (p := p) (K := K) u) =
      AdicCompletion.evalₐ (lambdaIdeal p K) N
        (completedLog (p := p) (K := K) v) := by
  cases N with
  | zero =>
      rw [completedLog_evalₐ, completedLog_evalₐ]
      simp [completedLogCoord]
  | succ N =>
      rw [completedLog_evalₐ_succ, completedLog_evalₐ_succ]
      apply samePrimeFiniteLog_eq_of_sub_mem
      simpa [completedLogArg] using huv

/-- The general depth comparison at Vandiver's exact depth `2 * p`. -/
theorem completedLog_evalₐ_two_mul_prime_eq_of_sub_mem
    (u v : completedLogDomain (p := p) (K := K))
    (huv :
      (((u : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K) -
          ((v : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K)) ∈
        (lambdaIdeal p K) ^ (2 * p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (2 * p)
        (completedLog (p := p) (K := K) u) =
      AdicCompletion.evalₐ (lambdaIdeal p K) (2 * p)
        (completedLog (p := p) (K := K) v) :=
  completedLog_evalₐ_eq_of_sub_mem u v (2 * p) huv

/-- Equivalent completed-ideal form of the arbitrary-depth comparison. -/
theorem completedLog_sub_mem_completeLambda_pow_of_sub_mem
    (u v : completedLogDomain (p := p) (K := K)) (N : ℕ)
    (huv :
      (((u : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K) -
          ((v : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K)) ∈
        (lambdaIdeal p K) ^ N) :
    completedLog (p := p) (K := K) u -
        completedLog (p := p) (K := K) v ∈
      (dworkCompleteLambdaIdeal p K) ^ N := by
  apply dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
  rw [map_sub, completedLog_evalₐ_eq_of_sub_mem u v N huv, sub_self]

/-- The completed-ideal comparison at Vandiver's exact depth `2 * p`. -/
theorem completedLog_sub_mem_completeLambda_two_mul_prime_of_sub_mem
    (u v : completedLogDomain (p := p) (K := K))
    (huv :
      (((u : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K) -
          ((v : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K)) ∈
        (lambdaIdeal p K) ^ (2 * p)) :
    completedLog (p := p) (K := K) u -
        completedLog (p := p) (K := K) v ∈
      (dworkCompleteLambdaIdeal p K) ^ (2 * p) :=
  completedLog_sub_mem_completeLambda_pow_of_sub_mem u v (2 * p) huv

/-! ## Cyclotomic gauge functoriality -/

/-- The cyclotomic action preserves the completed-log principal-unit
domain. -/
noncomputable def completedLogDomainCyclotomic
    (a : KummerCriterion.CyclotomicUnitDelta p)
    (u : completedLogDomain (p := p) (K := K)) :
    completedLogDomain (p := p) (K := K) :=
  ⟨Units.map
      (valuedIntegerCyclotomicEquiv (p := p) K a).toMonoidHom
      (u : (ValuedIntegerRing p K)ˣ),
    by
      rw [KummerCriterion.Ideal.mem_oneUnitsSubgroup]
      change valuedIntegerCyclotomicEquiv (p := p) K a
          (((u : (ValuedIntegerRing p K)ˣ) :
              ValuedIntegerRing p K)) - 1 ∈ lambdaIdeal p K
      simpa only [map_sub, map_one] using
        (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
          (p := p) (K := K) a u.2)⟩

/-- The additive principal-unit coordinate commutes with the cyclotomic
action. -/
theorem completedLogArg_completedLogDomainCyclotomic
    (a : KummerCriterion.CyclotomicUnitDelta p)
    (u : completedLogDomain (p := p) (K := K)) :
    completedLogArg (p := p) (K := K)
        (completedLogDomainCyclotomic (p := p) (K := K) a u) =
      valuedIntegerCyclotomicEquiv (p := p) K a
        (completedLogArg (p := p) (K := K) u) := by
  simp [completedLogArg, completedLogDomainCyclotomic]

/-- Kummer's completed same-prime logarithm is equivariant for the
cyclotomic action.

The proof lifts the finite-log equivariance theorem quotient by quotient;
there is no supplied gauge law or selected-prime computation. -/
theorem dworkCompleteCyclotomicEquiv_completedLog
    (a : KummerCriterion.CyclotomicUnitDelta p)
    (u : completedLogDomain (p := p) (K := K)) :
    dworkCompleteCyclotomicEquiv (p := p) K a
        (completedLog (p := p) (K := K) u) =
      completedLog (p := p) (K := K)
        (completedLogDomainCyclotomic (p := p) (K := K) a u) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      rw [evalₐ_dworkCompleteCyclotomicEquiv,
        completedLog_evalₐ, completedLog_evalₐ]
      simp [completedLogCoord]
  | succ N =>
      rw [evalₐ_dworkCompleteCyclotomicEquiv,
        completedLog_evalₐ_succ, completedLog_evalₐ_succ]
      rw [samePrimeFiniteLog_eq_of_eq
        (p := p) (K := K) (N := N)
        (completedLogArg_completedLogDomainCyclotomic
          (p := p) (K := K) a u)
        (completedLogArg_mem (p := p) (K := K)
          (completedLogDomainCyclotomic (p := p) (K := K) a u))
        (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
          (p := p) (K := K) a
          (completedLogArg_mem (p := p) (K := K) u))]
      exact samePrimeFiniteLog_quotientMap_cyclotomic
        (p := p) (K := K) a
        (completedLogArg_mem (p := p) (K := K) u)

end Fermat.Conservation.Credit.Flow
