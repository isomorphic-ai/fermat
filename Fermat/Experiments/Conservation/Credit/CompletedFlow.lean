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
import Fermat.Experiments.Conservation.Credit.Flow
import KummerCriterion.CyclotomicUnits.LogDomain
import KummerCriterion.CyclotomicUnits.KummerLogCoefficient.Coordinates

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

/-! ## Actual-unit conservation -/

/-- Kummer's completed logarithm bundled as the multiplicative-to-additive
flow on actual principal units.

The multiplicative wrapper is only a change of notation on the additive
completed local ring.  Thus this map is constructed from `completedLog`,
whose multiplication law is already proved by the pinned same-prime
logarithm, rather than supplied as an independent flow. -/
noncomputable def completedLogFlow :
    completedLogDomain (p := p) (K := K) →*
      Multiplicative (DworkCompleteIntegerRing p K) where
  toFun u := Multiplicative.ofAdd
    (completedLog (p := p) (K := K) u)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [completedLog_one]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    simp [completedLog_mul]

@[simp]
theorem completedLogFlow_apply
    (u : completedLogDomain (p := p) (K := K)) :
    Multiplicative.toAdd (completedLogFlow (p := p) (K := K) u) =
      completedLog (p := p) (K := K) u :=
  rfl

/-- Product conservation for actual principal units, exposed through the
generated flow object. -/
theorem completedLogFlow_mul
    (u v : completedLogDomain (p := p) (K := K)) :
    completedLogFlow (p := p) (K := K) (u * v) =
      completedLogFlow (p := p) (K := K) u *
        completedLogFlow (p := p) (K := K) v :=
  (completedLogFlow (p := p) (K := K)).map_mul u v

/-! The further projection from this completed value to the finite
high-character coefficient space is precisely the missing prime-cube
comparison recorded in `FINDINGS.md`; it is not postulated here. -/

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

/-! ## Prime-power Dwork coefficients -/

/-- Parameter-adic depth by `q * (p - 1)` forces every Dwork power-basis
coefficient into the `q`th power of the rational prime ideal.

This is the arbitrary-precision extractor missing from the packaged
mod-`p` coordinate.  It stops before reducing the coefficient, so the
prime-square information required by the high flow is retained. -/
theorem
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_pow_of_mem_parameterIdeal_pow_mul_pred
    {x y : DworkCompleteIntegerRing p K} (q : ℕ)
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (q * (p - 1)))
    (i : Fin (p - 1)) :
    (dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i ∈
      (rationalPadicPrimeIdeal p) ^ q := by
  let R₀ : Type := RationalPadicIntegerRing p
  let S : Type _ := DworkCompleteIntegerRing p K
  rcases
      exists_natCast_prime_pow_mul_eq_of_mem_dworkParameterIdeal_pow_mul_pred_add
        (p := p) (K := K) q 0 (by simpa using hxy) with
    ⟨z, _hz, hz⟩
  have hz' :
      (p : R₀) ^ q • z = x - y := by
    change algebraMap R₀ S ((p : R₀) ^ q) * z = x - y
    simpa [R₀, S, map_pow] using hz
  have hrepr :
      (dworkParameterPowerBasis p K).repr (x - y) i =
        (p : R₀) ^ q * (dworkParameterPowerBasis p K).repr z i := by
    calc
      (dworkParameterPowerBasis p K).repr (x - y) i =
          (dworkParameterPowerBasis p K).repr ((p : R₀) ^ q • z) i := by
        rw [hz']
      _ = (((p : R₀) ^ q) •
          (dworkParameterPowerBasis p K).repr z) i := by
        rw [(dworkParameterPowerBasis p K).repr.map_smul]
      _ = (p : R₀) ^ q *
          (dworkParameterPowerBasis p K).repr z i := by
        simp [Pi.smul_apply, smul_eq_mul]
  have hp :
      (p : R₀) ^ q ∈ (rationalPadicPrimeIdeal p) ^ q := by
    simp [rationalPadicPrimeIdeal, Ideal.span_singleton_pow]
  have hsub :
      (dworkParameterPowerBasis p K).repr (x - y) i =
        (dworkParameterPowerBasis p K).repr x i -
          (dworkParameterPowerBasis p K).repr y i := by
    exact congrArg (fun f => f i)
      ((dworkParameterPowerBasis p K).repr.map_sub x y)
  rw [← hsub, hrepr]
  exact ((rationalPadicPrimeIdeal p) ^ q).mul_mem_right _ hp

/-- Exact depth `2 * p` retains two rational prime-adic layers in every
Dwork power-basis coefficient. -/
theorem
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_two_mul_prime
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (2 * p))
    (i : Fin (p - 1)) :
    (dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i ∈
      (rationalPadicPrimeIdeal p) ^ 2 := by
  apply
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_pow_of_mem_parameterIdeal_pow_mul_pred
      (p := p) (K := K) 2
  exact Ideal.pow_le_pow_right (by omega) hxy

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
