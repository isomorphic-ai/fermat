/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The critical norm-image gap at 59

An arbitrary extension norm in `U59` is put into its integral selected-root
normal form. Its constant coordinate, finite triangular base, and residual
are then treated separately. The residual is driven through the five actual
depth rounds `0 -> 2 -> 6 -> 14 -> 30 -> 62`; the constant is controlled by
residue Frobenius and the first-unit power kernel; and valuation separation
pushes the triangular base from `U59` into `U60`.

Recombining the exact norm factors proves that the actual norm image has no
nontrivial class in `U59 / U60`. In particular, the explicit correction and
the local primitive root are not norms, so the genuine Kummer cup is nonzero.
-/
import Fermat.Exponents.FiftyNine.Conservation.FiveStepResidual59
import Fermat.Exponents.FiftyNine.Conservation.InitialIntegralDecomposition59
import Fermat.Exponents.FiftyNine.Conservation.PowerU1Reflection59
import Fermat.Exponents.FiftyNine.Conservation.TriangularNormSeparation59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59
import Mathlib.Tactic

open scoped NumberField WithZero BigOperators
open Polynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Fermat.FiftyNine.Conservation.NormImageBridge59

open Fermat.Conservation.PrimeTriangularUnitFactorization
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
open Fermat.FiftyNine.Conservation.TriangularNormSeparation59
open Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
open Fermat.FiftyNine.Conservation.TriangularResidualNormalization59
open Fermat.FiftyNine.Conservation.FiveStepResidual59
open Fermat.FiftyNine.Conservation.InitialIntegralDecomposition59
open Fermat.FiftyNine.Conservation.PowerU1Reflection59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

local instance : NontriviallyNormedField (F59 K) :=
  lambdaField59NontriviallyNormedField K

noncomputable local instance : FiniteDimensional (F59 K) (E59 K) :=
  (twistedLambdaPowerBasis59 K).finite

/-- Every actual extension norm that enters the critical layer `U59`
already lies in `U60`. -/
theorem normUnit_mem_U60_of_eq_norm_of_mem_U59
    (beta : E59 K) (normUnit : (F59 K)ˣ)
    (hnormEq : (normUnit : F59 K) = Algebra.norm (F59 K) beta)
    (hnorm59 : normUnit ∈ U59 K) :
    normUnit ∈ U60 K := by
  have hnormDepth59 :
      Valued.v (Algebra.norm (F59 K) beta - 1) ≤
        WithZero.exp (-59 : ℤ) := by
    have h := hnorm59
    rw [mem_lambdaOneUnits] at h
    rw [hnormEq] at h
    norm_num at h ⊢
    exact h
  have hnormLt : Valued.v (Algebra.norm (F59 K) beta - 1) < 1 :=
    hnormDepth59.trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  have hnormVal : Valued.v (Algebra.norm (F59 K) beta) = 1 := by
    have hone :=
      (Valued.v : Valuation (F59 K) ℤᵐ⁰).map_one_add_of_lt hnormLt
    simpa only [add_sub_cancel] using hone
  obtain ⟨f, c0, P, y0, hbetaFactor, hc0Val, hf0, hfDeg, hf,
      hP, hPspectral, hPne, hy0⟩ :=
    exists_initial_integral_decomposition K beta hnormVal
  obtain ⟨residualUnit, hresidualEq, hresidual60⟩ :=
    exists_residualElement59_normUnit_mem_U60_of_depth_zero K y0 hy0
  have htriangularDepth1 := norm_aeval_triangularProduct_mem_U1 K f hf
  have htriangularLt :
      Valued.v
          (Algebra.norm (F59 K)
              (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) - 1) <
        1 :=
    htriangularDepth1.trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  have htriangularVal :
      Valued.v
          (Algebra.norm (F59 K)
            (aeval (twistedLambdaRoot59 K) (triangularProduct f 58))) = 1 := by
    have hone :=
      (Valued.v : Valuation (F59 K) ℤᵐ⁰).map_one_add_of_lt htriangularLt
    simpa only [add_sub_cancel] using hone
  have htriangularNe :
      Algebra.norm (F59 K)
          (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) ≠ 0 := by
    apply (Valuation.ne_zero_iff (Valued.v : Valuation (F59 K) ℤᵐ⁰)).mp
    rw [htriangularVal]
    exact one_ne_zero
  let triangularUnit : (F59 K)ˣ := Units.mk0
    (Algebra.norm (F59 K)
      (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)))
    htriangularNe
  have htriangularEq :
      (triangularUnit : F59 K) = Algebra.norm (F59 K)
        (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) := rfl
  have htriangular1 : triangularUnit ∈ lambdaOneUnits K 1 (by norm_num) := by
    rw [mem_lambdaOneUnits, htriangularEq]
    exact htriangularDepth1
  have hc0ne : c0 ≠ 0 := by
    apply (Valuation.ne_zero_iff (Valued.v : Valuation (F59 K) ℤᵐ⁰)).mp
    rw [hc0Val]
    exact one_ne_zero
  let constantUnit : (F59 K)ˣ := Units.mk0 c0 hc0ne
  have hfinrank : Module.finrank (F59 K) (E59 K) = 59 := by
    calc
      Module.finrank (F59 K) (E59 K) =
          (twistedLambdaPowerBasis59 K).dim :=
        (twistedLambdaPowerBasis59 K).finrank
      _ = 59 := twistedLambdaPowerBasis59_dim K
  have hunitFactor :
      normUnit = constantUnit ^ 59 * triangularUnit * residualUnit := by
    apply Units.ext
    change (normUnit : F59 K) =
      c0 ^ 59 * (triangularUnit : F59 K) * (residualUnit : F59 K)
    rw [hnormEq, hbetaFactor, map_mul, map_mul, Algebra.norm_algebraMap,
      hfinrank, hP, ← htriangularEq, ← hresidualEq]
  let U1 : Subgroup (F59 K)ˣ := lambdaOneUnits K 1 (by norm_num)
  have hnorm1 : normUnit ∈ U1 := by
    exact lambdaOneUnits_mono K (m := 1) (n := 59) (by norm_num) hnorm59
  have hresidual1 : residualUnit ∈ U1 := by
    exact lambdaOneUnits_mono K (m := 1) (n := 60) (by norm_num) hresidual60
  have hconstantPowEq :
      constantUnit ^ 59 =
        normUnit * (triangularUnit * residualUnit)⁻¹ := by
    rw [hunitFactor]
    group
  have hconstantPow1 : constantUnit ^ 59 ∈ U1 := by
    rw [hconstantPowEq]
    exact U1.mul_mem hnorm1 (U1.inv_mem (U1.mul_mem htriangular1 hresidual1))
  have hconstant1 : constantUnit ∈ U1 :=
    mem_U1_of_pow_fiftyNine_mem_U1 K constantUnit hconstantPow1
  have hconstantPow60 : constantUnit ^ 59 ∈ U60 K := by
    apply pow_fiftyNine_mem_U60_of_mem_U1 K constantUnit
    simpa [U1] using hconstant1
  have hresidual59 : residualUnit ∈ U59 K :=
    U60_le_U59 K hresidual60
  have hconstantPow59 : constantUnit ^ 59 ∈ U59 K :=
    U60_le_U59 K hconstantPow60
  have htriangularFactorEq :
      triangularUnit =
        (constantUnit ^ 59)⁻¹ * normUnit * residualUnit⁻¹ := by
    rw [hunitFactor]
    group
  have htriangular59 : triangularUnit ∈ U59 K := by
    rw [htriangularFactorEq]
    exact (U59 K).mul_mem
      ((U59 K).mul_mem ((U59 K).inv_mem hconstantPow59) hnorm59)
      ((U59 K).inv_mem hresidual59)
  have htriangularDepth59 :
      Valued.v
          (Algebra.norm (F59 K)
              (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) - 1) ≤
        WithZero.exp (-59 : ℤ) := by
    have h := htriangular59
    rw [mem_lambdaOneUnits] at h
    rw [htriangularEq] at h
    norm_num at h ⊢
    exact h
  have htriangularDepth60 :=
    norm_aeval_triangularProduct_mem_U60_of_mem_U59 K f hf
      htriangularDepth59
  have htriangular60 : triangularUnit ∈ U60 K := by
    rw [mem_lambdaOneUnits]
    rw [htriangularEq]
    norm_num at htriangularDepth60 ⊢
    exact htriangularDepth60
  rw [hunitFactor]
  exact (U60 K).mul_mem
    ((U60 K).mul_mem hconstantPow60 htriangular60) hresidual60

/-- Unit-hom form of the critical norm-image depth gap. -/
theorem twistedLambdaNormUnits59_mem_U60_of_mem_U59
    (beta : (E59 K)ˣ)
    (hbeta : twistedLambdaNormUnits59 K beta ∈ U59 K) :
    twistedLambdaNormUnits59 K beta ∈ U60 K := by
  apply normUnit_mem_U60_of_eq_norm_of_mem_U59 K
    (beta : E59 K) (twistedLambdaNormUnits59 K beta)
  · rfl
  · exact hbeta

/-- The actual norm image on the critical quotient is trivial. -/
theorem normImageCriticalUnitLayer59_eq_bot :
    normImageCriticalUnitLayer59 K = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, huNorm, rfl⟩ := hx
    have huNorm' := huNorm
    change ((u : U59 K) : (F59 K)ˣ) ∈
      (twistedLambdaNormUnits59 K).range at huNorm'
    obtain ⟨beta, hbeta⟩ := huNorm'
    have hu60 : ((u : U59 K) : (F59 K)ˣ) ∈ U60 K := by
      rw [← hbeta]
      apply twistedLambdaNormUnits59_mem_U60_of_mem_U59 K beta
      rw [hbeta]
      exact u.property
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (Subgroup.mem_subgroupOf).mpr hu60
  · exact bot_le

/-- The explicit correction is not an actual norm from the twisted Kummer
extension. -/
theorem primitiveRootNormCorrection59_not_norm :
    ¬ ∃ beta : E59 K,
      Algebra.norm (F59 K) beta = primitiveRootNormCorrection59 K := by
  rintro ⟨beta, hbeta⟩
  have hmem : correctionFieldUnit59 K ∈ U60 K := by
    apply normUnit_mem_U60_of_eq_norm_of_mem_U59 K beta
      (correctionFieldUnit59 K)
    · simpa using hbeta.symm
    · exact correctionFieldUnit59_mem_U59 K
  exact correctionFieldUnit59_not_mem_U60 K hmem

/-- Therefore the local primitive 59th root is not a norm from the concrete
twisted-lambda Kummer extension. -/
theorem lambdaLocalPrimitiveRoot59_not_norm :
    ¬ ∃ beta : E59 K,
      Algebra.norm (F59 K) beta = lambdaLocalPrimitiveRoot59 K := by
  exact (not_congr (primitiveRoot_is_norm_iff_correction_is_norm K)).mpr
    (primitiveRootNormCorrection59_not_norm K)

/-- The genuine twisted-lambda Kummer cup is therefore nonzero. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero :
    twistedLambdaKummerCupH2Class59 K ≠ 0 := by
  exact
    (twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm K).mpr
      (lambdaLocalPrimitiveRoot59_not_norm K)

end Fermat.FiftyNine.Conservation.NormImageBridge59
