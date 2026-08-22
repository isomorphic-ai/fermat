/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Initial integral triangular decomposition at 59

A norm-unit extension element is first written in the selected-root power
basis and normalized by its unit constant coefficient. Although its
positive coefficients are only on the closed unit boundary, the selected
root is strictly inside the spectral unit ball; this makes the evaluated
triangular product a spectral unit and permits an exact multiplicative
residual decomposition of coordinate depth zero.
-/
import Fermat.Exponents.FiftyNine.Conservation.TriangularResidualStep59
import Mathlib.Tactic

open scoped NumberField WithZero BigOperators
open Polynomial

noncomputable section

set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.InitialIntegralDecomposition59

open Fermat.Conservation.PrimeTriangularUnitFactorization
open Fermat.Conservation.PrimeTriangularNormBounds
open Fermat.Conservation.PrimeTriangularSpectralContraction
open Fermat.Conservation.PrimeTriangularSpectralAbsorption
open Fermat.Conservation.SpectralNormProductRemainder
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59
open Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
open Fermat.FiftyNine.Conservation.TriangularResidualNormalization59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

local instance : NontriviallyNormedField (F59 K) :=
  lambdaField59NontriviallyNormedField K

noncomputable local instance : FiniteDimensional (F59 K) (E59 K) :=
  (twistedLambdaPowerBasis59 K).finite

/-- Initial integral decomposition of an arbitrary extension element whose
field norm is a valuation unit. The returned polynomial is normalized,
`P` is its literal evaluated triangular product, and the residual coordinate
vector starts the depth recurrence at zero. -/
theorem exists_initial_integral_decomposition
    (beta : E59 K)
    (hbeta : Valued.v (Algebra.norm (F59 K) beta) = 1) :
    ∃ (f : (F59 K)[X]) (c0 : F59 K) (P y0 : E59 K),
      beta = algebraMap (F59 K) (E59 K) c0 * P * residualElement59 K y0 ∧
      Valued.v c0 = 1 ∧
      f.coeff 0 = 1 ∧
      f.natDegree < 59 ∧
      (∀ j : ℕ, 0 < j → Valued.v (f.coeff j) ≤ 1) ∧
      P = aeval (twistedLambdaRoot59 K) (triangularProduct f 58) ∧
      spectralNorm (F59 K) (E59 K) P = 1 ∧
      P ≠ 0 ∧
      HasCoordinateDepth59 K y0 0 := by
  obtain ⟨fRaw, hfRawDeg, hbetaEval, hfRaw, hc0Val⟩ :=
    exists_integral_bounded_aeval_of_norm_valuation_eq_one K beta hbeta
  have hc0Ne : fRaw.coeff 0 ≠ 0 := by
    apply (Valuation.ne_zero_iff
      (Valued.v : Valuation (F59 K) ℤᵐ⁰)).mp
    rw [hc0Val]
    exact one_ne_zero
  let c0 : F59 K := fRaw.coeff 0
  let f : (F59 K)[X] := normalizeConstant fRaw
  have hf0 : f.coeff 0 = 1 := by
    exact normalizeConstant_coeff_zero fRaw hc0Ne
  have hfDeg : f.natDegree < 59 := by
    change (normalizeConstant fRaw).natDegree < 59
    apply lt_of_le_of_lt _ hfRawDeg
    rw [normalizeConstant]
    exact natDegree_mul_le.trans (by simp)
  have hfVal : ∀ j : ℕ, 0 < j → Valued.v (f.coeff j) ≤ 1 := by
    intro j hj
    change Valued.v ((normalizeConstant fRaw).coeff j) ≤ 1
    rw [normalizeConstant, coeff_C_mul]
    change Valued.v ((fRaw.coeff 0)⁻¹ * fRaw.coeff j) ≤ 1
    rw [map_mul, map_inv₀, hc0Val, inv_one, one_mul]
    by_cases hj59 : j < 59
    · exact hfRaw j hj59
    · have hzero : fRaw.coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le hfRawDeg (Nat.le_of_not_gt hj59))
      rw [hzero, map_zero]
      exact bot_le
  have hfNorm : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ 1 := by
    intro j hj
    rw [Valued.toNormedField.norm_le_one_iff]
    exact hfVal j hj
  let P : E59 K :=
    aeval (twistedLambdaRoot59 K) (triangularProduct f 58)
  have hP : spectralNorm (F59 K) (E59 K) P = 1 := by
    exact evaluated_triangularProduct_spectralNorm_eq_one_of_alpha_lt_one
      f 58 hfNorm (twistedLambdaRoot59 K)
        (spectralNorm_twistedLambdaRoot59_lt_one K)
  have hPNe : P ≠ 0 := by
    intro hzero
    rw [hzero, spectralNorm_zero] at hP
    norm_num at hP
  obtain ⟨delta, hdelta, hdeltaNorm⟩ :=
    exists_evaluated_triangular_remainder_spectralNorm_le_sq
      (F := F59 K) (E := E59 K)
      f hf0 59 (by norm_num) hfDeg 1 zero_le_one le_rfl hfNorm
      (twistedLambdaRoot59 K) (twistedLambda59 K)
      (twistedLambdaRoot59_pow K)
      (le_of_lt (spectralNorm_twistedLambdaRoot59_lt_one K))
  have hdeltaNorm' : spectralNorm (F59 K) (E59 K) delta ≤ 1 := by
    simpa using hdeltaNorm
  let y0 : E59 K := delta / P
  have hy0Norm : spectralNorm (F59 K) (E59 K) y0 ≤ 1 := by
    exact spectralNorm_div_le_of_eq_one delta P hP 1 hdeltaNorm'
  have hy0Depth : HasCoordinateDepth59 K y0 0 := by
    intro i
    apply twistedLambdaPowerBasis59_coeff_valuation_le_exp_neg_of_spectralNorm
      K y0 0
    simpa using hy0Norm
  have hbetaNormalized :
      beta = algebraMap (F59 K) (E59 K) c0 *
        aeval (twistedLambdaRoot59 K) f := by
    have hpoly := C_coeff_zero_mul_normalizeConstant fRaw hc0Ne
    calc
      beta = aeval (twistedLambdaRoot59 K) fRaw := hbetaEval
      _ = aeval (twistedLambdaRoot59 K) (C c0 * f) := by
        exact congrArg
          (fun g : (F59 K)[X] ↦ aeval (twistedLambdaRoot59 K) g)
          (by simpa [c0, f] using hpoly.symm)
      _ = algebraMap (F59 K) (E59 K) c0 *
          aeval (twistedLambdaRoot59 K) f := by simp
  refine ⟨f, c0, P, y0, ?_, ?_, hf0, hfDeg, hfVal, rfl, hP, hPNe,
    hy0Depth⟩
  · calc
      beta = algebraMap (F59 K) (E59 K) c0 *
          aeval (twistedLambdaRoot59 K) f := hbetaNormalized
      _ = algebraMap (F59 K) (E59 K) c0 *
          (P + algebraMap (F59 K) (E59 K) (twistedLambda59 K) * delta) := by
        rw [hdelta]
      _ = algebraMap (F59 K) (E59 K) c0 * P *
          residualElement59 K y0 := by
        rw [residualElement59]
        dsimp [y0]
        field_simp [hPNe]
  · exact hc0Val

end Fermat.FiftyNine.Conservation.InitialIntegralDecomposition59
