/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# One full triangular residual step at 59

Normalization adds one lambda-depth and triangular contraction doubles it,
giving the exact recurrence `s ↦ 2*s+2`.  The additive Kummer remainder is
absorbed through a spectral unit, producing an actual multiplicative
factorization in the extension.

The field norm of the extracted base is computed explicitly.  Its constant
part is handled by the first-unit 59th-power kernel, while all 58 elementary
norm factors already lie in `U60`.  Thus each step returns a concrete `U60`
unit representing the norm of its base factor.
-/
import Fermat.Experiments.Conservation.PrimeTriangularExplicitNorm
import Fermat.Experiments.Conservation.PrimeTriangularSpectralAbsorption
import Fermat.Exponents.FiftyNine.Conservation.CriticalUnitPowerKernel59
import Fermat.Exponents.FiftyNine.Conservation.TriangularResidualNormalization59
import Mathlib.Tactic

open scoped NumberField WithZero BigOperators
open Polynomial

noncomputable section

set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.TriangularResidualStep59

open Fermat.Conservation.PrimeTriangularUnitFactorization
open Fermat.Conservation.PrimeTriangularNormBounds
open Fermat.Conservation.PrimeTriangularSpectralAbsorption
open Fermat.Conservation.PrimeTriangularExplicitNorm
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
open Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
open Fermat.FiftyNine.Conservation.TriangularResidualNormalization59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

local instance : NontriviallyNormedField (F59 K) :=
  lambdaField59NontriviallyNormedField K

noncomputable local instance : FiniteDimensional (F59 K) (E59 K) :=
  (twistedLambdaPowerBasis59 K).finite

/-- One complete residual round adds one lambda and then squares depth. -/
def nextDepth59 (s : ℕ) : ℕ := 2 * s + 2

/-- The explicit base factor extracted by one triangular residual round. -/
def triangularBase59 (y : E59 K) : E59 K :=
  algebraMap (F59 K) (E59 K) (residualConstant59 K y) *
    aeval (twistedLambdaRoot59 K)
      (triangularProduct (normalizedResidualPolynomial59 K y) 58)

theorem depthRadius59_lt_one (s : ℕ) (hs : 0 < s) :
    depthRadius59 K s < 1 := by
  rw [depthRadius59, Valued.toNormedField.norm_lt_one_iff,
    canonicalLambda59_pow_valuation]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- One genuine multiplicative triangular round realizes
`s ↦ 2*s+2` on all selected-root coordinates. -/
theorem exists_residual_step
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    ∃ z : E59 K,
      residualElement59 K y =
          triangularBase59 K y * residualElement59 K z ∧
      HasCoordinateDepth59 K z (nextDepth59 s) := by
  let f : (F59 K)[X] := normalizedResidualPolynomial59 K y
  obtain ⟨hf0, hdeg, hf⟩ := normalizedResidualPolynomial59_data K y s hy
  let q : ℝ := depthRadius59 K (s + 1)
  have hfnorm : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q := by
    intro j hj
    apply (valuation_le_exp_neg_iff_norm_le_depthRadius59 K _ (s + 1)).mp
    exact hf j hj
  obtain ⟨z, hzEq, hzSpectral⟩ :=
    exists_evaluated_triangular_absorption_spectralNorm_le_sq
      (F := F59 K) (E := E59 K)
      f hf0 59 (by norm_num) hdeg q
      (depthRadius59_nonneg K (s + 1))
      (depthRadius59_le_one K (s + 1))
      (depthRadius59_lt_one K (s + 1) (by omega))
      hfnorm (twistedLambdaRoot59 K) (twistedLambda59 K)
      (twistedLambdaRoot59_pow K)
      (le_of_lt (spectralNorm_twistedLambdaRoot59_lt_one K))
  refine ⟨z, ?_, ?_⟩
  · rw [residualElement59_eq_constant_mul_normalized K y s hy]
    rw [hzEq]
    simp only [triangularBase59, residualElement59, f]
    ring
  · intro i
    apply twistedLambdaPowerBasis59_coeff_valuation_le_exp_neg_of_spectralNorm
      K z (nextDepth59 s)
    have hdepth : nextDepth59 s = 2 * (s + 1) := by
      simp [nextDepth59]
      omega
    rw [hdepth, ← depthRadius59_sq K (s + 1)]
    simpa [q] using hzSpectral

private theorem exp_factor_depth60
    (s j : ℕ) (hj : 0 < j) :
    WithZero.exp (-((s + 1 : ℕ) : ℤ)) ^ 59 *
        WithZero.exp (-1 : ℤ) ^ j ≤
      WithZero.exp (-60 : ℤ) := by
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, WithZero.exp_le_exp]
  simp only [nsmul_eq_mul]
  push_cast
  omega

/-- Every explicit elementary norm extracted from a residual round already
lies at depth 60. -/
theorem triangularNormPerturbation59_depth60
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 58) :
    Valued.v
        (triangularCoefficient (normalizedResidualPolynomial59 K y) j ^ 59 *
          twistedLambda59 K ^ j) ≤
      WithZero.exp (-60 : ℤ) := by
  let f : (F59 K)[X] := normalizedResidualPolynomial59 K y
  let q : ℝ := depthRadius59 K (s + 1)
  obtain ⟨hf0, hdeg, hf⟩ := normalizedResidualPolynomial59_data K y s hy
  have hfnorm : ∀ n : ℕ, 0 < n → ‖f.coeff n‖ ≤ q := by
    intro n hn
    apply (valuation_le_exp_neg_iff_norm_le_depthRadius59 K _ (s + 1)).mp
    exact hf n hn
  have hcNorm : ‖triangularCoefficient f j‖ ≤ q :=
    triangularCoefficient_norm_le f q
      (depthRadius59_nonneg K (s + 1))
      (depthRadius59_le_one K (s + 1)) hfnorm j
      (Finset.mem_Icc.mp hj).1
  have hcVal : Valued.v (triangularCoefficient f j) ≤
      WithZero.exp (-((s + 1 : ℕ) : ℤ)) :=
    (valuation_le_exp_neg_iff_norm_le_depthRadius59 K _ (s + 1)).mpr hcNorm
  rw [map_mul, map_pow, map_pow, twistedLambda59_valuation]
  apply le_trans (mul_le_mul_left
    (pow_le_pow_left' hcVal 59) (WithZero.exp (-1 : ℤ) ^ j))
  exact exp_factor_depth60 s j (Finset.mem_Icc.mp hj).1

/-- The actual field norm of the explicit base extracted in one residual
round is represented by a concrete unit in `U60`. -/
theorem exists_triangularBase59_normUnit_mem_U60
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    ∃ u : (F59 K)ˣ,
      (u : F59 K) = Algebra.norm (F59 K) (triangularBase59 K y) ∧
      u ∈ U60 K := by
  classical
  let f : (F59 K)[X] := normalizedResidualPolynomial59 K y
  let u0 : F59 K := residualConstant59 K y
  have hu0val : Valued.v u0 = 1 := residualConstant59_valuation K y s hy
  have hu0ne : u0 ≠ 0 := residualConstant59_ne_zero K y s hy
  let u0Unit : (F59 K)ˣ := Units.mk0 u0 hu0ne
  have hu0Sub : Valued.v ((u0Unit : F59 K) - 1) ≤
      WithZero.exp (-1 : ℤ) := by
    change Valued.v (residualConstant59 K y - 1) ≤ _
    rw [residualConstant59_eq, add_sub_cancel_left, map_mul,
      twistedLambda59_valuation]
    have hcoeff := selectedRootPolynomial59_coeff_depth K y s hy 0
    calc
      WithZero.exp (-1 : ℤ) *
          Valued.v ((twistedLambdaPowerBasisPolynomial59 K y).coeff 0) ≤
        WithZero.exp (-1 : ℤ) * WithZero.exp (-(s : ℤ)) :=
          mul_le_mul_right hcoeff _
      _ ≤ WithZero.exp (-1 : ℤ) * 1 := by
        apply mul_le_mul_right
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      _ = WithZero.exp (-1 : ℤ) := mul_one _
  have hu0PowMem : u0Unit ^ 59 ∈ U60 K :=
    pow_fiftyNine_mem_U60_of_mem_U1 K u0Unit hu0Sub
  let term : ℕ → F59 K := fun j ↦
    triangularCoefficient f j ^ 59 * twistedLambda59 K ^ j
  have htermDepth : ∀ j ∈ Finset.Icc 1 58,
      Valued.v (term j) ≤ WithZero.exp (-60 : ℤ) := by
    intro j hj
    exact triangularNormPerturbation59_depth60 K y s hy j hj
  have htermLt : ∀ j ∈ Finset.Icc 1 58, Valued.v (term j) < 1 := by
    intro j hj
    exact (htermDepth j hj).trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  have hfactorVal : ∀ j ∈ Finset.Icc 1 58,
      Valued.v (1 + term j) = 1 := by
    intro j hj
    exact (Valued.v : Valuation (F59 K) ℤᵐ⁰).map_one_add_of_lt
      (htermLt j hj)
  have hfactorNe : ∀ j ∈ Finset.Icc 1 58, 1 + term j ≠ 0 := by
    intro j hj
    apply (Valuation.ne_zero_iff (Valued.v : Valuation (F59 K) ℤᵐ⁰)).mp
    rw [hfactorVal j hj]
    exact one_ne_zero
  let factorUnit : ℕ → (F59 K)ˣ := fun j ↦
    if hj : j ∈ Finset.Icc 1 58 then Units.mk0 (1 + term j) (hfactorNe j hj)
    else 1
  have hfactorUnitVal : ∀ j ∈ Finset.Icc 1 58,
      (factorUnit j : F59 K) = 1 + term j := by
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ 58 := Finset.mem_Icc.mp hj
    simp [factorUnit, hj']
  have hfactorMem : ∀ j ∈ Finset.Icc 1 58, factorUnit j ∈ U60 K := by
    intro j hj
    rw [mem_lambdaOneUnits]
    rw [hfactorUnitVal j hj, add_sub_cancel_left]
    exact htermDepth j hj
  let productUnit : (F59 K)ˣ := ∏ j ∈ Finset.Icc 1 58, factorUnit j
  have hproductMem : productUnit ∈ U60 K := by
    exact Subgroup.prod_mem (U60 K) hfactorMem
  have hproductVal : (productUnit : F59 K) =
      ∏ j ∈ Finset.Icc 1 58, (1 + term j) := by
    dsimp [productUnit]
    rw [Units.coe_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact hfactorUnitVal j hj
  have hnormProduct :
      Algebra.norm (F59 K)
          (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) =
        ∏ j ∈ Finset.Icc 1 58, (1 + term j) := by
    exact norm_aeval_triangularProduct 59 (F59 K)
      (lambdaLocalPrimitiveRoot59 K) (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K) f 58 (by norm_num) (by norm_num)
  have hfinrank : Module.finrank (F59 K) (E59 K) = 59 := by
    calc
      Module.finrank (F59 K) (E59 K) =
          (twistedLambdaPowerBasis59 K).dim :=
        (twistedLambdaPowerBasis59 K).finrank
      _ = 59 := twistedLambdaPowerBasis59_dim K
  have hnormBase : Algebra.norm (F59 K) (triangularBase59 K y) =
      u0 ^ 59 * ∏ j ∈ Finset.Icc 1 58, (1 + term j) := by
    rw [triangularBase59, map_mul, Algebra.norm_algebraMap, hfinrank]
    exact congrArg (fun z : F59 K ↦ u0 ^ 59 * z) hnormProduct
  let baseNormUnit : (F59 K)ˣ := u0Unit ^ 59 * productUnit
  refine ⟨baseNormUnit, ?_, (U60 K).mul_mem hu0PowMem hproductMem⟩
  dsimp [baseNormUnit]
  change u0 ^ 59 * (productUnit : F59 K) = _
  rw [hproductVal, hnormBase]

/-- One full recurrence step: exact extension-field factorization, the
coordinate recurrence `s ↦ 2*s+2`, and an actual `U60` representative for
the norm of the extracted base. -/
theorem exists_residual_step_with_normUnit
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    ∃ (z : E59 K) (u : (F59 K)ˣ),
      residualElement59 K y =
          triangularBase59 K y * residualElement59 K z ∧
      HasCoordinateDepth59 K z (nextDepth59 s) ∧
      (u : F59 K) = Algebra.norm (F59 K) (triangularBase59 K y) ∧
      u ∈ U60 K := by
  obtain ⟨z, hzEq, hzDepth⟩ := exists_residual_step K y s hy
  obtain ⟨u, huEq, huMem⟩ :=
    exists_triangularBase59_normUnit_mem_U60 K y s hy
  exact ⟨z, u, hzEq, hzDepth, huEq, huMem⟩

end Fermat.FiftyNine.Conservation.TriangularResidualStep59
