/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Normalize one twisted-lambda residual at 59

For an extension remainder `y`, form the selected-root polynomial for
`1 + twistedLambda * y`.  Its constant coefficient is a base one-unit.
Dividing by that coefficient leaves a normalized degree-`< 59` polynomial
whose positive coefficients have gained one integral lambda-depth.
-/
import Fermat.Exponents.FiftyNine.Conservation.TriangularSpectralDepth59
import Mathlib.Tactic

open scoped NumberField WithZero
open Polynomial

noncomputable section

namespace Fermat.FiftyNine.Conservation.TriangularResidualNormalization59

open Fermat.Conservation.PrimeTriangularUnitFactorization
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- Every selected-root coordinate of `y` has lambda-depth at least `s`. -/
def HasCoordinateDepth59 (y : E59 K) (s : ℕ) : Prop :=
  ∀ i : Fin (twistedLambdaPowerBasis59 K).dim,
    Valued.v ((twistedLambdaPowerBasis59 K).basis.repr y i) ≤
      WithZero.exp (-(s : ℤ))

/-- The selected-root polynomial representing `1 + twistedLambda * y`. -/
def residualPolynomial59 (y : E59 K) : (F59 K)[X] :=
  1 + C (twistedLambda59 K) * twistedLambdaPowerBasisPolynomial59 K y

/-- The base-field constant extracted from a residual polynomial. -/
def residualConstant59 (y : E59 K) : F59 K :=
  (residualPolynomial59 K y).coeff 0

/-- The residual polynomial after its constant coefficient is removed. -/
def normalizedResidualPolynomial59 (y : E59 K) : (F59 K)[X] :=
  normalizeConstant (residualPolynomial59 K y)

/-- The actual extension-field residual represented by `y`. -/
def residualElement59 (y : E59 K) : E59 K :=
  1 + algebraMap (F59 K) (E59 K) (twistedLambda59 K) * y

theorem aeval_residualPolynomial59 (y : E59 K) :
    aeval (twistedLambdaRoot59 K) (residualPolynomial59 K y) =
      residualElement59 K y := by
  rw [residualPolynomial59, residualElement59, map_add, map_one, map_mul,
    aeval_C, aeval_twistedLambdaPowerBasisPolynomial59]

theorem selectedRootPolynomial59_coeff_depth
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    ∀ j : ℕ,
      Valued.v ((twistedLambdaPowerBasisPolynomial59 K y).coeff j) ≤
        WithZero.exp (-(s : ℤ)) := by
  intro j
  by_cases hj : j < 59
  · have hjdim : j < (twistedLambdaPowerBasis59 K).dim := by
      rw [twistedLambdaPowerBasis59_dim]
      exact hj
    rw [twistedLambdaPowerBasisPolynomial59_coeff K y j hjdim]
    exact hy ⟨j, hjdim⟩
  · have hzero :
        (twistedLambdaPowerBasisPolynomial59 K y).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le
          (twistedLambdaPowerBasisPolynomial59_natDegree_lt K y)
          (Nat.le_of_not_gt hj))
    rw [hzero, map_zero]
    exact bot_le

theorem residualConstant59_eq (y : E59 K) :
    residualConstant59 K y =
      1 + twistedLambda59 K *
        (twistedLambdaPowerBasisPolynomial59 K y).coeff 0 := by
  simp [residualConstant59, residualPolynomial59, coeff_add]

private theorem twisted_coefficient_depth
    (y : E59 K) (s j : ℕ) (hy : HasCoordinateDepth59 K y s) :
    Valued.v
        (twistedLambda59 K *
          (twistedLambdaPowerBasisPolynomial59 K y).coeff j) ≤
      WithZero.exp (-((s + 1 : ℕ) : ℤ)) := by
  rw [map_mul, twistedLambda59_valuation]
  calc
    WithZero.exp (-1 : ℤ) *
        Valued.v ((twistedLambdaPowerBasisPolynomial59 K y).coeff j) ≤
      WithZero.exp (-1 : ℤ) * WithZero.exp (-(s : ℤ)) :=
        mul_le_mul_right (selectedRootPolynomial59_coeff_depth K y s hy j) _
    _ = WithZero.exp (-((s + 1 : ℕ) : ℤ)) := by
      rw [← WithZero.exp_add, WithZero.exp_inj]
      push_cast
      omega

/-- The extracted constant is a base one-unit. -/
theorem residualConstant59_valuation
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    Valued.v (residualConstant59 K y) = 1 := by
  rw [residualConstant59_eq]
  apply (Valued.v : Valuation (F59 K) ℤᵐ⁰).map_one_add_of_lt
  exact (twisted_coefficient_depth K y s 0 hy).trans_lt (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega)

theorem residualConstant59_ne_zero
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    residualConstant59 K y ≠ 0 := by
  apply (Valuation.ne_zero_iff
    (Valued.v : Valuation (F59 K) ℤᵐ⁰)).mp
  rw [residualConstant59_valuation K y s hy]
  exact one_ne_zero

theorem residualPolynomial59_natDegree_lt (y : E59 K) :
    (residualPolynomial59 K y).natDegree < 59 := by
  have hprod :
      (C (twistedLambda59 K) *
          twistedLambdaPowerBasisPolynomial59 K y).natDegree ≤
        (twistedLambdaPowerBasisPolynomial59 K y).natDegree := by
    calc
      (C (twistedLambda59 K) *
          twistedLambdaPowerBasisPolynomial59 K y).natDegree ≤
          (C (twistedLambda59 K)).natDegree +
            (twistedLambdaPowerBasisPolynomial59 K y).natDegree :=
        natDegree_mul_le
      _ = (twistedLambdaPowerBasisPolynomial59 K y).natDegree := by simp
  apply lt_of_le_of_lt _
    (twistedLambdaPowerBasisPolynomial59_natDegree_lt K y)
  exact (natDegree_add_le 1
    (C (twistedLambda59 K) * twistedLambdaPowerBasisPolynomial59 K y)).trans
      (max_le (by simp) hprod)

/-- One normalization raises every positive polynomial coefficient from
depth `s` to depth `s + 1`. -/
theorem normalizedResidualPolynomial59_data
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    (normalizedResidualPolynomial59 K y).coeff 0 = 1 ∧
      (normalizedResidualPolynomial59 K y).natDegree < 59 ∧
      ∀ j : ℕ, 0 < j →
        Valued.v ((normalizedResidualPolynomial59 K y).coeff j) ≤
          WithZero.exp (-((s + 1 : ℕ) : ℤ)) := by
  have hu0ne := residualConstant59_ne_zero K y s hy
  constructor
  · exact normalizeConstant_coeff_zero (residualPolynomial59 K y) hu0ne
  constructor
  · apply lt_of_le_of_lt _ (residualPolynomial59_natDegree_lt K y)
    rw [normalizedResidualPolynomial59, normalizeConstant]
    exact natDegree_mul_le.trans (by simp)
  · intro j hj
    have huCoeff :
        (residualPolynomial59 K y).coeff j =
          twistedLambda59 K *
            (twistedLambdaPowerBasisPolynomial59 K y).coeff j := by
      simp [residualPolynomial59, coeff_add, coeff_C_mul, coeff_one,
        Nat.ne_of_gt hj]
    rw [normalizedResidualPolynomial59, normalizeConstant, coeff_C_mul,
      huCoeff]
    change Valued.v
      ((residualConstant59 K y)⁻¹ *
        (twistedLambda59 K *
          (twistedLambdaPowerBasisPolynomial59 K y).coeff j)) ≤ _
    rw [map_mul, map_inv₀, residualConstant59_valuation K y s hy,
      inv_one, one_mul]
    exact twisted_coefficient_depth K y s j hy

/-- Evaluation commutes with removing the residual constant. -/
theorem residualElement59_eq_constant_mul_normalized
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    residualElement59 K y =
      algebraMap (F59 K) (E59 K) (residualConstant59 K y) *
        aeval (twistedLambdaRoot59 K) (normalizedResidualPolynomial59 K y) := by
  have hpoly := C_coeff_zero_mul_normalizeConstant
    (residualPolynomial59 K y) (residualConstant59_ne_zero K y s hy)
  calc
    residualElement59 K y =
        aeval (twistedLambdaRoot59 K) (residualPolynomial59 K y) :=
      (aeval_residualPolynomial59 K y).symm
    _ = aeval (twistedLambdaRoot59 K)
        (C ((residualPolynomial59 K y).coeff 0) *
          normalizeConstant (residualPolynomial59 K y)) := by
      exact congrArg
        (fun f : (F59 K)[X] ↦ aeval (twistedLambdaRoot59 K) f) hpoly.symm
    _ = algebraMap (F59 K) (E59 K) (residualConstant59 K y) *
        aeval (twistedLambdaRoot59 K)
          (normalizedResidualPolynomial59 K y) := by
      simp [residualConstant59, normalizedResidualPolynomial59]

end Fermat.FiftyNine.Conservation.TriangularResidualNormalization59
