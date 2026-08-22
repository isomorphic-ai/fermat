/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Terminal norm bound for the triangular residual at 59

Coordinate depth controls the spectral norm of a residual parameter.  After
multiplication by the twisted Kummer radicand, the residual one-unit gains
one more lambda-depth.  The generic spectral product estimate then shows
that its actual field norm has the same depth.  In particular, coordinate
depth at least 59 makes the residual norm invisible modulo `U_60`.
-/
import Fermat.Exponents.FiftyNine.Conservation.TriangularResidualStep59
import Fermat.Experiments.Conservation.SpectralNormProductRemainder
import Mathlib.Tactic

open scoped NumberField WithZero

noncomputable section

namespace Fermat.FiftyNine.Conservation.TriangularTerminalResidual59

open Fermat.Conservation.SpectralNormProductRemainder
open Fermat.Conservation.KummerCyclicQuotient59
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

local instance : Polynomial.IsSplittingField (F59 K) (E59 K)
    (kummerPolynomial59 (F59 K) (twistedLambda59 K)) :=
  kummerExtension59_isSplittingField (F59 K) (twistedLambda59 K)

local instance : IsGalois (F59 K) (E59 K) :=
  isGalois_of_isSplittingField_X_pow_sub_C
    ⟨lambdaLocalPrimitiveRoot59 K,
      (mem_primitiveRoots (by norm_num : 0 < 59)).2
        (lambdaLocalPrimitiveRoot59_isPrimitive K)⟩
    (twistedLambdaPolynomial59_irreducible K) (E59 K)

theorem depthRadius59_add (m n : ℕ) :
    depthRadius59 K m * depthRadius59 K n = depthRadius59 K (m + n) := by
  simp only [depthRadius59, ← norm_mul, ← pow_add]

theorem norm_twistedLambda59_eq_depthRadius_one :
    ‖twistedLambda59 K‖ = depthRadius59 K 1 := by
  apply le_antisymm
  · rw [depthRadius59, Valued.toNormedField.norm_le_iff,
      twistedLambda59_valuation, canonicalLambda59_pow_valuation]
    norm_num
  · rw [depthRadius59, Valued.toNormedField.norm_le_iff,
      twistedLambda59_valuation, canonicalLambda59_pow_valuation]
    norm_num

/-- Integer coordinate depth bounds the spectral norm of the represented
extension element. -/
theorem spectralNorm_le_depthRadius59_of_coordinateDepth
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    spectralNorm (F59 K) (E59 K) y ≤ depthRadius59 K s := by
  by_cases hy0 : y = 0
  · subst y
    rw [spectralNorm_zero]
    exact depthRadius59_nonneg K s
  obtain ⟨i, hi0, hiEq, hiBound⟩ :=
    exists_dominant_twistedLambdaPowerBasis_coefficient K y hy0
  rw [hiEq]
  have hcoeff :
      ‖(twistedLambdaPowerBasis59 K).basis.repr y i‖ ≤
        depthRadius59 K s :=
    (valuation_le_exp_neg_iff_norm_le_depthRadius59 K _ s).mp (hy i)
  have hroot :
      spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ (i : ℕ) ≤ 1 :=
    pow_le_one₀ (spectralNorm_nonneg _)
      (le_of_lt (spectralNorm_twistedLambdaRoot59_lt_one K))
  calc
    ‖(twistedLambdaPowerBasis59 K).basis.repr y i‖ *
          spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ (i : ℕ) ≤
        depthRadius59 K s * 1 :=
      mul_le_mul hcoeff hroot
        (pow_nonneg (spectralNorm_nonneg _) _)
        (depthRadius59_nonneg K s)
    _ = depthRadius59 K s := mul_one _

theorem spectralNorm_twistedLambda_mul_le_depthRadius_succ
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    spectralNorm (F59 K) (E59 K)
        (algebraMap (F59 K) (E59 K) (twistedLambda59 K) * y) ≤
      depthRadius59 K (s + 1) := by
  rw [← spectralMulAlgNorm_def, map_mul, spectralMulAlgNorm_def,
    spectralMulAlgNorm_def, spectralNorm_extends,
    norm_twistedLambda59_eq_depthRadius_one]
  calc
    depthRadius59 K 1 * spectralNorm (F59 K) (E59 K) y ≤
        depthRadius59 K 1 * depthRadius59 K s :=
      mul_le_mul_of_nonneg_left
        (spectralNorm_le_depthRadius59_of_coordinateDepth K y s hy)
        (depthRadius59_nonneg K 1)
    _ = depthRadius59 K (s + 1) := by
      rw [depthRadius59_add]
      congr 1
      omega

/-- The norm of a residual one-unit preserves its gained lambda-depth. -/
theorem norm_residualElement59_sub_one_valuation_le
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s) :
    Valued.v
        (Algebra.norm (F59 K) (residualElement59 K y) - 1) ≤
      WithZero.exp (-((s + 1 : ℕ) : ℤ)) := by
  let t : E59 K := algebraMap (F59 K) (E59 K) (twistedLambda59 K) * y
  have ht : spectralNorm (F59 K) (E59 K) t ≤ depthRadius59 K (s + 1) :=
    spectralNorm_twistedLambda_mul_le_depthRadius_succ K y s hy
  have ht1 : spectralNorm (F59 K) (E59 K) t ≤ 1 :=
    ht.trans (depthRadius59_le_one K (s + 1))
  have hnorm := norm_one_add_sub_one_norm_le t ht1
  have hnormRadius :
      ‖Algebra.norm (F59 K) (residualElement59 K y) - 1‖ ≤
        depthRadius59 K (s + 1) := by
    change ‖Algebra.norm (F59 K) (1 + t) - 1‖ ≤ _
    exact hnorm.trans ht
  have hval := Valued.toNormedField.norm_le_iff.mp hnormRadius
  rw [canonicalLambda59_pow_valuation] at hval
  exact hval

/-- A terminal residual with coordinate depth at least 59 has norm in
`U_60`. -/
theorem norm_residualElement59_mem_U60_of_depth
    (y : E59 K) (s : ℕ) (hy : HasCoordinateDepth59 K y s)
    (hs : 60 ≤ s + 1) :
    Valued.v
        (Algebra.norm (F59 K) (residualElement59 K y) - 1) ≤
      WithZero.exp (-60 : ℤ) := by
  exact (norm_residualElement59_sub_one_valuation_le K y s hy).trans (by
    rw [WithZero.exp_le_exp]
    omega)

end Fermat.FiftyNine.Conservation.TriangularTerminalResidual59
