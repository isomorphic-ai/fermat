/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Spectral contraction recovers integral lambda depth at 59

The generic triangular factorization contracts its evaluated remainder by
`q²` in spectral norm.  In the Eisenstein selected-root basis at 59, an
integer lambda-depth bound on spectral norm forces the same depth on every
base-field coordinate: the fractional root weight `i / 59`, for `i < 59`,
cannot consume one complete base valuation step.

Consequently one evaluated triangular round doubles the integer depth of
every coordinate of its remainder.  This is the local adapter needed by the
finite depth-amplification argument; the generic factorization and spectral
contraction remain prime-parametric.
-/
import Fermat.Experiments.Conservation.PrimeTriangularSpectralContraction
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaEisensteinIntegrality59
import Mathlib.Tactic

open scoped NumberField WithZero
open Polynomial

noncomputable section

namespace Fermat.FiftyNine.Conservation.TriangularSpectralDepth59

open Fermat.Conservation.PrimeTriangularUnitFactorization
open Fermat.Conservation.PrimeTriangularSpectralContraction
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.EisensteinIntegrality59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

theorem canonicalLambda59_ne_zero : canonicalLambda59 K ≠ 0 := by
  apply (Valuation.ne_zero_iff (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰)).mp
  rw [canonicalLambda59_valuation]
  exact WithZero.exp_ne_zero

@[reducible] noncomputable def lambdaField59NontriviallyNormedField :
    NontriviallyNormedField (LambdaField59 K) :=
  ⟨⟨(canonicalLambda59 K)⁻¹, by
    rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀,
      canonicalLambda59_valuation]
    rw [show (WithZero.exp (-1 : ℤ))⁻¹ = WithZero.exp (1 : ℤ) by norm_num]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num⟩⟩

local instance : NontriviallyNormedField (LambdaField59 K) :=
  lambdaField59NontriviallyNormedField K

/-- The real norm radius corresponding to lambda-depth `s`. -/
def depthRadius59 (s : ℕ) : ℝ :=
  ‖canonicalLambda59 K ^ s‖

@[simp]
theorem depthRadius59_zero : depthRadius59 K 0 = 1 := by
  simp [depthRadius59]

theorem depthRadius59_nonneg (s : ℕ) : 0 ≤ depthRadius59 K s := by
  exact norm_nonneg _

theorem depthRadius59_pos (s : ℕ) : 0 < depthRadius59 K s := by
  exact norm_pos_iff.mpr (pow_ne_zero s (canonicalLambda59_ne_zero K))

theorem depthRadius59_le_one (s : ℕ) : depthRadius59 K s ≤ 1 := by
  rw [depthRadius59, Valued.toNormedField.norm_le_one_iff, map_pow,
    canonicalLambda59_valuation]
  rw [← WithZero.exp_nsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp only [nsmul_eq_mul]
  omega

theorem canonicalLambda59_pow_valuation (s : ℕ) :
    Valued.v (canonicalLambda59 K ^ s) = WithZero.exp (-(s : ℤ)) := by
  rw [map_pow, canonicalLambda59_valuation, ← WithZero.exp_nsmul]
  congr 1
  simp only [nsmul_eq_mul]
  omega

/-- Valuation depth and the induced real norm radius are equivalent. -/
theorem valuation_le_exp_neg_iff_norm_le_depthRadius59
    (x : LambdaField59 K) (s : ℕ) :
    Valued.v x ≤ WithZero.exp (-(s : ℤ)) ↔
      ‖x‖ ≤ depthRadius59 K s := by
  rw [depthRadius59, Valued.toNormedField.norm_le_iff,
    canonicalLambda59_pow_valuation]

theorem depthRadius59_sq (s : ℕ) :
    depthRadius59 K s ^ 2 = depthRadius59 K (2 * s) := by
  simp only [depthRadius59, ← norm_pow]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- A weighted selected-root monomial estimate recovers an integer
base-field depth.  The fractional root weight cannot consume one whole
base valuation step because `i < 59`. -/
theorem coefficient_valuation_le_exp_neg_of_weighted_norm_le_depthRadius59
    (b : LambdaField59 K) {i : ℕ} (hi : i < 59) (s : ℕ)
    (hweight : spectralNorm (F59 K) (E59 K)
        (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) ≤
      depthRadius59 K s) :
    Valued.v b ≤ WithZero.exp (-(s : ℤ)) := by
  let lambdaPow : LambdaField59 K := canonicalLambda59 K ^ s
  have hlambdaPow0 : lambdaPow ≠ 0 :=
    pow_ne_zero s (canonicalLambda59_ne_zero K)
  have hscaled : spectralNorm (F59 K) (E59 K)
      (algebraMap (F59 K) (E59 K) (b / lambdaPow) *
        twistedLambdaRoot59 K ^ i) ≤ 1 := by
    rw [spectralNorm_algebraMap_mul_root_pow]
    rw [norm_div]
    rw [div_mul_eq_mul_div]
    apply (div_le_one (norm_pos_iff.mpr hlambdaPow0)).mpr
    rw [spectralNorm_algebraMap_mul_root_pow] at hweight
    simpa [lambdaPow, depthRadius59, norm_pow] using hweight
  have hscaledVal : Valued.v (b / lambdaPow) ≤ 1 :=
    coefficient_valuation_le_one_of_weighted_norm_le_one K
      (b / lambdaPow) hi hscaled
  have hlambdaVal : Valued.v lambdaPow = WithZero.exp (-(s : ℤ)) := by
    change Valued.v (canonicalLambda59 K ^ s) = WithZero.exp (-(s : ℤ))
    exact canonicalLambda59_pow_valuation K s
  have hdiv : Valued.v b / Valued.v lambdaPow ≤ 1 := by
    simpa only [Valuation.map_div] using hscaledVal
  have hle : Valued.v b ≤ Valued.v lambdaPow :=
    (div_le_one₀ (hlambdaVal.symm ▸ WithZero.exp_pos)).mp hdiv
  simpa [hlambdaVal] using hle

/-- A spectral depth bound on an extension element forces the same integer
depth on every selected-root power-basis coefficient. -/
theorem twistedLambdaPowerBasis59_coeff_valuation_le_exp_neg_of_spectralNorm
    (beta : E59 K) (s : ℕ)
    (hbeta : spectralNorm (F59 K) (E59 K) beta ≤ depthRadius59 K s)
    (i : Fin (twistedLambdaPowerBasis59 K).dim) :
    Valued.v ((twistedLambdaPowerBasis59 K).basis.repr beta i) ≤
      WithZero.exp (-(s : ℤ)) := by
  by_cases hbeta0 : beta = 0
  · subst beta
    simp
  obtain ⟨k, hk, hkvalue, hbound⟩ :=
    exists_dominant_twistedLambdaPowerBasis_coefficient K beta hbeta0
  apply coefficient_valuation_le_exp_neg_of_weighted_norm_le_depthRadius59
    K ((twistedLambdaPowerBasis59 K).basis.repr beta i)
  · rw [← twistedLambdaPowerBasis59_dim K]
    exact i.isLt
  · exact (hbound i).trans hbeta

/-- At 59, the generic evaluated triangular remainder has twice the input
integer depth in every selected-root power-basis coordinate. -/
theorem exists_evaluated_triangular_remainder_with_coefficient_depth
    (f : (LambdaField59 K)[X]) (hf0 : f.coeff 0 = 1)
    (hdeg : f.natDegree < 59) (s : ℕ)
    (hf : ∀ j : ℕ, 0 < j →
      Valued.v (f.coeff j) ≤ WithZero.exp (-(s : ℤ))) :
    ∃ y : E59 K,
      aeval (twistedLambdaRoot59 K) f =
          aeval (twistedLambdaRoot59 K) (triangularProduct f 58) +
            algebraMap (F59 K) (E59 K) (twistedLambda59 K) * y ∧
      ∀ i : Fin (twistedLambdaPowerBasis59 K).dim,
        Valued.v ((twistedLambdaPowerBasis59 K).basis.repr y i) ≤
          WithZero.exp (-((2 * s : ℕ) : ℤ)) := by
  let q : ℝ := depthRadius59 K s
  have hq0 : 0 ≤ q := depthRadius59_nonneg K s
  have hq1 : q ≤ 1 := depthRadius59_le_one K s
  have hfnorm : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q := by
    intro j hj
    exact (valuation_le_exp_neg_iff_norm_le_depthRadius59 K (f.coeff j) s).mp
      (hf j hj)
  obtain ⟨y, hy, hyspectral⟩ :=
    exists_evaluated_triangular_remainder_spectralNorm_le_sq
      (F := F59 K) (E := E59 K)
      f hf0 59 (by norm_num) hdeg q hq0 hq1 hfnorm
      (twistedLambdaRoot59 K) (twistedLambda59 K)
      (twistedLambdaRoot59_pow K)
      (le_of_lt (spectralNorm_twistedLambdaRoot59_lt_one K))
  refine ⟨y, by norm_num at hy ⊢; exact hy, ?_⟩
  intro i
  apply twistedLambdaPowerBasis59_coeff_valuation_le_exp_neg_of_spectralNorm
    K y (2 * s)
  simpa [q, ← depthRadius59_sq K s] using hyspectral

end Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
