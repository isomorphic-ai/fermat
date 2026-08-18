/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Spectral bounds for polynomial evaluation

Evaluating a polynomial at an element of spectral norm at most one does not
increase its coefficient supremum norm.  This is the bridge from the exact
coefficient contraction in triangular Kummer factorization to a contraction
inside the Kummer extension.
-/
import Fermat.Conservation.SpectralNormProductRemainder
import Mathlib.Analysis.Polynomial.Norm

open Polynomial

noncomputable section

namespace Fermat.Conservation.PolynomialSpectralNormBound

variable {F E : Type*}
variable [NontriviallyNormedField F] [Field E] [Algebra F E]
variable [Algebra.IsAlgebraic F E] [IsUltrametricDist F] [CompleteSpace F]

/-- Evaluating at a spectral one-unit does not increase the coefficient
supremum norm. -/
theorem spectralNorm_aeval_le_supNorm
    (alpha : E) (halpha : spectralNorm F E alpha ≤ 1) (f : F[X]) :
    spectralNorm F E (aeval alpha f) ≤ f.supNorm := by
  rw [aeval_def, eval₂_eq_sum_range]
  let s := Finset.range (f.natDegree + 1)
  have hs : s.Nonempty := by
    exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  have hsum := IsNonarchimedean.apply_sum_le_sup
    (isNonarchimedean_spectralNorm (K := F) (L := E)) hs
    (l := fun i : ℕ => algebraMap F E (f.coeff i) * alpha ^ i)
  apply hsum.trans
  apply Finset.sup'_le hs
  intro i hi
  rw [← spectralMulAlgNorm_def, map_mul, map_pow,
    spectralMulAlgNorm_def, spectralMulAlgNorm_def,
    spectralNorm_extends]
  calc
    ‖f.coeff i‖ * spectralNorm F E alpha ^ i ≤
        ‖f.coeff i‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_one₀ (spectralNorm_nonneg alpha) halpha)
        (norm_nonneg _)
    _ = ‖f.coeff i‖ := mul_one _
    _ ≤ f.supNorm := f.le_supNorm i

end Fermat.Conservation.PolynomialSpectralNormBound
