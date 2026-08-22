import Fermat.Descent.Irregular.CyclicDifferenceMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Nonsingularity of reduced cyclic difference matrices

This companion to `Fermat.Irregular.CyclicDifferenceMatrix` keeps
determinant machinery out of the large finite cyclic-correlation
certificates. Import it when a nonzero-determinant conclusion is needed.
-/

namespace Fermat.Irregular.CyclicDifferenceMatrix

open scoped BigOperators Matrix

/-- A delta cyclic correlation makes the reduced difference matrix
nonsingular. -/
theorem differenceMatrix_det_ne_zero
    {n : ℕ} [NeZero (n + 1)] {R : Type*}
    [CommRing R] [Nontrivial R]
    (f g : Cyc n → R)
    (hcorr : ∀ d : Cyc n,
      (∑ u : Cyc n, f u * g (u + d)) = if d = 0 then 1 else 0) :
    (differenceMatrix n f).det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det
    (differenceMatrix_mul_eq_one f g hcorr)
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

end Fermat.Irregular.CyclicDifferenceMatrix
