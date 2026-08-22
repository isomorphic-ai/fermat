import Fermat.Descent.Irregular.CyclicDifferenceMatrixNonsingular
import Fermat.Exponents.SixHundredSeven.CircularUnitCorrelation

/-!
# Compressed circular-unit determinant at exponent 607

The 303 cyclic correlations give an inverse for the reduced difference
matrix. The recorded row and column permutations then transfer
nonsingularity to the package ordering. The package Fourier audit gives
nontrivial-mode product `272 mod 607`; the inverse certificate below records
the kernel-checkable fact needed downstream, namely determinant
nonvanishing.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

local instance : Fact (1 < 607) := ⟨by omega⟩

/-- The reduced difference matrices are mutual inverses. -/
theorem differenceMatrix_mul_inverse :
    differenceMatrix symbolPhase * differenceMatrix correlationInverse = 1 :=
  differenceMatrix_mul_eq_one symbolPhase correlationInverse phase_correlation

/-- The reduced cyclic difference matrix is nonsingular. -/
theorem differenceMatrix_det_ne_zero :
    (differenceMatrix symbolPhase).det ≠ 0 :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix_det_ne_zero
    symbolPhase correlationInverse phase_correlation

/-- Reindexing the package ordering recovers the reduced cyclic matrix. -/
theorem matrix_reindexed :
    Matrix.reindex rowPermutation columnPermutation matrix =
      differenceMatrix symbolPhase := by
  ext i j
  simp [matrix, Matrix.reindex_apply]

/-- The exponent-607 circular-unit matrix is nonsingular modulo `607`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_reindex rowPermutation columnPermutation matrix
  rw [matrix_reindexed, hzero, mul_zero] at hdet
  exact differenceMatrix_det_ne_zero hdet

end

end Fermat.SixHundredSeven.CircularUnitCertificate
