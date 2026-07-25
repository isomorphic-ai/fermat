import Fermat.Irregular.CyclicDifferenceMatrixNonsingular
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelation

/-!
# Compressed circular-unit determinant at exponent 1831

The 915 cyclic correlations give an inverse for the reduced difference
matrix. The recorded row and column permutations then transfer
nonsingularity to the package's original `914 × 914` matrix. An
independent modular elimination audit gives determinant `1003 mod 1831`;
the inverse certificate below records the smaller kernel-checkable fact
needed downstream, namely that this determinant is nonzero.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

local instance : Fact (1 < 1831) := ⟨by omega⟩

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

/-- The uploaded circular-unit matrix is nonsingular modulo `1831`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_reindex rowPermutation columnPermutation matrix
  rw [matrix_reindexed, hzero, mul_zero] at hdet
  exact differenceMatrix_det_ne_zero hdet

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
