import Fermat.Descent.Irregular.CyclicDifferenceMatrixNonsingular
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelation

/-!
# Compressed circular-unit determinant at exponent 1381

The 690 cyclic correlations give an inverse for the reduced difference
matrix. The recorded row and column permutations then transfer
nonsingularity to the package's original `689 × 689` matrix. An
independent modular elimination audit gives determinant `639 mod 1381`;
the inverse certificate below records the smaller kernel-checkable fact
needed downstream, namely that this determinant is nonzero.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

local instance : Fact (1 < 1381) := ⟨by omega⟩

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

/-- The uploaded circular-unit matrix is nonsingular modulo `1381`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_reindex rowPermutation columnPermutation matrix
  rw [matrix_reindexed, hzero, mul_zero] at hdet
  exact differenceMatrix_det_ne_zero hdet

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
