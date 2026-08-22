import Fermat.Descent.Irregular.CircularUnitIndex
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelation

/-!
# Compressed circular-unit determinant at exponent 691

The 345 cyclic correlations give an inverse for the reduced difference
matrix. The recorded row and column permutations then transfer
nonsingularity to the package's original `344 × 344` matrix. An
independent modular elimination audit gives determinant `36 mod 691`;
the inverse certificate below records the smaller kernel-checkable fact
needed downstream, namely that this determinant is nonzero.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

/-- The reduced difference matrices are mutual inverses. -/
theorem differenceMatrix_mul_inverse :
    differenceMatrix symbolPhase * differenceMatrix correlationInverse = 1 :=
  differenceMatrix_mul_eq_one symbolPhase correlationInverse phase_correlation

/-- The reduced cyclic difference matrix is nonsingular. -/
theorem differenceMatrix_det_ne_zero :
    (differenceMatrix symbolPhase).det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det differenceMatrix_mul_inverse
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact (by decide : (0 : ZMod 691) ≠ 1) hdet

/-- Reindexing the package ordering recovers the reduced cyclic matrix. -/
theorem matrix_reindexed :
    Matrix.reindex rowPermutation columnPermutation matrix =
      differenceMatrix symbolPhase := by
  ext i j
  simp [matrix, Matrix.reindex_apply]

/-- The uploaded circular-unit matrix is nonsingular modulo `691`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_reindex rowPermutation columnPermutation matrix
  rw [matrix_reindexed, hzero, mul_zero] at hdet
  exact differenceMatrix_det_ne_zero hdet

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
