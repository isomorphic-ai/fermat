import Fermat.Irregular.CircularUnitIndex
import Fermat.FiveHundredEightySeven.CircularUnitCorrelation

/-!
# The compressed exponent-587 circular-unit certificate

Instead of checking a dense `292 × 292` inverse, this module checks the
`293` cyclic correlations of two phase vectors.  The generic cyclic theorem
then supplies an inverse for the reduced difference matrix.  Finally the
recorded row and column permutations transfer nonsingularity back to the
package's original ordering.
-/

namespace Fermat.FiveHundredEightySeven.CircularUnitCertificate

noncomputable section

open Fermat.FiveHundredEightySeven.CircularUnitCyclic
open Fermat.FiveHundredEightySeven.CircularUnitMatrix

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
  exact (by decide : (0 : ZMod 587) ≠ 1) hdet

/-- Reindexing the original package ordering recovers the reduced cyclic
difference matrix exactly. -/
theorem matrix_reindexed :
    Matrix.reindex rowPermutation columnPermutation matrix =
      differenceMatrix symbolPhase := by
  ext i j
  simp [matrix, Matrix.reindex_apply]

/-- The package matrix is nonsingular over `ZMod 587`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_reindex rowPermutation columnPermutation matrix
  rw [matrix_reindexed, hzero, mul_zero] at hdet
  exact differenceMatrix_det_ne_zero hdet

end

end Fermat.FiveHundredEightySeven.CircularUnitCertificate
