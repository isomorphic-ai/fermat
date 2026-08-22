import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitFourierFactors

/-!
# Factored circular-unit determinant at exponent 1831

This is an independent replacement path for the cyclic-correlation
certificate.  The generic Fourier determinant theorem reduces
nonsingularity to the `914` nontrivial coefficients checked in
`CircularUnitFourierFactors`; the package row and column permutations then
transfer the result to the uploaded `914 × 914` matrix.

The correlation certificate remains available in parallel while downstream
consumers are migrated and both routes are compared.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificateFactored

noncomputable section

open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitFourierFactors
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩

/-- The reduced cyclic difference matrix is nonsingular by its Fourier
factorization, without using the cyclic-correlation inverse. -/
theorem differenceMatrix_det_ne_zero :
    (differenceMatrix symbolPhase).det ≠ 0 :=
  (differenceMatrix_det_ne_zero_iff_fourierCoeff
    (9 : ZMod 1831) fourierRoot_isPrimitive symbolPhase).2 fhat_ne_zero

/-- Reindexing the package ordering recovers the reduced cyclic matrix. -/
theorem matrix_reindexed :
    Matrix.reindex rowPermutation columnPermutation matrix =
      differenceMatrix symbolPhase := by
  ext i j
  simp [matrix, Matrix.reindex_apply]

/-- The uploaded circular-unit matrix is nonsingular modulo `1831`, proved
through the factored Fourier route. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_reindex rowPermutation columnPermutation matrix
  rw [matrix_reindexed, hzero, mul_zero] at hdet
  exact differenceMatrix_det_ne_zero hdet

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificateFactored
