import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows00_04

/-!
# Rows 5--9 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 5 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_5 (j : Fin 77) :
    (matrix * matrixInverse) (5 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 5 j := by
  decide +revert

/-- Row 6 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_6 (j : Fin 77) :
    (matrix * matrixInverse) (6 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 6 j := by
  decide +revert

/-- Row 7 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_7 (j : Fin 77) :
    (matrix * matrixInverse) (7 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 7 j := by
  decide +revert

/-- Row 8 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_8 (j : Fin 77) :
    (matrix * matrixInverse) (8 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 8 j := by
  decide +revert

/-- Row 9 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_9 (j : Fin 77) :
    (matrix * matrixInverse) (9 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 9 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
