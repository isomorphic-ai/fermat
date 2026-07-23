import Fermat.OneHundredFiftySeven.CircularUnitMatrix

/-!
# Rows 0--4 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 0 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_0 (j : Fin 77) :
    (matrix * matrixInverse) (0 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 0 j := by
  decide +revert

/-- Row 1 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_1 (j : Fin 77) :
    (matrix * matrixInverse) (1 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 1 j := by
  decide +revert

/-- Row 2 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_2 (j : Fin 77) :
    (matrix * matrixInverse) (2 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 2 j := by
  decide +revert

/-- Row 3 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_3 (j : Fin 77) :
    (matrix * matrixInverse) (3 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 3 j := by
  decide +revert

/-- Row 4 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_4 (j : Fin 77) :
    (matrix * matrixInverse) (4 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 4 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
