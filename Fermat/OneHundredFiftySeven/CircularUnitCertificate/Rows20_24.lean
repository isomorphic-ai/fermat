import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows00_19

/-!
# Rows 20--24 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 20 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_20 (j : Fin 77) :
    (matrix * matrixInverse) (20 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 20 j := by
  decide +revert

/-- Row 21 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_21 (j : Fin 77) :
    (matrix * matrixInverse) (21 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 21 j := by
  decide +revert

/-- Row 22 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_22 (j : Fin 77) :
    (matrix * matrixInverse) (22 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 22 j := by
  decide +revert

/-- Row 23 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_23 (j : Fin 77) :
    (matrix * matrixInverse) (23 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 23 j := by
  decide +revert

/-- Row 24 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_24 (j : Fin 77) :
    (matrix * matrixInverse) (24 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 24 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
