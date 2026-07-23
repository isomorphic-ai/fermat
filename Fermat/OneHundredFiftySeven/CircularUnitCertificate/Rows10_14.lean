import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows05_09

/-!
# Rows 10--14 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 10 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_10 (j : Fin 77) :
    (matrix * matrixInverse) (10 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 10 j := by
  decide +revert

/-- Row 11 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_11 (j : Fin 77) :
    (matrix * matrixInverse) (11 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 11 j := by
  decide +revert

/-- Row 12 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_12 (j : Fin 77) :
    (matrix * matrixInverse) (12 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 12 j := by
  decide +revert

/-- Row 13 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_13 (j : Fin 77) :
    (matrix * matrixInverse) (13 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 13 j := by
  decide +revert

/-- Row 14 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_14 (j : Fin 77) :
    (matrix * matrixInverse) (14 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 14 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
