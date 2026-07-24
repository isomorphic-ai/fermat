import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows30_34

/-!
# Rows 35--39 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 35 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_35 (j : Fin 77) :
    (matrix * matrixInverse) (35 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 35 j := by
  decide +revert

/-- Row 36 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_36 (j : Fin 77) :
    (matrix * matrixInverse) (36 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 36 j := by
  decide +revert

/-- Row 37 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_37 (j : Fin 77) :
    (matrix * matrixInverse) (37 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 37 j := by
  decide +revert

/-- Row 38 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_38 (j : Fin 77) :
    (matrix * matrixInverse) (38 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 38 j := by
  decide +revert

/-- Row 39 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_39 (j : Fin 77) :
    (matrix * matrixInverse) (39 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 39 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
