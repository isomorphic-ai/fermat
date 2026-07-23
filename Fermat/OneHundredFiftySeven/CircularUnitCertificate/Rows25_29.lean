import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows20_24

/-!
# Rows 25--29 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 25 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_25 (j : Fin 77) :
    (matrix * matrixInverse) (25 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 25 j := by
  decide +revert

/-- Row 26 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_26 (j : Fin 77) :
    (matrix * matrixInverse) (26 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 26 j := by
  decide +revert

/-- Row 27 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_27 (j : Fin 77) :
    (matrix * matrixInverse) (27 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 27 j := by
  decide +revert

/-- Row 28 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_28 (j : Fin 77) :
    (matrix * matrixInverse) (28 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 28 j := by
  decide +revert

/-- Row 29 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_29 (j : Fin 77) :
    (matrix * matrixInverse) (29 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 29 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
