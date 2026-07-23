import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows40_44

/-!
# Rows 45--49 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 45 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_45 (j : Fin 77) :
    (matrix * matrixInverse) (45 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 45 j := by
  decide +revert

/-- Row 46 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_46 (j : Fin 77) :
    (matrix * matrixInverse) (46 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 46 j := by
  decide +revert

/-- Row 47 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_47 (j : Fin 77) :
    (matrix * matrixInverse) (47 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 47 j := by
  decide +revert

/-- Row 48 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_48 (j : Fin 77) :
    (matrix * matrixInverse) (48 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 48 j := by
  decide +revert

/-- Row 49 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_49 (j : Fin 77) :
    (matrix * matrixInverse) (49 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 49 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
