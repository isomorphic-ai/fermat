import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows10_14

/-!
# Rows 15--19 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 15 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_15 (j : Fin 77) :
    (matrix * matrixInverse) (15 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 15 j := by
  decide +revert

/-- Row 16 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_16 (j : Fin 77) :
    (matrix * matrixInverse) (16 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 16 j := by
  decide +revert

/-- Row 17 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_17 (j : Fin 77) :
    (matrix * matrixInverse) (17 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 17 j := by
  decide +revert

/-- Row 18 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_18 (j : Fin 77) :
    (matrix * matrixInverse) (18 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 18 j := by
  decide +revert

/-- Row 19 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_19 (j : Fin 77) :
    (matrix * matrixInverse) (19 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 19 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
