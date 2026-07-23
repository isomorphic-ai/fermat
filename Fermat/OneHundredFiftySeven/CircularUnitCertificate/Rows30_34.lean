import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows25_29

/-!
# Rows 30--34 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 30 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_30 (j : Fin 77) :
    (matrix * matrixInverse) (30 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 30 j := by
  decide +revert

/-- Row 31 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_31 (j : Fin 77) :
    (matrix * matrixInverse) (31 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 31 j := by
  decide +revert

/-- Row 32 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_32 (j : Fin 77) :
    (matrix * matrixInverse) (32 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 32 j := by
  decide +revert

/-- Row 33 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_33 (j : Fin 77) :
    (matrix * matrixInverse) (33 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 33 j := by
  decide +revert

/-- Row 34 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_34 (j : Fin 77) :
    (matrix * matrixInverse) (34 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 34 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
