import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows50_54

/-!
# Rows 55--59 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 55 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_55 (j : Fin 77) :
    (matrix * matrixInverse) (55 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 55 j := by
  decide +revert

/-- Row 56 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_56 (j : Fin 77) :
    (matrix * matrixInverse) (56 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 56 j := by
  decide +revert

/-- Row 57 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_57 (j : Fin 77) :
    (matrix * matrixInverse) (57 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 57 j := by
  decide +revert

/-- Row 58 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_58 (j : Fin 77) :
    (matrix * matrixInverse) (58 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 58 j := by
  decide +revert

/-- Row 59 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_59 (j : Fin 77) :
    (matrix * matrixInverse) (59 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 59 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
