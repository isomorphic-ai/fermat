import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows60_64

/-!
# Rows 65--69 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 65 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_65 (j : Fin 77) :
    (matrix * matrixInverse) (65 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 65 j := by
  decide +revert

/-- Row 66 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_66 (j : Fin 77) :
    (matrix * matrixInverse) (66 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 66 j := by
  decide +revert

/-- Row 67 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_67 (j : Fin 77) :
    (matrix * matrixInverse) (67 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 67 j := by
  decide +revert

/-- Row 68 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_68 (j : Fin 77) :
    (matrix * matrixInverse) (68 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 68 j := by
  decide +revert

/-- Row 69 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_69 (j : Fin 77) :
    (matrix * matrixInverse) (69 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 69 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
