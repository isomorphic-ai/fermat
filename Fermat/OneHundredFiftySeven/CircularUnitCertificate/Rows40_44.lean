import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows20_39

/-!
# Rows 40--44 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 40 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_40 (j : Fin 77) :
    (matrix * matrixInverse) (40 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 40 j := by
  decide +revert

/-- Row 41 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_41 (j : Fin 77) :
    (matrix * matrixInverse) (41 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 41 j := by
  decide +revert

/-- Row 42 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_42 (j : Fin 77) :
    (matrix * matrixInverse) (42 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 42 j := by
  decide +revert

/-- Row 43 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_43 (j : Fin 77) :
    (matrix * matrixInverse) (43 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 43 j := by
  decide +revert

/-- Row 44 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_44 (j : Fin 77) :
    (matrix * matrixInverse) (44 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 44 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
