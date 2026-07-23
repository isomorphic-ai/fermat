import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows45_49

/-!
# Rows 50--54 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 50 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_50 (j : Fin 77) :
    (matrix * matrixInverse) (50 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 50 j := by
  decide +revert

/-- Row 51 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_51 (j : Fin 77) :
    (matrix * matrixInverse) (51 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 51 j := by
  decide +revert

/-- Row 52 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_52 (j : Fin 77) :
    (matrix * matrixInverse) (52 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 52 j := by
  decide +revert

/-- Row 53 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_53 (j : Fin 77) :
    (matrix * matrixInverse) (53 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 53 j := by
  decide +revert

/-- Row 54 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_54 (j : Fin 77) :
    (matrix * matrixInverse) (54 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 54 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
