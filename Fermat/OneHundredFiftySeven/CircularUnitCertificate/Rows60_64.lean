import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows40_59

/-!
# Rows 60--64 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 60 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_60 (j : Fin 77) :
    (matrix * matrixInverse) (60 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 60 j := by
  decide +revert

/-- Row 61 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_61 (j : Fin 77) :
    (matrix * matrixInverse) (61 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 61 j := by
  decide +revert

/-- Row 62 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_62 (j : Fin 77) :
    (matrix * matrixInverse) (62 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 62 j := by
  decide +revert

/-- Row 63 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_63 (j : Fin 77) :
    (matrix * matrixInverse) (63 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 63 j := by
  decide +revert

/-- Row 64 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_64 (j : Fin 77) :
    (matrix * matrixInverse) (64 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 64 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
