import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows65_69

/-!
# Rows 70--74 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 70 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_70 (j : Fin 77) :
    (matrix * matrixInverse) (70 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 70 j := by
  decide +revert

/-- Row 71 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_71 (j : Fin 77) :
    (matrix * matrixInverse) (71 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 71 j := by
  decide +revert

/-- Row 72 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_72 (j : Fin 77) :
    (matrix * matrixInverse) (72 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 72 j := by
  decide +revert

/-- Row 73 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_73 (j : Fin 77) :
    (matrix * matrixInverse) (73 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 73 j := by
  decide +revert

/-- Row 74 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_74 (j : Fin 77) :
    (matrix * matrixInverse) (74 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 74 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
