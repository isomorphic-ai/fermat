import Fermat.OneHundredFiftySeven.CircularUnitMatrix

/-!
# Rows 0--19 of the exponent-157 circular-unit inverse

This shard keeps each kernel reduction small while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Row 0 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_0 (j : Fin 77) :
    (matrix * matrixInverse) (0 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 0 j := by
  decide +revert

/-- Row 1 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_1 (j : Fin 77) :
    (matrix * matrixInverse) (1 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 1 j := by
  decide +revert

/-- Row 2 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_2 (j : Fin 77) :
    (matrix * matrixInverse) (2 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 2 j := by
  decide +revert

/-- Row 3 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_3 (j : Fin 77) :
    (matrix * matrixInverse) (3 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 3 j := by
  decide +revert

/-- Row 4 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_4 (j : Fin 77) :
    (matrix * matrixInverse) (4 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 4 j := by
  decide +revert

/-- Row 5 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_5 (j : Fin 77) :
    (matrix * matrixInverse) (5 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 5 j := by
  decide +revert

/-- Row 6 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_6 (j : Fin 77) :
    (matrix * matrixInverse) (6 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 6 j := by
  decide +revert

/-- Row 7 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_7 (j : Fin 77) :
    (matrix * matrixInverse) (7 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 7 j := by
  decide +revert

/-- Row 8 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_8 (j : Fin 77) :
    (matrix * matrixInverse) (8 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 8 j := by
  decide +revert

/-- Row 9 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_9 (j : Fin 77) :
    (matrix * matrixInverse) (9 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 9 j := by
  decide +revert

/-- Row 10 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_10 (j : Fin 77) :
    (matrix * matrixInverse) (10 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 10 j := by
  decide +revert

/-- Row 11 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_11 (j : Fin 77) :
    (matrix * matrixInverse) (11 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 11 j := by
  decide +revert

/-- Row 12 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_12 (j : Fin 77) :
    (matrix * matrixInverse) (12 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 12 j := by
  decide +revert

/-- Row 13 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_13 (j : Fin 77) :
    (matrix * matrixInverse) (13 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 13 j := by
  decide +revert

/-- Row 14 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_14 (j : Fin 77) :
    (matrix * matrixInverse) (14 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 14 j := by
  decide +revert

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
