import Fermat.OneHundredFiftySeven.CircularUnitMatrix

/-!
# Rows 60--76 of the exponent-157 circular-unit inverse

This shard keeps each kernel reduction small while checking the uploaded
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

/-- Row 75 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_75 (j : Fin 77) :
    (matrix * matrixInverse) (75 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 75 j := by
  decide +revert

/-- Row 76 of the inverse-product certificate. -/
theorem matrix_mul_inverse_row_76 (j : Fin 77) :
    (matrix * matrixInverse) (76 : Fin 77) j =
      (1 : Matrix (Fin 77) (Fin 77) (ZMod 157)) 76 j := by
  decide +revert

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
