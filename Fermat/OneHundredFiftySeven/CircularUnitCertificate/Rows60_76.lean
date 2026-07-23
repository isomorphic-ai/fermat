import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows70_74

/-!
# Rows 75--76 of the exponent-157 circular-unit inverse

This shard keeps the kernel reduction bounded while checking the uploaded
matrix against its independently reconstructed inverse.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

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
