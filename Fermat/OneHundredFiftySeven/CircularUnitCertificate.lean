import Fermat.OneHundredFiftySeven.CircularUnitCertificate.Rows60_76

/-!
# The exponent-157 circular-unit inverse certificate

The uploaded `77 × 77` residue-symbol matrix at `q = 7537` is
nonsingular over `ZMod 157`.  Its inverse was reconstructed independently;
the row shards check all 5,929 entries of the product in the Lean kernel.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitCertificate

noncomputable section

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

/-- Kernel-checked inverse certificate for the uploaded matrix. -/
theorem matrix_mul_inverse : matrix * matrixInverse = 1 := by
  ext i j
  fin_cases i
  · exact matrix_mul_inverse_row_0 j
  · exact matrix_mul_inverse_row_1 j
  · exact matrix_mul_inverse_row_2 j
  · exact matrix_mul_inverse_row_3 j
  · exact matrix_mul_inverse_row_4 j
  · exact matrix_mul_inverse_row_5 j
  · exact matrix_mul_inverse_row_6 j
  · exact matrix_mul_inverse_row_7 j
  · exact matrix_mul_inverse_row_8 j
  · exact matrix_mul_inverse_row_9 j
  · exact matrix_mul_inverse_row_10 j
  · exact matrix_mul_inverse_row_11 j
  · exact matrix_mul_inverse_row_12 j
  · exact matrix_mul_inverse_row_13 j
  · exact matrix_mul_inverse_row_14 j
  · exact matrix_mul_inverse_row_15 j
  · exact matrix_mul_inverse_row_16 j
  · exact matrix_mul_inverse_row_17 j
  · exact matrix_mul_inverse_row_18 j
  · exact matrix_mul_inverse_row_19 j
  · exact matrix_mul_inverse_row_20 j
  · exact matrix_mul_inverse_row_21 j
  · exact matrix_mul_inverse_row_22 j
  · exact matrix_mul_inverse_row_23 j
  · exact matrix_mul_inverse_row_24 j
  · exact matrix_mul_inverse_row_25 j
  · exact matrix_mul_inverse_row_26 j
  · exact matrix_mul_inverse_row_27 j
  · exact matrix_mul_inverse_row_28 j
  · exact matrix_mul_inverse_row_29 j
  · exact matrix_mul_inverse_row_30 j
  · exact matrix_mul_inverse_row_31 j
  · exact matrix_mul_inverse_row_32 j
  · exact matrix_mul_inverse_row_33 j
  · exact matrix_mul_inverse_row_34 j
  · exact matrix_mul_inverse_row_35 j
  · exact matrix_mul_inverse_row_36 j
  · exact matrix_mul_inverse_row_37 j
  · exact matrix_mul_inverse_row_38 j
  · exact matrix_mul_inverse_row_39 j
  · exact matrix_mul_inverse_row_40 j
  · exact matrix_mul_inverse_row_41 j
  · exact matrix_mul_inverse_row_42 j
  · exact matrix_mul_inverse_row_43 j
  · exact matrix_mul_inverse_row_44 j
  · exact matrix_mul_inverse_row_45 j
  · exact matrix_mul_inverse_row_46 j
  · exact matrix_mul_inverse_row_47 j
  · exact matrix_mul_inverse_row_48 j
  · exact matrix_mul_inverse_row_49 j
  · exact matrix_mul_inverse_row_50 j
  · exact matrix_mul_inverse_row_51 j
  · exact matrix_mul_inverse_row_52 j
  · exact matrix_mul_inverse_row_53 j
  · exact matrix_mul_inverse_row_54 j
  · exact matrix_mul_inverse_row_55 j
  · exact matrix_mul_inverse_row_56 j
  · exact matrix_mul_inverse_row_57 j
  · exact matrix_mul_inverse_row_58 j
  · exact matrix_mul_inverse_row_59 j
  · exact matrix_mul_inverse_row_60 j
  · exact matrix_mul_inverse_row_61 j
  · exact matrix_mul_inverse_row_62 j
  · exact matrix_mul_inverse_row_63 j
  · exact matrix_mul_inverse_row_64 j
  · exact matrix_mul_inverse_row_65 j
  · exact matrix_mul_inverse_row_66 j
  · exact matrix_mul_inverse_row_67 j
  · exact matrix_mul_inverse_row_68 j
  · exact matrix_mul_inverse_row_69 j
  · exact matrix_mul_inverse_row_70 j
  · exact matrix_mul_inverse_row_71 j
  · exact matrix_mul_inverse_row_72 j
  · exact matrix_mul_inverse_row_73 j
  · exact matrix_mul_inverse_row_74 j
  · exact matrix_mul_inverse_row_75 j
  · exact matrix_mul_inverse_row_76 j

/-- The successful second circular-unit probe is nonsingular over
`ZMod 157`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det matrix_mul_inverse
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact (by decide : (0 : ZMod 157) ≠ 1) hdet

end

end Fermat.OneHundredFiftySeven.CircularUnitCertificate
