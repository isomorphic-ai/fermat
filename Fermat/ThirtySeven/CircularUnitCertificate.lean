import Fermat.Irregular.CircularUnits

/-!
# The uploaded circular-unit matrix at exponent thirty-seven

This file kernel-checks the nonsingularity of the exact `17 × 17` matrix
from the exponent-`37` proof package.  An explicit inverse keeps the
certificate small: checking a matrix product requires only finite arithmetic,
whereas expanding a `17 × 17` determinant by permutations would be
prohibitively slow.

The certificate proves the lattice-index consequence once the entries have
been realized by power-residue homomorphisms.  It does not assert the missing
circular-unit index formula relating that lattice index to `h⁺`.
-/

namespace Fermat.ThirtySeven.CircularUnitCertificate

open Fermat.Irregular.CircularUnits
open Module

/-- Rows `q₁,…,q₁₇` and columns `c₂,…,c₁₈` of the uploaded
power-residue-symbol certificate. -/
def matrix : Matrix (Fin 17) (Fin 17) (ZMod 37) := ![
  ![11, 19, 11, 8, 12, 6, 24, 36, 4, 20, 14, 4, 27, 19, 18, 2, 25],
  ![0, 1, 13, 30, 3, 16, 7, 14, 28, 8, 30, 9, 25, 32, 34, 8, 26],
  ![30, 17, 32, 0, 6, 36, 22, 22, 24, 29, 18, 29, 26, 5, 1, 8, 20],
  ![13, 3, 7, 28, 30, 25, 34, 26, 8, 32, 9, 8, 14, 16, 30, 1, 0],
  ![33, 11, 31, 6, 35, 3, 11, 16, 33, 17, 19, 28, 3, 29, 4, 12, 10],
  ![2, 13, 29, 31, 25, 33, 8, 27, 15, 12, 36, 36, 29, 6, 7, 24, 7],
  ![21, 12, 30, 5, 2, 8, 19, 14, 5, 13, 35, 33, 35, 6, 31, 18, 13],
  ![31, 17, 21, 32, 33, 1, 17, 24, 25, 3, 32, 19, 13, 12, 15, 27, 24],
  ![26, 5, 1, 25, 3, 21, 12, 7, 19, 15, 20, 13, 20, 5, 12, 9, 28],
  ![35, 2, 15, 0, 23, 7, 8, 14, 16, 33, 32, 21, 20, 7, 10, 15, 4],
  ![36, 28, 23, 5, 4, 36, 7, 31, 17, 21, 35, 25, 29, 19, 16, 28, 21],
  ![27, 23, 6, 13, 34, 27, 5, 5, 22, 4, 34, 10, 25, 31, 29, 11, 35],
  ![16, 7, 15, 32, 7, 35, 2, 8, 21, 4, 20, 14, 15, 0, 23, 33, 10],
  ![9, 18, 35, 21, 14, 14, 10, 29, 34, 22, 12, 29, 30, 24, 21, 28, 16],
  ![24, 5, 8, 18, 36, 30, 17, 22, 29, 20, 26, 22, 32, 0, 6, 29, 1],
  ![27, 2, 23, 31, 1, 19, 21, 30, 33, 18, 25, 9, 30, 7, 1, 23, 6],
  ![17, 25, 10, 18, 34, 22, 12, 6, 17, 9, 23, 35, 16, 9, 2, 4, 2]
]

/-- An explicit inverse of `matrix` over `ZMod 37`. -/
def matrixInverse : Matrix (Fin 17) (Fin 17) (ZMod 37) := ![
  ![16, 3, 33, 27, 24, 22, 35, 9, 2, 36, 7, 6, 24, 19, 36, 18, 15],
  ![16, 34, 20, 23, 8, 3, 10, 7, 25, 0, 4, 1, 17, 19, 28, 25, 36],
  ![24, 11, 6, 30, 20, 27, 3, 2, 21, 36, 20, 8, 28, 23, 19, 8, 17],
  ![9, 15, 35, 27, 13, 27, 7, 6, 18, 34, 30, 26, 10, 31, 28, 24, 15],
  ![18, 7, 24, 28, 21, 22, 3, 9, 21, 20, 12, 1, 25, 9, 31, 29, 4],
  ![29, 28, 2, 12, 9, 11, 15, 32, 17, 33, 8, 17, 29, 36, 26, 30, 20],
  ![24, 6, 3, 15, 12, 21, 36, 21, 13, 30, 32, 4, 33, 34, 16, 33, 19],
  ![21, 4, 26, 2, 29, 1, 26, 18, 1, 11, 24, 17, 35, 9, 8, 5, 20],
  ![6, 18, 18, 34, 25, 17, 22, 15, 28, 6, 19, 1, 21, 9, 35, 4, 26],
  ![18, 1, 34, 30, 33, 21, 9, 29, 16, 31, 18, 3, 12, 27, 30, 13, 10],
  ![26, 10, 4, 28, 2, 20, 28, 11, 19, 23, 13, 7, 31, 3, 22, 3, 6],
  ![21, 2, 31, 22, 34, 18, 14, 14, 11, 17, 33, 5, 24, 30, 2, 13, 15],
  ![36, 20, 19, 3, 4, 25, 7, 1, 8, 28, 34, 0, 16, 25, 23, 17, 10],
  ![20, 12, 3, 11, 13, 22, 9, 32, 19, 29, 12, 31, 0, 35, 28, 15, 16],
  ![19, 28, 34, 34, 6, 17, 10, 9, 13, 32, 29, 9, 8, 26, 12, 25, 16],
  ![12, 28, 11, 9, 0, 32, 3, 35, 31, 20, 29, 15, 13, 22, 16, 19, 12],
  ![20, 18, 17, 34, 27, 33, 25, 21, 16, 36, 24, 14, 3, 17, 5, 8, 5]
]

/-- Kernel-checked multiplication of the uploaded matrix by its certificate
inverse. -/
theorem matrix_mul_inverse : matrix * matrixInverse = 1 := by
  decide

/-- The uploaded matrix is nonsingular over `ZMod 37`. -/
theorem matrix_det_ne_zero : matrix.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det matrix_mul_inverse
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact (by decide : (0 : ZMod 37) ≠ 1) hdet

/-- Once an actual family of residue-symbol homomorphisms has the uploaded
evaluation matrix, its generated lattice has index prime to `37`. -/
theorem not_dvd_card_quotient_span_of_evalMatrix_eq
    {M : Type*} [AddCommGroup M] (b : Basis (Fin 17) ℤ M)
    (u : Fin 17 → M) (f : Fin 17 → M →ₗ[ℤ] ZMod 37)
    (heval : evalMatrix u f = matrix) :
    ¬ (37 ∣ Nat.card (M ⧸ Submodule.span ℤ (Set.range u))) := by
  apply not_dvd_card_quotient_span_of_eval_det_ne_zero b u f
  rw [heval]
  exact matrix_det_ne_zero

end Fermat.ThirtySeven.CircularUnitCertificate
