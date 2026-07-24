import Fermat.OneThousandThreeHundredEightyOne.VandiverRelationNormalization1381

/-!
# Transferring congruences through positive relation normalization

The positive exponent used in Vandiver's polynomial calculation differs
from the original integer exponent by a multiple of `1381^3`. Consequently
the coefficient-wise cube divisibility obtained from the positive
calculation descends unchanged to the original relation.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedCongruence

open Fermat.OneThousandThreeHundredEightyOne.VandiverRelationNormalization

/-- Divisibility by `1381^3` for a normalized exponent times an arbitrary
integer factor implies the same divisibility for the original exponent
times that factor. -/
theorem cube_dvd_mul_of_normalizedRelationExponent1381
    (t : ℕ) (ht : 0 < t) (a B : ℤ)
    (h : (1381 : ℤ) ^ 3 ∣
      (normalizedRelationExponent1381 t a : ℤ) * B) :
    (1381 : ℤ) ^ 3 ∣ a * B := by
  have hcorrection : (1381 : ℤ) ^ 3 ∣
      (normalizedRelationExponent1381 t a : ℤ) * B - a * B := by
    refine ⟨(t : ℤ) * ((-a).toNat : ℤ) * B, ?_⟩
    rw [normalizedRelationExponent1381_cast t ht a]
    push_cast
    ring
  have hsub := dvd_sub h hcorrection
  convert hsub using 1
  ring

end Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedCongruence
