import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverRelationNormalization1831

/-!
# Transferring congruences through positive relation normalization

The positive exponent used in Vandiver's polynomial calculation differs
from the original integer exponent by a multiple of `1831^3`. Consequently
the coefficient-wise cube divisibility obtained from the positive
calculation descends unchanged to the original relation.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedCongruence

open Fermat.OneThousandEightHundredThirtyOne.VandiverRelationNormalization

/-- Divisibility by `1831^3` for a normalized exponent times an arbitrary
integer factor implies the same divisibility for the original exponent
times that factor. -/
theorem cube_dvd_mul_of_normalizedRelationExponent1831
    (t : ℕ) (ht : 0 < t) (a B : ℤ)
    (h : (1831 : ℤ) ^ 3 ∣
      (normalizedRelationExponent1831 t a : ℤ) * B) :
    (1831 : ℤ) ^ 3 ∣ a * B := by
  have hcorrection : (1831 : ℤ) ^ 3 ∣
      (normalizedRelationExponent1831 t a : ℤ) * B - a * B := by
    refine ⟨(t : ℤ) * ((-a).toNat : ℤ) * B, ?_⟩
    rw [normalizedRelationExponent1831_cast t ht a]
    push_cast
    ring
  have hsub := dvd_sub h hcorrection
  convert hsub using 1
  ring

end Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedCongruence
