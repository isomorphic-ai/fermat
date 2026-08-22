import Fermat.Exponents.SixHundredSeven.VandiverRelationNormalization607

/-!
# Transferring congruences through positive relation normalization

The positive exponent used in Vandiver's polynomial calculation differs
from the original integer exponent by a multiple of `607^3`. Consequently
the coefficient-wise cube divisibility obtained from the positive
calculation descends unchanged to the original relation.
-/

namespace Fermat.SixHundredSeven.VandiverNormalizedCongruence

open Fermat.SixHundredSeven.VandiverRelationNormalization

/-- Divisibility by `607^3` for a normalized exponent times an arbitrary
integer factor implies the same divisibility for the original exponent
times that factor. -/
theorem cube_dvd_mul_of_normalizedRelationExponent607
    (t : ℕ) (ht : 0 < t) (a B : ℤ)
    (h : (607 : ℤ) ^ 3 ∣
      (normalizedRelationExponent607 t a : ℤ) * B) :
    (607 : ℤ) ^ 3 ∣ a * B := by
  have hcorrection : (607 : ℤ) ^ 3 ∣
      (normalizedRelationExponent607 t a : ℤ) * B - a * B := by
    refine ⟨(t : ℤ) * ((-a).toNat : ℤ) * B, ?_⟩
    rw [normalizedRelationExponent607_cast t ht a]
    push_cast
    ring
  have hsub := dvd_sub h hcorrection
  convert hsub using 1
  ring

end Fermat.SixHundredSeven.VandiverNormalizedCongruence
