import Fermat.FiftyNine.VandiverRelationNormalization

/-!
# Transferring congruences through positive relation normalization

The positive exponent used in Vandiver's polynomial calculation differs
from the original integer exponent by a multiple of `59^3`.  Consequently
the coefficient-wise cube divisibility obtained from the positive
calculation descends unchanged to the original relation.
-/

namespace Fermat.FiftyNine.VandiverNormalizedCongruence

open Fermat.FiftyNine.VandiverRelationNormalization

/-- Divisibility by `59^3` for a normalized exponent times an arbitrary
integer factor implies the same divisibility for the original exponent
times that factor. -/
theorem cube_dvd_mul_of_normalizedRelationExponent59
    (t : ℕ) (ht : 0 < t) (a B : ℤ)
    (h : (59 : ℤ) ^ 3 ∣
      (normalizedRelationExponent59 t a : ℤ) * B) :
    (59 : ℤ) ^ 3 ∣ a * B := by
  have hcorrection : (59 : ℤ) ^ 3 ∣
      (normalizedRelationExponent59 t a : ℤ) * B - a * B := by
    refine ⟨(t : ℤ) * ((-a).toNat : ℤ) * B, ?_⟩
    rw [normalizedRelationExponent59_cast t ht a]
    push_cast
    ring
  have hsub := dvd_sub h hcorrection
  convert hsub using 1
  ring

end Fermat.FiftyNine.VandiverNormalizedCongruence
