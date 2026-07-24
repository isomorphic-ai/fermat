import Fermat.ThirtySeven.VandiverRelationNormalization

/-!
# Transferring congruences through positive relation normalization

The positive exponent used in Vandiver's polynomial calculation differs
from the original integer exponent by a multiple of `37^3`.  Consequently
the coefficient-wise cube divisibility obtained from the positive
calculation descends unchanged to the original relation.
-/

namespace Fermat.ThirtySeven.VandiverNormalizedCongruence

open Fermat.ThirtySeven.VandiverRelationNormalization

/-- Divisibility by `37^3` for a normalized exponent times an arbitrary
integer factor implies the same divisibility for the original exponent
times that factor. -/
theorem cube_dvd_mul_of_normalizedRelationExponent37
    (t : ℕ) (ht : 0 < t) (a B : ℤ)
    (h : (37 : ℤ) ^ 3 ∣
      (normalizedRelationExponent37 t a : ℤ) * B) :
    (37 : ℤ) ^ 3 ∣ a * B := by
  have hcorrection : (37 : ℤ) ^ 3 ∣
      (normalizedRelationExponent37 t a : ℤ) * B - a * B := by
    refine ⟨(t : ℤ) * ((-a).toNat : ℤ) * B, ?_⟩
    rw [normalizedRelationExponent37_cast t ht a]
    push_cast
    ring
  have hsub := dvd_sub h hcorrection
  convert hsub using 1
  ring

end Fermat.ThirtySeven.VandiverNormalizedCongruence
