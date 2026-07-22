import Fermat.Basic
import Fermat.ThirtySeven.CircularUnitCertificate

/-!
# Finite-field provenance of the exponent-thirty-seven matrix

The uploaded matrix was obtained from normalized circular-unit values at the
auxiliary prime `149`.  This module checks every one of its 289 entries
directly in `ZMod 149`: raising the normalized value to `(149 - 1) / 37 = 4`
gives the recorded power of the fixed 37th root `16`.

This is the finite-field half of the residue-symbol certificate.  Constructing
the resulting homomorphisms on cyclotomic units modulo torsion remains a
separate global number-theoretic bridge.
-/

namespace Fermat.ThirtySeven.CircularUnitResidues

open Fermat.ThirtySeven.CircularUnitCertificate

local instance : Fact (Nat.Prime 149) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The conjugate of the fixed 37th root used in row `j`. -/
def embeddingRoot (j : Fin 17) : ZMod 149 :=
  16 ^ (j.val + 1)

/-- The circular-unit index used in column `i`. -/
def unitIndex (i : Fin 17) : ℕ :=
  i.val + 2

/-- The least nonnegative representative of `(1 - a) / 2` modulo `37`.
Here `19` is the inverse of `2` modulo `37`. -/
def normalizationExponent (i : Fin 17) : ℕ :=
  ((38 - unitIndex i) * 19) % 37

/-- The normalized circular-unit value
`r^((1-a)/2) * (1-r^a)/(1-r)` at the selected embedding. -/
def normalizedUnitValue (j i : Fin 17) : ZMod 149 :=
  embeddingRoot j ^ normalizationExponent i *
    (1 - embeddingRoot j ^ unitIndex i) / (1 - embeddingRoot j)

/-- The fixed element `16` has exact order `37` modulo `149`. -/
theorem root_order : orderOf (16 : ZMod 149) = 37 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- Every entry of the uploaded matrix is the discrete logarithm of the
corresponding fourth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 17) :
    normalizedUnitValue j i ^ 4 =
      (16 : ZMod 149) ^ (matrix j i).val := by
  fin_cases j <;> fin_cases i <;> decide

end Fermat.ThirtySeven.CircularUnitResidues
