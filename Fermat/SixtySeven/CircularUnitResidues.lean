import Fermat.Irregular.CircularUnitFamily
import Fermat.SixtySeven.CircularUnitCertificate
import Fermat.SixtySeven.FirstCase

/-!
# Finite-field provenance of the exponent-67 matrix

The uploaded matrix is obtained from the canonical normalized circular-unit
values at `269`.  For row `j` and column `i`, raising the value to
`(269 - 1) / 67 = 4` produces the recorded power of the fixed root `16`.
All `1024` entries are checked in the kernel.
-/

namespace Fermat.SixtySeven.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.SixtySeven.CircularUnitCertificate

local instance : Fact (Nat.Prime 269) := ⟨Fermat.SixtySeven.prime_269⟩
local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩

def embeddingRoot (j : Fin 32) : ZMod 269 :=
  16 ^ (j.val + 1)

def unitIndex (i : Fin 32) : ℕ :=
  i.val + 2

def normalizationExponent (i : Fin 32) : ℕ :=
  canonicalNormalizationExponent (p := 67) (unitIndex i)

def normalizedUnitValue (j i : Fin 32) : ZMod 269 :=
  embeddingRoot j ^ normalizationExponent i *
    (1 - embeddingRoot j ^ unitIndex i) / (1 - embeddingRoot j)

theorem root_order : orderOf (16 : ZMod 269) = 67 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- Every matrix entry has been reconstructed from the finite-field residue
symbol, rather than trusted as an opaque CSV value. -/
theorem matrix_entry_certificate (j i : Fin 32) :
    normalizedUnitValue j i ^ 4 =
      (16 : ZMod 269) ^ (matrix j i).val := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      fin_cases j <;> fin_cases i <;> decide

end Fermat.SixtySeven.CircularUnitResidues
