import Fermat.FiftyNine.CircularUnitCertificate
import Fermat.FiftyNine.FirstCase
import Fermat.Irregular.CircularUnitFamily
import Fermat.Irregular.CircularUnitResidues

/-!
# Finite-field provenance of the exponent-59 unit matrix

The matrix certificate is not treated as opaque data.  Every entry is
recomputed from the canonical generic circular-unit family at the split
prime `827`, using the fixed order-`59` root `671` and the fourteenth-power
residue symbol.
-/

namespace Fermat.FiftyNine.CircularUnitResidues

open Fermat.FiftyNine.CircularUnitCertificate
open Fermat.Irregular.CircularUnitFamily

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 827) := ⟨Fermat.FiftyNine.prime_827⟩
local instance : Fact (Nat.Prime 59) := ⟨Fermat.FiftyNine.prime_59⟩

/-- The conjugate of the fixed order-`59` root used in row `j`. -/
def embeddingRoot (j : Fin 28) : ZMod 827 :=
  671 ^ (j.val + 1)

/-- The circular-unit column index `a = 2, ..., 29`. -/
def unitIndex (i : Fin 28) : ℕ :=
  i.val + 2

/-- Canonical exponent representing `(1-a)/2` modulo `59`. -/
def normalizationExponent (i : Fin 28) : ℕ :=
  canonicalNormalizationExponent (p := 59) (unitIndex i)

/-- The finite-field value of the canonical normalized circular unit. -/
def normalizedUnitValue (j i : Fin 28) : ZMod 827 :=
  embeddingRoot j ^ normalizationExponent i *
    (1 - embeddingRoot j ^ unitIndex i) / (1 - embeddingRoot j)

/-- The package's fixed root `671 = 2^14` has exact order `59`. -/
theorem root_order : orderOf (671 : ZMod 827) = 59 := by
  exact orderOf_eq_prime (by decide) (by decide)

/-- Every row root remains primitive because `1 ≤ j+1 ≤ 28 < 59`. -/
theorem embeddingRoot_isPrimitive (j : Fin 28) :
    IsPrimitiveRoot (embeddingRoot j) 59 := by
  have hroot : IsPrimitiveRoot (671 : ZMod 827) 59 :=
    IsPrimitiveRoot.iff_orderOf.mpr root_order
  apply hroot.pow_of_coprime
  exact Nat.Coprime.symm <| Nat.coprime_of_lt_prime
    (by omega) (by omega) Fermat.FiftyNine.prime_59

/-- Every one of the 784 uploaded entries is the discrete logarithm of the
corresponding fourteenth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 28) :
    normalizedUnitValue j i ^ 14 =
      (671 : ZMod 827) ^ (matrix j i).val := by
  rw [normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

/-- The complete finite exponent-`59` certificate, packaged for the generic
residue-character construction. -/
def residueCertificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 59 827 where
  hp2 := by norm_num
  symbolExponent := 14
  q_sub_one := by norm_num
  root := 671
  root_isPrimitive := IsPrimitiveRoot.iff_orderOf.mpr root_order
  matrix := matrix
  entry_certificate := by
    intro j i
    simpa [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue,
      Fermat.Irregular.CircularUnitResidues.embeddingRoot,
      normalizedUnitValue, embeddingRoot, normalizationExponent, unitIndex] using
      matrix_entry_certificate j i

end Fermat.FiftyNine.CircularUnitResidues
