import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate

/-!
# Circular-unit residue setup at exponent 1831

The compressed finite-field computation at `358877` is bundled into the
generic circular-unit residue interface. Its `914 × 914` matrix is not
expanded entry by entry here: `CircularUnitEntryCertificate` reconstructs
every entry from 915 cyclic phase values.

This determinant-free module contains the shared residue certificate and its
evaluation-matrix identification. Independent downstream routes can therefore
reuse the same checked entries without importing a nonsingularity certificate.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- The complete `q = 358877` residue-symbol certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 1831 358877 where
  hp2 := by norm_num
  symbolExponent := 196
  q_sub_one := by norm_num
  root := 266093
  root_isPrimitive :=
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.root_isPrimitive
  matrix := Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix.matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneThousandEightHundredThirtyOne.prime_1831 (by norm_num)

/-- The checked finite phases reconstruct the evaluation matrix on
cyclotomic units modulo torsion. -/
theorem evalMatrix_circularUnit1831
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues
