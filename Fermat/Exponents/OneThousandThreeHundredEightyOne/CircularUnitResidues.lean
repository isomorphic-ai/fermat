import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCertificate
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate

/-!
# Circular-unit residue certificate at exponent 1381

The compressed finite-field computation at `38669` is bundled into the
generic circular-unit residue interface. Its `689 × 689` matrix is not
expanded entry by entry here: `CircularUnitEntryCertificate` reconstructs
every entry from 690 cyclic phase values, while `CircularUnitCertificate`
proves nonsingularity from the matching cyclic-correlation inverse.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (Nat.Prime 38669) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_38669⟩

/-- The complete `q = 38669` residue-symbol certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 1381 38669 where
  hp2 := by norm_num
  symbolExponent := 28
  q_sub_one := by norm_num
  root := 33927
  root_isPrimitive :=
    Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate.root_isPrimitive
  matrix := Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix.matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {1381} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneThousandThreeHundredEightyOne.prime_1381 (by norm_num)

/-- The checked finite phases reconstruct the evaluation matrix on
cyclotomic units modulo torsion. -/
theorem evalMatrix_circularUnit1381
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- The circular-unit subgroup has real index prime to `1381`. -/
theorem not_dvd_circularUnit1381_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381) :
    ¬1381 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta
    Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate.matrix_det_ne_zero

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitResidues
