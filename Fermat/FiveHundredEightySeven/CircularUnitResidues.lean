import Fermat.FiveHundredEightySeven.CircularUnitCertificate
import Fermat.FiveHundredEightySeven.CircularUnitEntryCertificate

/-!
# Circular-unit residue certificate at exponent 587

The compressed finite-field computation at `8219` is bundled into the
generic circular-unit residue interface.  Its `292 × 292` matrix is not
expanded entry by entry here: `CircularUnitEntryCertificate` reconstructs
every entry from 293 cyclic phase values, while
`CircularUnitCertificate` proves nonsingularity from the matching cyclic
correlation inverse.
-/

namespace Fermat.FiveHundredEightySeven.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.FiveHundredEightySeven.CircularUnitEntryCertificate
open Fermat.FiveHundredEightySeven.CircularUnitMatrix

local instance : Fact (Nat.Prime 587) :=
  ⟨Fermat.FiveHundredEightySeven.prime_587⟩
local instance : Fact (Nat.Prime 8219) :=
  ⟨Fermat.FiveHundredEightySeven.prime_8219⟩

/-- The complete `q = 8219` residue-symbol certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 587 8219 where
  hp2 := by norm_num
  symbolExponent := 14
  q_sub_one := by norm_num
  root := 8165
  root_isPrimitive :=
    Fermat.FiveHundredEightySeven.CircularUnitEntryCertificate.root_isPrimitive
  matrix := Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {587} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.FiveHundredEightySeven.prime_587 (by norm_num)

/-- The checked finite phases reconstruct the evaluation matrix on
cyclotomic units modulo torsion. -/
theorem evalMatrix_circularUnit587
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 587) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- The circular-unit subgroup has real index prime to `587`. -/
theorem not_dvd_circularUnit587_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 587) :
    ¬587 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta
    Fermat.FiveHundredEightySeven.CircularUnitCertificate.matrix_det_ne_zero

end Fermat.FiveHundredEightySeven.CircularUnitResidues
