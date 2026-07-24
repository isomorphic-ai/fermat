import Fermat.FourHundredNinetyOne.CircularUnitCertificate
import Fermat.FourHundredNinetyOne.CircularUnitEntryCertificate

/-!
# Circular-unit residue certificate at exponent 491

The compressed finite-field computation at `q = 983` is bundled into the
generic circular-unit residue interface.  The source matrix is reconstructed
from 245 cyclic phase values; its matching cyclic inverse proves
nonsingularity without expanding a dense inverse.
-/

namespace Fermat.FourHundredNinetyOne.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.FourHundredNinetyOne.CircularUnitEntryCertificate
open Fermat.FourHundredNinetyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 491) :=
  ⟨Fermat.FourHundredNinetyOne.prime_491⟩
local instance : Fact (Nat.Prime 983) :=
  ⟨Fermat.FourHundredNinetyOne.prime_983⟩

/-- The complete `q = 983` residue-symbol certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 491 983 where
  hp2 := by norm_num
  symbolExponent := 2
  q_sub_one := by norm_num
  root := 2
  root_isPrimitive :=
    Fermat.FourHundredNinetyOne.CircularUnitEntryCertificate.root_isPrimitive
  matrix := Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.FourHundredNinetyOne.prime_491 (by norm_num)

/-- The checked phases reconstruct the circular-unit evaluation matrix. -/
theorem evalMatrix_circularUnit491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- The circular-unit subgroup has real index prime to `491`. -/
theorem not_dvd_circularUnit491_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    ¬491 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta
    Fermat.FourHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero

end Fermat.FourHundredNinetyOne.CircularUnitResidues
