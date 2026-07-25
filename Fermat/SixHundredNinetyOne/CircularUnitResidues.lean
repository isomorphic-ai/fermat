import Fermat.SixHundredNinetyOne.CircularUnitCertificate
import Fermat.SixHundredNinetyOne.CircularUnitEntryCertificate

/-!
# Circular-unit residue certificate at exponent 691

The compressed finite-field computation at `11057` is bundled into the
generic circular-unit residue interface. Its `344 × 344` matrix is not
expanded entry by entry here: `CircularUnitEntryCertificate` reconstructs
every entry from 345 cyclic phase values, while `CircularUnitCertificate`
proves nonsingularity from the matching cyclic-correlation inverse.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.SixHundredNinetyOne.CircularUnitEntryCertificate
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 691) :=
  ⟨Fermat.SixHundredNinetyOne.prime_691⟩
local instance : Fact (Nat.Prime 11057) :=
  ⟨Fermat.SixHundredNinetyOne.prime_11057⟩

/-- The complete `q = 11057` residue-symbol certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 691 11057 where
  hp2 := by norm_num
  symbolExponent := 16
  q_sub_one := by norm_num
  root := 1820
  root_isPrimitive :=
    Fermat.SixHundredNinetyOne.CircularUnitEntryCertificate.root_isPrimitive
  matrix := Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {691} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.SixHundredNinetyOne.prime_691 (by norm_num)

/-- The checked finite phases reconstruct the evaluation matrix on
cyclotomic units modulo torsion. -/
theorem evalMatrix_circularUnit691
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 691) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- The circular-unit subgroup has real index prime to `691`. -/
theorem not_dvd_circularUnit691_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 691) :
    ¬691 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta
    Fermat.SixHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero

end Fermat.SixHundredNinetyOne.CircularUnitResidues
