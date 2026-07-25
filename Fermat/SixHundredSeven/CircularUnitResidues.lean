import Fermat.SixHundredSeven.CircularUnitCertificate
import Fermat.SixHundredSeven.CircularUnitEntryCertificate

/-!
# Circular-unit residue certificate at exponent 607

The compressed finite-field computation at `20639` is bundled into the
generic circular-unit residue interface. Its `302 × 302` matrix is not
expanded entry by entry: the entry modules reconstruct every entry from 303
cyclic phase values, while the correlation certificate proves
nonsingularity from the matching cyclic inverse.
-/

namespace Fermat.SixHundredSeven.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.SixHundredSeven.CircularUnitEntryCertificate
open Fermat.SixHundredSeven.CircularUnitMatrix

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩

/-- The complete `q = 20639` residue-symbol certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 607 20639 where
  hp2 := by norm_num
  symbolExponent := 34
  q_sub_one := by norm_num
  root := 14674
  root_isPrimitive :=
    Fermat.SixHundredSeven.CircularUnitEntryCertificate.root_isPrimitive
  matrix := Fermat.SixHundredSeven.CircularUnitMatrix.matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {607} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.SixHundredSeven.prime_607 (by norm_num)

/-- The checked finite phases reconstruct the evaluation matrix on
cyclotomic units modulo torsion. -/
theorem evalMatrix_circularUnit607
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- The circular-unit subgroup has real index prime to `607`. -/
theorem not_dvd_circularUnit607_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607) :
    ¬607 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta
    Fermat.SixHundredSeven.CircularUnitCertificate.matrix_det_ne_zero

end Fermat.SixHundredSeven.CircularUnitResidues
