import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesBase
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCertificate

/-!
# Circular-unit residue certificate at exponent 1831

The determinant-free residue setup is provided by `CircularUnitResiduesBase`.
This module retains the original route from the full `914 × 914` determinant
certificate to the real circular-unit index.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneThousandEightHundredThirtyOne.prime_1831 (by norm_num)

/-- The circular-unit subgroup has real index prime to `1831`. -/
theorem not_dvd_circularUnit1831_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831) :
    ¬1831 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate.matrix_det_ne_zero

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues
