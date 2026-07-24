import Fermat.Irregular.CircularUnitResidues
import Fermat.OneHundredFiftySeven.CircularUnitCertificate
import Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate

/-!
# Finite-field provenance of the exponent-157 unit matrix

The successful second probe in the uploaded package is the split prime
`7537 = 48 * 157 + 1`, with the fixed order-`157` root
`418 = 7^48`.  Every one of the `77 * 77` matrix entries is recomputed
from the canonical normalized circular unit and its forty-eighth-power
residue symbol.

The generic residue-character construction then turns this finite data
into actual linear functionals on units modulo torsion.  Consequently the
relative real circular-unit index is prime to `157`.  The subsequent
Sinnott--Kummer identification with the plus class number remains the
shared historical boundary and is not asserted here.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.CircularUnitResidues

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnits
open Fermat.OneHundredFiftySeven.CircularUnitCertificate
open Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate
open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩

/-- The complete finite `q = 7537` computation bundled for the generic
residue-character construction. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 157 7537 where
  hp2 := by norm_num
  symbolExponent := 48
  q_sub_one := by norm_num
  root := 418
  root_isPrimitive := root_isPrimitive
  matrix := matrix
  entry_certificate := matrix_entry_certificate

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneHundredFiftySeven.prime_157 (by norm_num)

/-- The finite entry certificates construct the actual evaluation matrix
on units modulo torsion. -/
theorem evalMatrix_circularUnit157
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- Unconditional algebraic endpoint immediately before Sinnott--Kummer:
the relative index of the canonical real circular units is prime to `157`.
-/
theorem not_dvd_circularUnit157_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    ¬157 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta matrix_det_ne_zero

end

end Fermat.OneHundredFiftySeven.CircularUnitResidues
