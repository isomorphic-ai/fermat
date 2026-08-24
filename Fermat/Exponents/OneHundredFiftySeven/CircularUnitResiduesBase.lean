import Fermat.Exponents.OneHundredFiftySeven.CircularUnitResidueEntryBase

/-!
# Determinant-free circular-unit residue setup at exponent 157

The finite computation at `q = 7537` is bundled into the generic residue
certificate.  This module authenticates all matrix entries but deliberately
does not import the old inverse or determinant certificate, so selective
Bernoulli-channel routes can reuse the same provenance independently.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.CircularUnitResidues

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnits
open Fermat.OneHundredFiftySeven.CircularUnitResidueEntryBase
open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩

/-- The complete finite `q = 7537` residue-symbol computation, without any
nonsingularity hypothesis or conclusion. -/
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

/-- The finite entry certificates construct the actual evaluation matrix on
units modulo torsion. -/
theorem evalMatrix_circularUnit157
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

end


end Fermat.OneHundredFiftySeven.CircularUnitResidues
