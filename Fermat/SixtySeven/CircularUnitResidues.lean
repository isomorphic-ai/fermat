import Fermat.Irregular.CircularUnitResidues
import Fermat.SixtySeven.CircularUnitCertificate
import Fermat.SixtySeven.FirstCase

/-!
# Finite-field provenance of the exponent-67 matrix

The uploaded matrix is obtained from the canonical normalized circular-unit
values at `269`.  For row `j` and column `i`, raising the value to
`(269 - 1) / 67 = 4` produces the recorded power of the fixed root `16`.
All `1024` entries are checked in the kernel.
-/

namespace Fermat.SixtySeven.CircularUnitResidues

open Fermat.Irregular.CircularUnitFamily
open Fermat.SixtySeven.CircularUnitCertificate

local instance : Fact (Nat.Prime 269) := ⟨Fermat.SixtySeven.prime_269⟩
local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩

def embeddingRoot (j : Fin 32) : ZMod 269 :=
  16 ^ (j.val + 1)

def unitIndex (i : Fin 32) : ℕ :=
  i.val + 2

def normalizationExponent (i : Fin 32) : ℕ :=
  canonicalNormalizationExponent (p := 67) (unitIndex i)

def normalizedUnitValue (j i : Fin 32) : ZMod 269 :=
  embeddingRoot j ^ normalizationExponent i *
    (1 - embeddingRoot j ^ unitIndex i) / (1 - embeddingRoot j)

theorem root_order : orderOf (16 : ZMod 269) = 67 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- Every matrix entry has been reconstructed from the finite-field residue
symbol, rather than trusted as an opaque CSV value. -/
theorem matrix_entry_certificate (j i : Fin 32) :
    normalizedUnitValue j i ^ 4 =
      (16 : ZMod 269) ^ (matrix j i).val := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 100000 in
      rw [normalizedUnitValue, div_pow]
      apply (div_eq_iff ?_).2
      · decide +kernel +revert
      · decide +kernel +revert

/-! ## Generic residue-character assembly -/

/-- The entire finite q=269 computation bundled for the generic
residue-character construction. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 67 269 where
  hp2 := by norm_num
  symbolExponent := 4
  q_sub_one := by norm_num
  root := 16
  root_isPrimitive := IsPrimitiveRoot.iff_orderOf.mpr root_order
  matrix := matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {67} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K) Fermat.SixtySeven.prime_67
    (by norm_num)

/-- The finite entry certificate now produces the actual evaluation matrix
on units modulo torsion, with no exponent-local homomorphism hypothesis. -/
theorem evalMatrix_circularUnit67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67) :
    Fermat.Irregular.CircularUnits.evalMatrix
        (classOfUnit ∘ circularUnitFamily hzeta (by norm_num))
        (certificate.residueFunctionals hzeta) = matrix := by
  exact certificate.evalMatrix_circularUnitFamily hzeta

/-- Unconditional algebraic endpoint before Sinnott--Kummer: the relative
real circular-unit index is prime to `67`. -/
theorem not_dvd_circularUnit67_real_index
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67) :
    ¬67 ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta (by norm_num))) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  exact certificate.not_dvd_circularUnitFamily_real_index_of_cyclotomic
    hzeta matrix_det_ne_zero

end Fermat.SixtySeven.CircularUnitResidues
