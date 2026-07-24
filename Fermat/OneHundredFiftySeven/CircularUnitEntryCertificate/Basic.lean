import Fermat.Irregular.CircularUnitResidues
import Fermat.OneHundredFiftySeven.FoldCertificates
import Fermat.OneHundredFiftySeven.CircularUnitCertificate

/-!
# Basic data for the exponent-157 circular-unit entry certificate

At the successful second probe `q = 7537`, the package uses the order-157
root `418 = 7^48`.  The finite entry checks are split into a serialized chain
of seven-row blocks.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩
local instance : Fact (Nat.Prime 7537) :=
  ⟨Fermat.OneHundredFiftySeven.FoldCertificates.prime_7537⟩

/-- The package's second-probe root `418 = 7^48` has exact order `157`. -/
theorem root_order : orderOf (418 : ZMod 7537) = 157 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The root `418` is primitive of order `157`. -/
theorem root_isPrimitive : IsPrimitiveRoot (418 : ZMod 7537) 157 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

namespace Internal

/-- The finite-field equality checked for one matrix entry. -/
def entryStatement (j i : Fin 77) : Prop :=
  Fermat.Irregular.CircularUnitResidues.normalizedUnitValue
        (p := 157) (418 : ZMod 7537) j i ^ 48 =
    (418 : ZMod 7537) ^ (matrix j i).val

/-- Split the 77 rows into eleven seven-row blocks.  This keeps each
kernel computation small enough to elaborate without retaining all 5,929
entry proofs at once. -/
def rowAt (block : Fin 11) (row : Fin 7) : Fin 77 :=
  ⟨7 * block.val + row.val, by omega⟩

end Internal

end Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate
