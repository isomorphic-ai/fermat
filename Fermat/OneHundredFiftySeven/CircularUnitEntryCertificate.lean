import Fermat.Irregular.CircularUnitResidues
import Fermat.OneHundredFiftySeven.FoldCertificates
import Fermat.OneHundredFiftySeven.CircularUnitCertificate

/-!
# Entry provenance for the exponent-157 circular-unit matrix

At the successful second probe `q = 7537`, the package uses the order-157
root `418 = 7^48`.  This file recomputes every matrix entry from the
canonical normalized circular unit and its forty-eighth-power residue
symbol.
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

/-- Every uploaded entry is the discrete logarithm of the corresponding
forty-eighth-power residue symbol.  The decision procedure ranges over all
5,929 pairs of row and column indices in the Lean kernel. -/
theorem matrix_entry_certificate (j i : Fin 77) :
    Fermat.Irregular.CircularUnitResidues.normalizedUnitValue
          (p := 157) (418 : ZMod 7537) j i ^ 48 =
      (418 : ZMod 7537) ^ (matrix j i).val := by
  decide +revert

end Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate
