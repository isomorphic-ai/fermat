import Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Block10

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

/-- Every uploaded entry is the discrete logarithm of the corresponding
forty-eighth-power residue symbol.  The decision procedure ranges over all
5,929 pairs of row and column indices in the Lean kernel. -/
theorem matrix_entry_certificate (j i : Fin 77) :
    Fermat.Irregular.CircularUnitResidues.normalizedUnitValue
          (p := 157) (418 : ZMod 7537) j i ^ 48 =
      (418 : ZMod 7537) ^ (matrix j i).val := by
  change Internal.entryStatement j i
  let block : Fin 11 := ⟨j.val / 7, by omega⟩
  let row : Fin 7 := ⟨j.val % 7, Nat.mod_lt _ (by norm_num)⟩
  have hj : Internal.rowAt block row = j := by
    apply Fin.ext
    change 7 * (j.val / 7) + j.val % 7 = j.val
    exact Nat.div_add_mod j.val 7
  rw [← hj]
  clear_value block
  fin_cases block
  · exact Internal.entryBlock0 row i
  · exact Internal.entryBlock1 row i
  · exact Internal.entryBlock2 row i
  · exact Internal.entryBlock3 row i
  · exact Internal.entryBlock4 row i
  · exact Internal.entryBlock5 row i
  · exact Internal.entryBlock6 row i
  · exact Internal.entryBlock7 row i
  · exact Internal.entryBlock8 row i
  · exact Internal.entryBlock9 row i
  · exact Internal.entryBlock10 row i

end Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate
