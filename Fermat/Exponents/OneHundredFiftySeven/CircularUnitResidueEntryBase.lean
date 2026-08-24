import Fermat.Descent.Irregular.CircularUnitResidues
import Fermat.Exponents.OneHundredFiftySeven.FoldCertificates
import Fermat.Exponents.OneHundredFiftySeven.CircularUnitMatrix

/-!
# Independent entry provenance for the selective exponent-157 route

This module rechecks the `q = 7537` residue-symbol entries without importing
the historical matrix inverse or determinant certificate.  The checks are
split into eleven seven-row lemmas solely to keep kernel reduction bounded.
The old exponent route and its entry-certificate files remain untouched.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitResidueEntryBase

open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩

/-- The package root `418 = 7^48` has exact order `157`. -/
theorem root_order : orderOf (418 : ZMod 7537) = 157 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `157`. -/
theorem root_isPrimitive : IsPrimitiveRoot (418 : ZMod 7537) 157 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

namespace Internal

def entryStatement (j i : Fin 77) : Prop :=
  Fermat.Irregular.CircularUnitResidues.normalizedUnitValue
        (p := 157) (418 : ZMod 7537) j i ^ 48 =
    (418 : ZMod 7537) ^ (matrix j i).val

def rowAt (block : Fin 11) (row : Fin 7) : Fin 77 :=
  ⟨7 * block.val + row.val, by omega⟩

private theorem entryBlock0 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 0 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock1 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 1 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock2 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 2 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock3 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 3 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock4 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 4 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock5 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 5 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock6 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 6 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock7 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 7 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock8 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 8 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock9 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 9 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

private theorem entryBlock10 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 10 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

end Internal

/-- Every matrix entry is the discrete logarithm of the corresponding
forty-eighth-power residue symbol. -/
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

end Fermat.OneHundredFiftySeven.CircularUnitResidueEntryBase
