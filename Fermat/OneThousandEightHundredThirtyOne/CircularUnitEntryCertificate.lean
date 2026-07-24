import Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCoordinates
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitPhaseCertificate

/-!
# Complete finite-field entry provenance at exponent 1831

The structural weight identity, 915 checked phase values, and two checked
one-dimensional real-class coordinate tables reconstruct every one of the
source `914 × 914` residue-symbol entries without storing or enumerating
the dense matrix.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- Every compressed entry is the discrete logarithm of the corresponding
one-hundred-ninety-sixth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 914) :
    normalizedUnitValue (p := 1831) (266093 : ZMod 358877) j i ^ 196 =
      (266093 : ZMod 358877) ^ (matrix j i).val := by
  let x : ZMod 358877 :=
    embeddingRoot (p := 1831) (266093 : ZMod 358877) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 1831) (q := 358877)
      (by norm_num) root_isPrimitive j).ne_zero (by norm_num)
  have hrowWeight : weight x = weight (classRoot r) := by
    rcases row_root_relation j with h | h
    · exact congrArg weight h.symm
    · calc
        weight x = weight x⁻¹ := (weight_inv x hx0).symm
        _ = weight (classRoot r) := congrArg weight h.symm
  have hprodWeight : weight (x ^ a) = weight (classRoot (r + s)) := by
    rcases product_root_relation j i with h | h
    · exact congrArg weight h.symm
    · calc
        weight (x ^ a) = weight (x ^ a)⁻¹ :=
          (weight_inv (x ^ a) (pow_ne_zero _ hx0)).symm
        _ = weight (classRoot (r + s)) := congrArg weight h.symm
  rw [normalized_pow_eq_weight_ratio]
  change weight (x ^ a) / weight x = _
  rw [hprodWeight, hrowWeight, weight_ratio_eq_phase_ratio,
    phase_value_certificate, phase_value_certificate]
  rw [← root_pow_sub_val]
  rfl

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
