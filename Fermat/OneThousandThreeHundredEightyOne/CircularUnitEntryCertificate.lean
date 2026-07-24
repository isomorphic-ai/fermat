import Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCoordinates
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitPhaseCertificate

/-!
# Complete finite-field entry provenance at exponent 1381

The structural weight identity, 690 checked phase values, and two checked
one-dimensional real-class coordinate tables reconstruct every one of the
source `689 × 689` residue-symbol entries without storing or enumerating
the dense matrix.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (Nat.Prime 38669) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_38669⟩

/-- Every compressed entry is the discrete logarithm of the corresponding
twenty-eighth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 689) :
    normalizedUnitValue (p := 1381) (33927 : ZMod 38669) j i ^ 28 =
      (33927 : ZMod 38669) ^ (matrix j i).val := by
  let x : ZMod 38669 :=
    embeddingRoot (p := 1381) (33927 : ZMod 38669) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 1381) (q := 38669)
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

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate
