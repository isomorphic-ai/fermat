import Fermat.Exponents.SixHundredSeven.CircularUnitEntryCoordinates
import Fermat.Exponents.SixHundredSeven.CircularUnitPhaseCertificate

/-!
# Complete finite-field entry provenance at exponent 607

The structural weight identity, 303 checked phase values, and two checked
one-dimensional real-class coordinate tables reconstruct every one of the
source `302 × 302` residue-symbol entries without storing or enumerating a
dense matrix.
-/

namespace Fermat.SixHundredSeven.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitResidues
open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩

/-- Every compressed entry is the discrete logarithm of the corresponding
thirty-fourth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 302) :
    normalizedUnitValue (p := 607) (14674 : ZMod 20639) j i ^ 34 =
      (14674 : ZMod 20639) ^ (matrix j i).val := by
  let x : ZMod 20639 :=
    embeddingRoot (p := 607) (14674 : ZMod 20639) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 607) (q := 20639)
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

end Fermat.SixHundredSeven.CircularUnitEntryCertificate
