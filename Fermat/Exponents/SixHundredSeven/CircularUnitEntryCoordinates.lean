import Fermat.Exponents.SixHundredSeven.CircularUnitEntryBasic

/-!
# One-dimensional real-class coordinates at exponent 607

The source row and column permutations each carry one real cyclic
coordinate. We check those two `302`-point tables separately. The
two-dimensional product relation then follows algebraically from addition
in the cyclic group; no `302 × 302` table is enumerated.
-/

namespace Fermat.SixHundredSeven.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitResidues
open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩

/-- The row permutation records the real class of each embedding exponent,
expressed without choosing its sign. -/
theorem row_exponent_square_certificate (j : Fin 302) :
    ((classExponent (coord (rowPermutation j)) : ZMod 607) ^ 2) =
      (((j.val + 1 : ℕ) : ZMod 607) ^ 2) := by
  decide +revert

/-- The column permutation records the real class of each circular-unit
exponent, expressed without choosing its sign. -/
theorem column_exponent_square_certificate (i : Fin 302) :
    (((3 : ZMod 607) ^ (coord (columnPermutation i)).val) ^ 2) =
      (((i.val + 2 : ℕ) : ZMod 607) ^ 2) := by
  decide +revert

/-- Every original row has the recorded real cyclic coordinate. -/
theorem row_root_relation (j : Fin 302) :
    classRoot (coord (rowPermutation j)) =
        embeddingRoot (p := 607) (14674 : ZMod 20639) j ∨
      classRoot (coord (rowPermutation j)) =
        (embeddingRoot (p := 607) (14674 : ZMod 20639) j)⁻¹ := by
  simpa only [embeddingRoot] using
    classRoot_eq_pow_or_inv_of_sq
      (coord (rowPermutation j)) (j.val + 1)
      (row_exponent_square_certificate j)

/-- Multiplying an embedding coordinate by a unit coordinate gives the sum
of their cyclic exponents, up to the harmless real-class sign. -/
theorem product_root_relation (j i : Fin 302) :
    classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        embeddingRoot (p := 607) (14674 : ZMod 20639) j ^ (i.val + 2) ∨
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        (embeddingRoot (p := 607) (14674 : ZMod 20639) j ^
          (i.val + 2))⁻¹ := by
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  let target : ℕ := (j.val + 1) * (i.val + 2)
  have hsquare :
      ((classExponent (r + s) : ZMod 607) ^ 2) =
        ((target : ℕ) : ZMod 607) ^ 2 := by
    dsimp only [target]
    rw [classExponent_add_sq, row_exponent_square_certificate,
      column_exponent_square_certificate]
    push_cast
    ring
  simpa only [r, s, target, embeddingRoot, pow_mul] using
    classRoot_eq_pow_or_inv_of_sq (r + s) target hsquare

end Fermat.SixHundredSeven.CircularUnitEntryCertificate
