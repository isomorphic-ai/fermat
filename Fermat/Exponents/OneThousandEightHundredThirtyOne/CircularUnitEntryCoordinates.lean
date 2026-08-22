import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitEntryBasic

/-!
# One-dimensional real-class coordinates at exponent 1831

The source row and column permutations each carry one real cyclic
coordinate.  We check those two `914`-point tables separately.  The
two-dimensional product relation then follows algebraically from addition
in the cyclic group; no `914 × 914` table is enumerated.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- The row permutation records the real class of each embedding
exponent, expressed without choosing its sign. -/
theorem row_exponent_square_certificate (j : Fin 914) :
    ((classExponent (coord (rowPermutation j)) : ZMod 1831) ^ 2) =
      (((j.val + 1 : ℕ) : ZMod 1831) ^ 2) := by
  decide +revert

/-- The column permutation records the real class of each circular-unit
exponent, expressed without choosing its sign. -/
theorem column_exponent_square_certificate (i : Fin 914) :
    (((3 : ZMod 1831) ^ (coord (columnPermutation i)).val) ^ 2) =
      (((i.val + 2 : ℕ) : ZMod 1831) ^ 2) := by
  decide +revert

/-- Every original row has the recorded real cyclic coordinate. -/
theorem row_root_relation (j : Fin 914) :
    classRoot (coord (rowPermutation j)) =
        embeddingRoot (p := 1831) (266093 : ZMod 358877) j ∨
      classRoot (coord (rowPermutation j)) =
        (embeddingRoot (p := 1831) (266093 : ZMod 358877) j)⁻¹ := by
  simpa only [embeddingRoot] using
    classRoot_eq_pow_or_inv_of_sq
      (coord (rowPermutation j)) (j.val + 1)
      (row_exponent_square_certificate j)

/-- Multiplying an embedding coordinate by a unit coordinate gives the
sum of their cyclic exponents, up to the harmless real-class sign. -/
theorem product_root_relation (j i : Fin 914) :
    classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        embeddingRoot (p := 1831) (266093 : ZMod 358877) j ^ (i.val + 2) ∨
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        (embeddingRoot (p := 1831) (266093 : ZMod 358877) j ^
          (i.val + 2))⁻¹ := by
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  let target : ℕ := (j.val + 1) * (i.val + 2)
  have hsquare :
      ((classExponent (r + s) : ZMod 1831) ^ 2) =
        ((target : ℕ) : ZMod 1831) ^ 2 := by
    dsimp only [target]
    rw [classExponent_add_sq, row_exponent_square_certificate,
      column_exponent_square_certificate]
    push_cast
    ring
  simpa only [r, s, target, embeddingRoot, pow_mul] using
    classRoot_eq_pow_or_inv_of_sq (r + s) target hsquare

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
