import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitEntryBasic

/-!
# Circular-unit phase certificate at exponent 1381

The 690 compressed phase values are checked directly in the split field
`ZMod 38669`.  These are the only finite-field logarithms needed to
reconstruct all `689 × 689` circular-unit residue entries.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (Nat.Prime 38669) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_38669⟩

/-- The 690 kernel-checked discrete logarithms of the relative phases. -/
theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (33927 : ZMod 38669) ^ (symbolPhase r).val := by
  have hr : classRoot r ≠ 0 := classRoot_ne_zero r
  have hzero : classRoot 0 ≠ 0 := classRoot_ne_zero 0
  have hzero1 : 1 - classRoot 0 ≠ 0 := by
    decide +kernel
  unfold phaseValue weight
  field_simp [hr, hzero, hzero1]
  decide +revert

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate
