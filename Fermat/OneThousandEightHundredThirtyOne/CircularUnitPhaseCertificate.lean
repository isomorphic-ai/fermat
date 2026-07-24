import Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryBasic

/-!
# Circular-unit phase certificate at exponent 1831

The 915 compressed phase values are checked directly in the split field
`ZMod 358877`.  These are the only finite-field logarithms needed to
reconstruct all `914 × 914` circular-unit residue entries.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- The 915 kernel-checked discrete logarithms of the relative phases. -/
theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (266093 : ZMod 358877) ^ (symbolPhase r).val := by
  have hr : classRoot r ≠ 0 := classRoot_ne_zero r
  have hzero : classRoot 0 ≠ 0 := classRoot_ne_zero 0
  have hzero1 : 1 - classRoot 0 ≠ 0 := by
    decide +kernel
  unfold phaseValue weight
  field_simp [hr, hzero, hzero1]
  decide +revert

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
