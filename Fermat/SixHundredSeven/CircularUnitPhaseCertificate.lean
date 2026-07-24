import Fermat.SixHundredSeven.CircularUnitEntryBasic

/-!
# Circular-unit phase certificate at exponent 607

The 303 compressed phase values are checked directly in the split field
`ZMod 20639`. These are the only finite-field logarithms needed to
reconstruct all `302 × 302` circular-unit residue entries.
-/

namespace Fermat.SixHundredSeven.CircularUnitEntryCertificate

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩

/-- The 303 kernel-checked discrete logarithms of the relative phases. -/
theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (14674 : ZMod 20639) ^ (symbolPhase r).val := by
  have hr : classRoot r ≠ 0 := classRoot_ne_zero r
  have hzero : classRoot 0 ≠ 0 := classRoot_ne_zero 0
  have hzero1 : 1 - classRoot 0 ≠ 0 := by
    decide +kernel
  unfold phaseValue weight
  field_simp [hr, hzero, hzero1]
  decide +revert

end Fermat.SixHundredSeven.CircularUnitEntryCertificate
