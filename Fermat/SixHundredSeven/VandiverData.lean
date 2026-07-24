import Fermat.Irregular.VandiverData
import Fermat.SixHundredSeven.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 607

The compact low scan leaves only index `592`. The direct Faulhaber
certificate at `592 * 607 = 359344` excludes a third factor of `607` from
the lifted Bernoulli numerator.

This module exposes the kernel-checked finite arithmetic through the common
`BernoulliCubeCondition` API. It does not by itself assert the global
second-case descent.
-/

namespace Fermat.SixHundredSeven.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

/-- Every irregular low channel has its corresponding cube exclusion. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 607)
    (hirregular : (607 : ℤ) ∣ (bernoulli j).num) :
    ¬(607 : ℤ) ^ 3 ∣ (bernoulli (j * 607)).num := by
  rw [Fermat.SixHundredSeven.IrregularScan.completeIrregularScan
    j hj hirregular]
  simpa using
    Fermat.SixHundredSeven.HighBernoulli.bernoulli_359344_numerator_not_dvd_cube

/-- The complete one-channel Bernoulli cube condition. -/
theorem bernoulliCubeCondition_sixHundredSeven :
    BernoulliCubeCondition 607 :=
  Fermat.SixHundredSeven.IrregularScan.bernoulliCubeCondition_607

/-- Numeric-name alias for campaign consumers. -/
theorem bernoulliCubeCondition_607 :
    BernoulliCubeCondition 607 :=
  bernoulliCubeCondition_sixHundredSeven

end Fermat.SixHundredSeven.VandiverData
