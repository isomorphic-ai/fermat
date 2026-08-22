import Fermat.Descent.Irregular.VandiverData
import Fermat.Exponents.OneThousandEightHundredThirtyOne.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 1831

The compact low scan leaves only index `1274`. The direct Faulhaber
certificate at `1274 * 1831 = 2332694` excludes a third factor of `1831`
from the lifted Bernoulli numerator.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- Every irregular low channel has its corresponding cube exclusion. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 1831)
    (hirregular : (1831 : ℤ) ∣ (bernoulli j).num) :
    ¬(1831 : ℤ) ^ 3 ∣ (bernoulli (j * 1831)).num := by
  rw [Fermat.OneThousandEightHundredThirtyOne.IrregularScan.completeIrregularScan
    j hj hirregular]
  simpa using
    Fermat.OneThousandEightHundredThirtyOne.HighBernoulli.bernoulli_2332694_numerator_not_dvd_cube

/-- The complete one-channel Bernoulli cube condition. -/
theorem bernoulliCubeCondition_oneThousandEightHundredThirtyOne :
    BernoulliCubeCondition 1831 :=
  Fermat.OneThousandEightHundredThirtyOne.IrregularScan.bernoulliCubeCondition_1831

end Fermat.OneThousandEightHundredThirtyOne.VandiverData
