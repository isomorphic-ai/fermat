import Fermat.Irregular.VandiverData
import Fermat.OneThousandThreeHundredEightyOne.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 1381

The compact low scan leaves only index `266`.  The direct Faulhaber
certificate at `266 * 1381 = 367346` excludes a third factor of `1381` from
the lifted Bernoulli numerator.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- Every irregular low channel has its corresponding cube exclusion. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 1381)
    (hirregular : (1381 : ℤ) ∣ (bernoulli j).num) :
    ¬(1381 : ℤ) ^ 3 ∣ (bernoulli (j * 1381)).num := by
  rw [Fermat.OneThousandThreeHundredEightyOne.IrregularScan.completeIrregularScan
    j hj hirregular]
  simpa using
    Fermat.OneThousandThreeHundredEightyOne.HighBernoulli.bernoulli_367346_numerator_not_dvd_cube

/-- The complete one-channel Bernoulli cube condition. -/
theorem bernoulliCubeCondition_oneThousandThreeHundredEightyOne :
    BernoulliCubeCondition 1381 :=
  Fermat.OneThousandThreeHundredEightyOne.IrregularScan.bernoulliCubeCondition_1381

end Fermat.OneThousandThreeHundredEightyOne.VandiverData
