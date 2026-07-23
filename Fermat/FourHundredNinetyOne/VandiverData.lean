import Fermat.Irregular.VandiverData
import Fermat.FourHundredNinetyOne.HighBernoulli
import Fermat.FourHundredNinetyOne.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 491

The compact low scan leaves exactly the three candidate channels
`292`, `336`, and `338`.  The direct Faulhaber certificates at their
`491`-fold lifts handle all three exceptional channels.
-/

namespace Fermat.FourHundredNinetyOne.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- Every irregular low channel has its corresponding cube exclusion. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 491)
    (hirregular : (491 : ℤ) ∣ (bernoulli j).num) :
    ¬(491 : ℤ) ^ 3 ∣ (bernoulli (j * 491)).num := by
  rcases Fermat.FourHundredNinetyOne.IrregularScan.completeIrregularScan
      j hj hirregular with rfl | rfl | rfl
  · simpa using
      HighBernoulli.bernoulli_143372_numerator_not_dvd_cube
  · simpa using
      HighBernoulli.bernoulli_164976_numerator_not_dvd_cube
  · simpa using
      HighBernoulli.bernoulli_165958_numerator_not_dvd_cube

/-- The complete three-channel Bernoulli cube condition. -/
theorem bernoulliCubeCondition_fourHundredNinetyOne :
    BernoulliCubeCondition 491 :=
  Fermat.FourHundredNinetyOne.IrregularScan.bernoulliCubeCondition_491

end Fermat.FourHundredNinetyOne.VandiverData
