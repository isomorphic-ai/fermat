import Fermat.Irregular.VandiverData
import Fermat.SixHundredNinetyOne.HighBernoulli
import Fermat.SixHundredNinetyOne.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 691

The compact implication-form low scan leaves only the candidate channels
`12` and `200`.  The direct Faulhaber certificates at their `691`-fold lifts
handle both exceptional channels without asserting that either low candidate
is in fact irregular.
-/

namespace Fermat.SixHundredNinetyOne.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

/-- Every irregular low channel has its corresponding cube exclusion. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 691)
    (hirregular : (691 : ℤ) ∣ (bernoulli j).num) :
    ¬(691 : ℤ) ^ 3 ∣ (bernoulli (j * 691)).num := by
  rcases Fermat.SixHundredNinetyOne.IrregularScan.completeIrregularScan
      j hj hirregular with rfl | rfl
  · simpa using
      HighBernoulli.bernoulli_8292_numerator_not_dvd_cube
  · simpa using
      HighBernoulli.bernoulli_138200_numerator_not_dvd_cube

/-- The complete two-candidate Bernoulli cube condition. -/
theorem bernoulliCubeCondition_sixHundredNinetyOne :
    BernoulliCubeCondition 691 :=
  Fermat.SixHundredNinetyOne.IrregularScan.bernoulliCubeCondition_691

end Fermat.SixHundredNinetyOne.VandiverData
