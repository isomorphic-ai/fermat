import Fermat.Irregular.DirectBernoulli
import Fermat.SixHundredNinetyOne.PowerSumCertificates

/-!
# The two high Bernoulli channels at exponent 691

The shared direct-Faulhaber theorem turns the two modular power sums from the
uploaded proof package into numerator nondivisibility statements at
`12 * 691` and `200 * 691`.
-/

namespace Fermat.SixHundredNinetyOne.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.SixHundredNinetyOne.PowerSumCertificates

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

/-- The lifted `12` channel has valuation strictly below three. -/
theorem bernoulli_8292_numerator_not_dvd_cube :
    ¬(691 : ℤ) ^ 3 ∣ (bernoulli 8292).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 691) (n := 8292) (c := 137514526) (r := 137514528)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 8290 ≤ 8293)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_8292
  · norm_num
  · exact correctionQuotients_not_dvd_cube.1
  · apply bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num

/-- The lifted `200` channel has valuation strictly below three. -/
theorem bernoulli_138200_numerator_not_dvd_cube :
    ¬(691 : ℤ) ^ 3 ∣ (bernoulli 138200).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 691) (n := 138200) (c := 636641333300)
      (r := 204839349)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 138198 ≤ 138201)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_138200
  · norm_num
  · exact correctionQuotients_not_dvd_cube.2
  · apply bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num

/-- Exact implication-form low-index scan boundary for the two-channel
package.  It does not assert that either candidate is irregular. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 691, (691 : ℤ) ∣ (bernoulli j).num →
    j = 12 ∨ j = 200

/-- Once the low scan restricts irregularity to the two candidates, the two
direct Faulhaber certificates discharge all exceptional conditions. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 691 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rcases hscan j hj hirregular with rfl | rfl
  · simpa using bernoulli_8292_numerator_not_dvd_cube
  · simpa using bernoulli_138200_numerator_not_dvd_cube

end Fermat.SixHundredNinetyOne.HighBernoulli
