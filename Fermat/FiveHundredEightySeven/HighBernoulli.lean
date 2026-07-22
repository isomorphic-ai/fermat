import Fermat.Irregular.DirectBernoulli
import Fermat.FiveHundredEightySeven.PowerSumCertificates

/-!
# The two high Bernoulli channels at exponent 587

The generic direct-Faulhaber theorem turns the two modular power sums into
the exact numerator nondivisibility conditions required at the lifted
irregular indices `90 * 587` and `92 * 587`.
-/

namespace Fermat.FiveHundredEightySeven.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.FiveHundredEightySeven.PowerSumCertificates

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

/-- The lifted `r = 90` channel has valuation strictly below three. -/
theorem bernoulli_52830_numerator_not_dvd_cube :
    ¬(587 : ℤ) ^ 3 ∣ (bernoulli 52830).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 587) (n := 52830) (c := 41865133485) (r := 171595362)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 52828 ≤ 52831)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_52830
  · norm_num
  · exact correctionQuotients_not_dvd_cube.1
  · apply bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num

/-- The lifted `r = 92` channel has valuation strictly below three. -/
theorem bernoulli_54004_numerator_not_dvd_cube :
    ¬(587 : ℤ) ^ 3 ∣ (bernoulli 54004).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 587) (n := 54004) (c := 44718624230) (r := 83385698)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 54002 ≤ 54005)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_54004
  · norm_num
  · exact correctionQuotients_not_dvd_cube.2
  · apply bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num

/-- Exact low-index scan boundary. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 587, (587 : ℤ) ∣ (bernoulli j).num →
    j = 90 ∨ j = 92

/-- Once the low scan identifies the two channels, the two high
certificates discharge every exceptional Vandiver condition. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 587 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rcases hscan j hj hirregular with rfl | rfl
  · simpa using bernoulli_52830_numerator_not_dvd_cube
  · simpa using bernoulli_54004_numerator_not_dvd_cube

end Fermat.FiveHundredEightySeven.HighBernoulli
