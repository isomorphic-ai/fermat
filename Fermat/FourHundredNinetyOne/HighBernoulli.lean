import Fermat.Irregular.DirectBernoulli
import Fermat.FourHundredNinetyOne.PowerSumCertificates

/-!
# The three high Bernoulli channels at exponent 491

The shared direct-Faulhaber theorem turns the three modular power sums from
the uploaded proof package into the numerator nondivisibility statements at
`292 * 491`, `336 * 491`, and `338 * 491`.
-/

namespace Fermat.FourHundredNinetyOne.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.FourHundredNinetyOne.PowerSumCertificates

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- The lifted `r = 292` channel has valuation strictly below three. -/
theorem bernoulli_143372_numerator_not_dvd_cube :
    ¬(491 : ℤ) ^ 3 ∣ (bernoulli 143372).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 491) (n := 143372) (c := 1000369145306) (r := 84619431)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 143370 ≤ 143373)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_143372
  · norm_num
  · exact correctionQuotients_not_dvd_cube.1
  · apply bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num

/-- The lifted `r = 336` channel has valuation strictly below three. -/
theorem bernoulli_164976_numerator_not_dvd_cube :
    ¬(491 : ℤ) ^ 3 ∣ (bernoulli 164976).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 491) (n := 164976) (c := 1524156512200) (r := 99325372)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 164974 ≤ 164977)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_164976
  · norm_num
  · exact correctionQuotients_not_dvd_cube.2.1
  · apply bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num

/-- The lifted `r = 338` channel has valuation strictly below three. -/
theorem bernoulli_165958_numerator_not_dvd_cube :
    ¬(491 : ℤ) ^ 3 ∣ (bernoulli 165958).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 491) (n := 165958) (c := 1551535920649) (r := 2651891)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 165956 ≤ 165959)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_165958
  · norm_num
  · exact correctionQuotients_not_dvd_cube.2.2
  · apply bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num

/-- Exact low-index scan boundary for the three-loop package. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 491, (491 : ℤ) ∣ (bernoulli j).num →
    j = 292 ∨ j = 336 ∨ j = 338

/-- Once the low scan identifies the three channels, the three direct
Faulhaber certificates discharge all exceptional Vandiver conditions. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 491 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rcases hscan j hj hirregular with rfl | rfl | rfl
  · simpa using bernoulli_143372_numerator_not_dvd_cube
  · simpa using bernoulli_164976_numerator_not_dvd_cube
  · simpa using bernoulli_165958_numerator_not_dvd_cube

end Fermat.FourHundredNinetyOne.HighBernoulli
