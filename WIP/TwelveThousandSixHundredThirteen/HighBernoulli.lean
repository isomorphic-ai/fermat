import Fermat.Descent.Irregular.DirectBernoulli
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificates

/-!
# The four high Bernoulli channels at exponent 12613

The generic direct-Faulhaber theorem turns the four modular power sums into
the numerator nondivisibility conditions required at the lifted indices
`j * 12613`, for `j ∈ {308, 502, 9400, 10536}`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.HighBernoulli

set_option maxRecDepth 1000000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

local instance : Fact (Nat.Prime 12613) := ⟨by norm_num⟩

/-- The lifted `j = 308` channel has valuation strictly below three. -/
theorem bernoulli_3884804_numerator_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (bernoulli 3884804).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 12613) (n := 3884804)
      (c := 774707375411970) (r := 411878233941)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 3884802 ≤ 3884805)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_3884804
  · norm_num
  · exact correctionQuotient_3884804_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num

/-- The lifted `j = 502` channel has valuation strictly below three. -/
theorem bernoulli_6331726_numerator_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (bernoulli 6331726).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 12613) (n := 6331726)
      (c := 3354259762969275) (r := 1858463317458)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 6331724 ≤ 6331727)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_6331726
  · norm_num
  · exact correctionQuotient_6331726_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num

/-- The lifted `j = 9400` channel has valuation strictly below three. -/
theorem bernoulli_118562200_numerator_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (bernoulli 118562200).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 12613) (n := 118562200)
      (c := 22022625921182665100) (r := 481876852301)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 118562198 ≤ 118562201)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_118562200
  · norm_num
  · exact correctionQuotient_118562200_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num

/-- The lifted `j = 10536` channel has valuation strictly below three. -/
theorem bernoulli_132890568_numerator_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (bernoulli 132890568).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 12613) (n := 132890568)
      (c := 31010789779264765988) (r := 147951625170)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 132890566 ≤ 132890569)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_132890568
  · norm_num
  · exact correctionQuotient_132890568_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 12613)
    · decide
    · norm_num

/-- Exact implication-form low-index scan boundary for the four package
channels. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 12613, (12613 : ℤ) ∣ (bernoulli j).num →
    j ∈ ({308, 502, 9400, 10536} : Finset ℕ)

/-- Once the low scan restricts irregularity to the four package indices,
the four direct Faulhaber certificates discharge the Bernoulli cube
condition. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 12613 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  have hcandidate := hscan j hj hirregular
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcandidate
  rcases hcandidate with rfl | rfl | rfl | rfl
  · simpa using bernoulli_3884804_numerator_not_dvd_cube
  · simpa using bernoulli_6331726_numerator_not_dvd_cube
  · simpa using bernoulli_118562200_numerator_not_dvd_cube
  · simpa using bernoulli_132890568_numerator_not_dvd_cube

end Fermat.TwelveThousandSixHundredThirteen.HighBernoulli
