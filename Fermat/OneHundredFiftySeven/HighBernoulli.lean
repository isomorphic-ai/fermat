import Fermat.Irregular.DirectBernoulli
import Fermat.OneHundredFiftySeven.PowerSumCertificates

/-!
# The two high Bernoulli channels at exponent 157

The shared direct-Faulhaber endpoint reduces each high Bernoulli numerator
condition to the exponent-specific power sum already checked in
`FoldCertificates`.  No 26,829- or 51,903-digit numerator is embedded in the
Lean source.
-/

namespace Fermat.OneHundredFiftySeven.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.OneHundredFiftySeven.PowerSumCertificates

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

/-- The lifted `r = 62` channel has valuation strictly below three. -/
theorem bernoulli_9734_numerator_not_dvd_cube :
    ¬(157 : ℤ) ^ 3 ∣ (bernoulli 9734).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 157) (n := 9734) (c := 979091135) (r := 73947)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 9732 ≤ 9735)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_9734
  · norm_num
  · exact correctionQuotients_not_dvd_cube.1
  · apply bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num

/-- The lifted `r = 110` channel has valuation strictly below three. -/
theorem bernoulli_17270_numerator_not_dvd_cube :
    ¬(157 : ℤ) ^ 3 ∣ (bernoulli 17270).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 157) (n := 17270) (c := 5467969815) (r := 394384)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 17268 ≤ 17271)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_17270
  · norm_num
  · exact correctionQuotients_not_dvd_cube.2
  · apply bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num

/-- Exact remaining low-index scan boundary.  The offline verifier proves
this implication by a complete scan through index 154; a future compact
Lean scan certificate can discharge it without changing the high proof. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 157, (157 : ℤ) ∣ (bernoulli j).num →
    j = 62 ∨ j = 110

/-- Once the low scan identifies the two channels, Kummer's proved
congruence discharges all regular indices and the two direct-Faulhaber
certificates discharge the exceptional indices. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 157 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rcases hscan j hj hirregular with rfl | rfl
  · simpa using bernoulli_9734_numerator_not_dvd_cube
  · simpa using bernoulli_17270_numerator_not_dvd_cube

end Fermat.OneHundredFiftySeven.HighBernoulli
