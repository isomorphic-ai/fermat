import Fermat.Irregular.DirectBernoulli
import Fermat.OneThousandThreeHundredEightyOne.PowerSumCertificates

/-!
# The high Bernoulli channel at exponent 1381

The generic direct-Faulhaber theorem turns the modular power sum at the
irregular index `266` into the numerator nondivisibility condition required
at the lifted index `266 * 1381 = 367346`.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.OneThousandThreeHundredEightyOne.PowerSumCertificates

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- The lifted `j = 266` channel has valuation strictly below three. -/
theorem bernoulli_367346_numerator_not_dvd_cube :
    ¬(1381 : ℤ) ^ 3 ∣ (bernoulli 367346).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 1381) (n := 367346) (c := 5982476711365) (r := 1069917321)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 367344 ≤ 367347)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_367346
  · norm_num
  · exact correctionQuotient_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num

/-- Exact implication-form low-index scan boundary for the single channel
reported by the paired four-digit proof package. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 1381, (1381 : ℤ) ∣ (bernoulli j).num →
    j = 266

/-- Once the low scan restricts irregularity to index `266`, the direct
Faulhaber certificate discharges the finite Bernoulli cube condition. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 1381 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rw [hscan j hj hirregular]
  simpa using bernoulli_367346_numerator_not_dvd_cube

end Fermat.OneThousandThreeHundredEightyOne.HighBernoulli
