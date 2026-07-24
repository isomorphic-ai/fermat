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

end Fermat.OneThousandThreeHundredEightyOne.HighBernoulli
