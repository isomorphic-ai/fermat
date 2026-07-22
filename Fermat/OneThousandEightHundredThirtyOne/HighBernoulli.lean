import Fermat.Irregular.DirectBernoulli
import Fermat.OneThousandEightHundredThirtyOne.PowerSumCertificates

/-!
# The high Bernoulli channel at exponent 1831

The generic direct-Faulhaber theorem turns the modular power sum at the
irregular index `1274` into the numerator nondivisibility condition required
at the lifted index `1274 * 1831 = 2332694`.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.OneThousandEightHundredThirtyOne.PowerSumCertificates

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- The lifted `j = 1274` channel has valuation strictly below three. -/
theorem bernoulli_2332694_numerator_not_dvd_cube :
    ¬(1831 : ℤ) ^ 3 ∣ (bernoulli 2332694).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 1831) (n := 2332694) (c := 1155403615531165) (r := 4975200524)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 1831)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 2332692 ≤ 2332695)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_2332694
  · norm_num
  · exact correctionQuotient_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 1831)
    · decide
    · norm_num

end Fermat.OneThousandEightHundredThirtyOne.HighBernoulli
