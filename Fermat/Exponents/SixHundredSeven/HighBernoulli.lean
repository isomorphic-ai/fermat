import Fermat.Descent.Irregular.DirectBernoulli
import Fermat.Exponents.SixHundredSeven.PowerSumCertificates

/-!
# The high Bernoulli channel at exponent 607

The shared direct-Faulhaber theorem turns the modular power sum at the sole
irregular index `592` into the numerator nondivisibility condition required
at the lifted index `592 * 607 = 359344`.
-/

namespace Fermat.SixHundredSeven.HighBernoulli

set_option maxRecDepth 100000

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.VandiverData
open Fermat.SixHundredSeven.PowerSumCertificates

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

/-- The lifted `j = 592` channel has valuation strictly below three. -/
theorem bernoulli_359344_numerator_not_dvd_cube :
    ¬(607 : ℤ) ^ 3 ∣ (bernoulli 359344).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 607) (n := 359344) (c := 12740640219720)
      (r := 188277439)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 607)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 359342 ≤ 359345)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact powerSum_359344
  · norm_num
  · exact correctionQuotient_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 607)
    · decide
    · norm_num

/-- Exact implication-form low-index scan boundary for the sole channel
reported by the paired proof package. -/
def CompleteIrregularScan : Prop :=
  ∀ j ∈ indices 607, (607 : ℤ) ∣ (bernoulli j).num →
    j = 592

/-- Once the low scan restricts irregularity to index `592`, the direct
Faulhaber certificate discharges the finite Bernoulli cube condition. -/
theorem bernoulliCubeCondition_of_completeIrregularScan
    (hscan : CompleteIrregularScan) : BernoulliCubeCondition 607 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rw [hscan j hj hirregular]
  simpa using bernoulli_359344_numerator_not_dvd_cube

end Fermat.SixHundredSeven.HighBernoulli
