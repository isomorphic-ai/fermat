import Fermat.Irregular.DirectBernoulli

/-!
# The high Bernoulli certificate for exponent 59

The sole irregular channel in the supplied package is `j = 44`, so
Vandiver's finite condition needs `59 ^ 3 ∤ num(B_(44*59))`.  The generic
direct-Faulhaber engine reduces this to one power sum in `ZMod (59^4)` and
small denominator checks.  No 5670-digit Bernoulli numerator is embedded in
the Lean proof.
-/

namespace Fermat.FiftyNine.HighBernoulli

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- The compact finite computation replacing the full numerator of
`B_2596`. -/
theorem powerSum_mod_fiftyNine_pow_four :
    (∑ a ∈ Finset.range 59, (a : ZMod (59 ^ 4)) ^ 2596) =
      59 * 62658 := by
  decide

/-- The preceding Bernoulli number `B_2594` is integral at `59`; its
denominator has no factor `59` because `58 ∤ 2594`. -/
theorem pIntegral_bernoulli_2594 : PIntegral 59 (bernoulli 2594) := by
  apply pIntegral_of_denominatorPrimeTo
  apply bernoulli_denominatorPrimeTo
  · decide
  · norm_num

/-- The target Bernoulli denominator is also prime to `59`. -/
theorem denominatorPrimeTo_bernoulli_2596 :
    DenominatorPrimeTo 59 (bernoulli 2596) := by
  apply bernoulli_denominatorPrimeTo
  · decide
  · norm_num

/-- The top binomial coefficient in the Faulhaber decomposition, reduced
to a three-factor computation by symmetry. -/
theorem choose_2597_2594 : (2597).choose 2594 = 59 * 49420910 := by
  rw [← Nat.choose_symm (by norm_num : 2594 ≤ 2597)]
  norm_num [Nat.choose]

/-- The exact numerator condition required in the unique irregular channel:
`59^3` does not divide the reduced numerator of `B_2596`. -/
theorem bernoulli_2596_numerator_not_dvd_cube :
    ¬(59 : ℤ) ^ 3 ∣ (bernoulli 2596).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 59) (n := 2596) (c := 49420910) (r := 62658)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact pIntegral_bernoulli_2594
  · exact choose_2597_2594
  · exact powerSum_mod_fiftyNine_pow_four
  · norm_num
  · norm_num
  · exact denominatorPrimeTo_bernoulli_2596

end Fermat.FiftyNine.HighBernoulli
