import Fermat.Irregular.DirectBernoulli
import Fermat.SixtySeven.FirstCase

/-!
# The lifted Bernoulli certificate at exponent 67

The unique exceptional channel in the uploaded package is `j = 58`, so
Vandiver's finite condition asks for `67³ ∤ num(B_(58·67))`.  The generic
Faulhaber engine reduces this to a 67-term power sum in `ZMod (67⁴)`.

The checked residue is

`sum a^3886 = 67 * 184049 = 67³ * 41 (mod 67⁴)`,

which records the package's sharp quotient `41` while proving the weaker
nondivisibility needed by the historical criterion.
-/

namespace Fermat.SixtySeven.HighBernoulli

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩

theorem choose_3887_3884 : (3887).choose 3884 = 67 * 145976285 := by
  rw [← Nat.choose_symm (by norm_num : 3884 ≤ 3887)]
  norm_num [Nat.choose]

/-- The sole large finite computation: only 67 modular powers are evaluated. -/
theorem powerSum_mod_sixtySeven_pow_four :
    (∑ a ∈ Finset.range 67, (a : ZMod (67 ^ 4)) ^ 3886) =
      67 * 184049 := by
  decide

theorem previousBernoulli_pIntegral :
    PIntegral 67 (bernoulli 3884) := by
  apply pIntegral_of_denominatorPrimeTo
  apply bernoulli_denominatorPrimeTo (p := 67)
  · decide
  · norm_num

theorem targetBernoulli_denominatorPrimeTo :
    DenominatorPrimeTo 67 (bernoulli 3886) := by
  apply bernoulli_denominatorPrimeTo (p := 67)
  · decide
  · norm_num

/-- The lifted Bernoulli numerator has fewer than three factors of `67`.
This is the exact finite input required at irregular index `58`. -/
theorem bernoulli_3886_numerator_not_dvd_cube :
    ¬(67 : ℤ) ^ 3 ∣ (bernoulli 3886).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 67) (n := 3886) (c := 145976285) (r := 184049)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · exact previousBernoulli_pIntegral
  · exact choose_3887_3884
  · exact powerSum_mod_sixtySeven_pow_four
  · norm_num
  · norm_num
  · exact targetBernoulli_denominatorPrimeTo

/-- The residue is visibly `67² * 41`, so it has exact valuation two. -/
theorem certifiedResidue_eq_sixtySeven_sq_mul_41 :
    184049 = 67 ^ 2 * 41 := by
  norm_num

end Fermat.SixtySeven.HighBernoulli
