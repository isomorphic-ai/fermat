import Fermat.Irregular.VandiverData
import Fermat.ThirtySeven.ArithmeticCertificate
import Fermat.ThirtySeven.HighBernoulli

/-!
# Vandiver's Bernoulli condition at exponent thirty-seven

The low-index scan proves that `32` is the only irregular index for `37`,
and the compact Faulhaber certificate proves `37 ^ 3 ∤ num(B_1184)`.
Together with Kummer's congruence, these facts discharge every Bernoulli
numerator condition in Vandiver's Case-II criterion.
-/

namespace Fermat.ThirtySeven.VandiverData

open Fermat.Irregular
open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The unique-irregular-index scan reduces all exceptional Vandiver data to
the already certified high Bernoulli number `B_1184`. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 37)
    (hirregular : (37 : ℤ) ∣ (bernoulli j).num) :
    ¬(37 : ℤ) ^ 3 ∣ (bernoulli (j * 37)).num := by
  have hj' : 2 ≤ j ∧ j ≤ 34 ∧ Even j := by
    simpa [indices, and_assoc] using hj
  have hmem :
      j ∈ ArithmeticCertificate.irregularIndices 37 := by
    simp only [ArithmeticCertificate.irregularIndices, Finset.mem_filter,
      Finset.mem_Icc]
    exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
  rw [ArithmeticCertificate.irregularIndices_thirtySeven] at hmem
  have hj32 : j = 32 := by simpa using hmem
  subst j
  simpa using HighBernoulli.bernoulli_1184_numerator_not_dvd_cube

/-- All of Vandiver's Bernoulli cube conditions at `p = 37`, reduced to the
exact Kummer congruence at the regular indices. -/
theorem bernoulliCubeCondition_thirtySeven
    (hKummer : ∀ j ∈ indices 37,
      KummerCongruenceModPrime 37 j (j * 37)) :
    BernoulliCubeCondition 37 := by
  apply bernoulliCubeCondition_of_kummer_of_irregular (by norm_num) hKummer
  exact irregularIndex_numerator_not_dvd_cube

end Fermat.ThirtySeven.VandiverData
