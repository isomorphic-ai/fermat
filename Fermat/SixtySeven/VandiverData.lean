import Fermat.Irregular.VandiverData
import Fermat.SixtySeven.ArithmeticCertificate
import Fermat.SixtySeven.HighBernoulli

/-!
# Vandiver's finite Bernoulli condition at exponent 67

The low recurrence scan proves that `58` is the sole irregular index.  The
generic Faulhaber certificate at `3886 = 58 * 67` handles that exceptional
channel, while the formal Voronoi--Kummer theorem discharges every regular
index.  Thus all Bernoulli numerator conditions in Vandiver's criterion are
unconditional here; the remaining gap is global singular-primary descent.
-/

namespace Fermat.SixtySeven.VandiverData

open Fermat.Irregular
open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩

theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 67)
    (hirregular : (67 : ℤ) ∣ (bernoulli j).num) :
    ¬(67 : ℤ) ^ 3 ∣ (bernoulli (j * 67)).num := by
  have hj' : 2 ≤ j ∧ j ≤ 64 ∧ Even j := by
    simpa [indices, and_assoc] using hj
  have hmem :
      j ∈ Fermat.SixtySeven.ArithmeticCertificate.irregularIndices 67 := by
    simp only [Fermat.SixtySeven.ArithmeticCertificate.irregularIndices,
      Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
  rw [Fermat.SixtySeven.ArithmeticCertificate.irregularIndices_sixtySeven] at hmem
  have hj58 : j = 58 := by simpa using hmem
  subst j
  simpa using
    Fermat.SixtySeven.HighBernoulli.bernoulli_3886_numerator_not_dvd_cube

/-- Every indexed Bernoulli numerator in Vandiver's finite condition is
checked at exponent `67`. -/
theorem bernoulliCubeCondition_sixtySeven : BernoulliCubeCondition 67 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  exact irregularIndex_numerator_not_dvd_cube

end Fermat.SixtySeven.VandiverData
