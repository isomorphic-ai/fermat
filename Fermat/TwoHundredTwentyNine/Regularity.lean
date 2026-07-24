import Fermat.Regular.KummerCriterion
import Fermat.TwoHundredTwentyNine.RegularityCertificate

/-!
# Regularity and Fermat's Last Theorem at exponent 229

The complete modular Voronoi scan is converted into Bernoulli-numerator
regularity by the proved depth-one Voronoi theorem.  The existing formal
Kummer criterion then identifies this numerical condition with cyclotomic
regularity, and the kernel-checked Lamé--Kummer descent proves FLT at `229`.

No class-number value or regular-prime conclusion is assumed.
-/

namespace Fermat.TwoHundredTwentyNine

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Regular.Faulhaber
open Fermat.TwoHundredTwentyNine.RegularityCertificate

/-- The support exponent is prime. -/
theorem prime_229 : Nat.Prime 229 := by
  norm_num

local instance : Fact (Nat.Prime 229) := ⟨prime_229⟩

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk226 : k ≤ 226) (hkeven : Even k) :
    ∃ i : Fin 113, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 113 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- The complete kernel-checked Bernoulli-numerator regularity condition
for exponent `229`. -/
theorem bernoulliNumeratorRegular_229 :
    BernoulliNumeratorRegular 229 := by
  intro k hk
  have hbounds : 2 ≤ k ∧ k ≤ 226 ∧ Even k := by
    simpa [regularIndices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  apply bernoulli_numerator_not_dvd_of_scanResidue_ne_zero
      (p := 229) (a := 6)
  · norm_num
  · omega
  · omega
  · exact hbounds.2.2
  · norm_num
  · rw [← hi]
    exact scanResidue_ne_zero i

/-- Kummer regularity of `229`, derived from the complete modular scan. -/
theorem isRegularPrime_229 : IsRegularPrime 229 :=
  isRegularPrime_of_bernoulliNumeratorRegular
    (by norm_num) bernoulliNumeratorRegular_229

/-- Fermat's Last Theorem for exponent `229`. -/
theorem holdsAt_twoHundredTwentyNine : Fermat.HoldsAt 229 :=
  holdsAt_of_bernoulliNumeratorRegular
    (by norm_num) bernoulliNumeratorRegular_229

end Fermat.TwoHundredTwentyNine
