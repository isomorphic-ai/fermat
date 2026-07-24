import Fermat.Regular.KummerCriterion
import Fermat.OneThousandFiftyOne.RegularityCertificate

/-!
# Regularity and Fermat's Last Theorem at exponent 1051

The complete modular Voronoi scan is converted into Bernoulli-numerator
regularity by the proved depth-one Voronoi theorem.  The formal Kummer
criterion then identifies this numerical condition with cyclotomic
regularity, and the kernel-checked Lamé--Kummer descent proves FLT at
`1051`.

This is the regular anchor used by the exponent-12613 package through
`12613 = 12 * 1051 + 1`.  No class-number value or regular-prime
conclusion is assumed.
-/

namespace Fermat.OneThousandFiftyOne

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Regular.Faulhaber
open Fermat.OneThousandFiftyOne.RegularityCertificate

/-- The support exponent is prime. -/
theorem prime_1051 : Nat.Prime 1051 := by
  norm_num

local instance : Fact (Nat.Prime 1051) := ⟨prime_1051⟩

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk1048 : k ≤ 1048) (hkeven : Even k) :
    ∃ i : Fin 524, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 524 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- The complete kernel-checked Bernoulli-numerator regularity condition
for exponent `1051`. -/
theorem bernoulliNumeratorRegular_1051 :
    BernoulliNumeratorRegular 1051 := by
  intro k hk
  have hbounds : 2 ≤ k ∧ k ≤ 1048 ∧ Even k := by
    simpa [regularIndices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  apply bernoulli_numerator_not_dvd_of_scanResidue_ne_zero
      (p := 1051) (a := 7)
  · norm_num
  · omega
  · omega
  · exact hbounds.2.2
  · norm_num
  · rw [← hi]
    exact scanResidue_ne_zero i

/-- Kummer regularity of `1051`, derived from the complete modular scan. -/
theorem isRegularPrime_1051 : IsRegularPrime 1051 :=
  isRegularPrime_of_bernoulliNumeratorRegular
    (by norm_num) bernoulliNumeratorRegular_1051

/-- Fermat's Last Theorem for exponent `1051`. -/
theorem holdsAt_oneThousandFiftyOne : Fermat.HoldsAt 1051 :=
  holdsAt_of_bernoulliNumeratorRegular
    (by norm_num) bernoulliNumeratorRegular_1051

end Fermat.OneThousandFiftyOne
