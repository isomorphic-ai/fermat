import Fermat.Descent.Regular.KummerCriterion
import Fermat.Exponents.OneThousandFiftyOne.RegularityCertificate

/-!
# Regularity and Fermat's Last Theorem at exponent 1051

The complete modular Voronoi scan is converted into Bernoulli-numerator
regularity by the proved depth-one Voronoi theorem.  The formal Kummer
criterion identifies this numerical condition with the explicit historical
cyclotomic class-number condition.

The patched generic `flt_regular` descent no longer consumes that condition.
Thus the scan and class-number results remain standard-axiom certificates,
while the FLT endpoint separately inherits the generic core's temporary
project seams.

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

/-- The historical cyclotomic class-number condition at `1051`, derived
from the complete modular scan. -/
theorem cyclotomicClassNumberRegular_1051 :
    CyclotomicClassNumberRegular 1051 :=
  cyclotomicClassNumberRegular_of_bernoulliNumeratorRegular
    (by norm_num) bernoulliNumeratorRegular_1051

/-- Fermat's Last Theorem for exponent `1051` from the patched generic
descent. -/
theorem holdsAt_oneThousandFiftyOne : Fermat.HoldsAt 1051 :=
  holdsAt_of_bernoulliNumeratorRegular
    (by norm_num) bernoulliNumeratorRegular_1051

end Fermat.OneThousandFiftyOne
