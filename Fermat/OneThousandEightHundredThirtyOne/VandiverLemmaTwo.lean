import Fermat.OneThousandEightHundredThirtyOne.VandiverLemmaTwoAssembly1831
import Fermat.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative1831

/-!
# Vandiver's Lemma II at exponent 1831

This file closes the literal repository interface for Vandiver's second
lemma. The proof uses the actual 914 diagonal cyclotomic units, the
depth-3662 polynomial remainder calculation, and the source's selected high
logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `1831`: a unit
congruent to a rational `1831`st power modulo `(1-zeta)^3662` is itself an
`1831`st power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_oneThousandEightHundredThirtyOne :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 1831 := by
  apply
    Fermat.OneThousandEightHundredThirtyOne.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences1831
  intro zeta hzeta
  exact
    Fermat.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences1831
      hzeta

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverLemmaTwo
