import Fermat.Exponents.SixHundredSeven.VandiverLemmaTwoAssembly607
import Fermat.Exponents.SixHundredSeven.VandiverPositiveRelationDerivative607

/-!
# Vandiver's Lemma II at exponent 607

This file closes the literal repository interface for Vandiver's second
lemma. The proof uses the actual 302 diagonal cyclotomic units, the
depth-1214 polynomial remainder calculation, and the source's selected high
logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.SixHundredSeven.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `607`: a unit
congruent to a rational `607`th power modulo `(1-zeta)^1214` is itself a
`607`th power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_sixHundredSeven :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 607 := by
  apply
    Fermat.SixHundredSeven.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences607
  intro zeta hzeta
  exact
    Fermat.SixHundredSeven.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences607
      hzeta

end

end Fermat.SixHundredSeven.VandiverLemmaTwo
