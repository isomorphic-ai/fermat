import Fermat.FourHundredNinetyOne.VandiverLemmaTwoAssembly
import Fermat.FourHundredNinetyOne.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 491

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual 244 diagonal cyclotomic units, the
depth-982 polynomial remainder calculation, and the source's selected high
logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `491`: a unit
congruent to a rational `491`st power modulo `(1-zeta)^982` is itself a
`491`st power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_fourHundredNinetyOne :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 491 := by
  apply
    Fermat.FourHundredNinetyOne.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences491
  intro zeta hzeta
  exact
    Fermat.FourHundredNinetyOne.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences491
      hzeta

end

end Fermat.FourHundredNinetyOne.VandiverLemmaTwo
