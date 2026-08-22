import Fermat.Exponents.SixHundredNinetyOne.VandiverLemmaTwoAssembly
import Fermat.Exponents.SixHundredNinetyOne.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 691

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual 344 diagonal cyclotomic units, the
depth-1382 polynomial remainder calculation, and the source's selected high
logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.SixHundredNinetyOne.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `691`: a unit
congruent to a rational `691`st power modulo `(1-zeta)^1382` is itself a
`691`st power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_sixHundredNinetyOne :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 691 := by
  apply
    Fermat.SixHundredNinetyOne.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences691
  intro zeta hzeta
  exact
    Fermat.SixHundredNinetyOne.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences691
      hzeta

end

end Fermat.SixHundredNinetyOne.VandiverLemmaTwo
