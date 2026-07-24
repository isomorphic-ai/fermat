import Fermat.FiveHundredEightySeven.VandiverLemmaTwoAssembly
import Fermat.FiveHundredEightySeven.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 587

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual 292 diagonal cyclotomic units, the
depth-1174 polynomial remainder calculation, and the source's selected high
logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.FiveHundredEightySeven.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `587`: a unit
congruent to a rational `587`th power modulo `(1-zeta)^1174` is itself a
`587`th power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_fiveHundredEightySeven :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 587 := by
  apply
    Fermat.FiveHundredEightySeven.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences587
  intro zeta hzeta
  exact
    Fermat.FiveHundredEightySeven.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences587
      hzeta

end

end Fermat.FiveHundredEightySeven.VandiverLemmaTwo
