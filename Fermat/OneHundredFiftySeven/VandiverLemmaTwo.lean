import Fermat.OneHundredFiftySeven.VandiverLemmaTwoAssembly
import Fermat.OneHundredFiftySeven.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 157

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual thirty-two diagonal cyclotomic units,
the depth-314 polynomial remainder calculation, and the source's selected
high logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `157`: a unit
congruent to a rational `157`th power modulo `(1-zeta)^314` is itself a
`157`th power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_oneHundredFiftySeven :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 157 := by
  apply
    Fermat.OneHundredFiftySeven.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences157
  intro zeta hzeta
  exact
    Fermat.OneHundredFiftySeven.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences157
      hzeta

end

end Fermat.OneHundredFiftySeven.VandiverLemmaTwo
