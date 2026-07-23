import Fermat.ThirtySeven.VandiverLemmaTwoAssembly
import Fermat.ThirtySeven.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 37

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual seventeen diagonal cyclotomic units,
the depth-74 polynomial remainder calculation, and the source's selected
high logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `37`: a unit
congruent to a rational `37`th power modulo `(1-zeta)^74` is itself a
`37`th power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_thirtySeven :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 37 := by
  apply
    Fermat.ThirtySeven.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences37
  intro zeta hzeta
  exact
    Fermat.ThirtySeven.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences37
      hzeta

end

end Fermat.ThirtySeven.VandiverLemmaTwo
