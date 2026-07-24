import Fermat.SixtySeven.VandiverLemmaTwoAssembly
import Fermat.SixtySeven.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 67

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual thirty-two diagonal cyclotomic units,
the depth-134 polynomial remainder calculation, and the source's selected
high logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.SixtySeven.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `67`: a unit
congruent to a rational `67`th power modulo `(1-zeta)^134` is itself a
`67`th power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_sixtySeven :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 67 := by
  apply
    Fermat.SixtySeven.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences67
  intro zeta hzeta
  exact
    Fermat.SixtySeven.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences67
      hzeta

end

end Fermat.SixtySeven.VandiverLemmaTwo
