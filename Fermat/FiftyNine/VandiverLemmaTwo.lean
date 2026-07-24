import Fermat.FiftyNine.VandiverLemmaTwoAssembly
import Fermat.FiftyNine.VandiverPositiveRelationDerivative

/-!
# Vandiver's Lemma II at exponent 59

This file closes the literal repository interface for Vandiver's second
lemma.  The proof uses the actual twenty-eight diagonal cyclotomic units,
the depth-118 polynomial remainder calculation, and the source's selected
high logarithmic derivatives.
-/

open scoped NumberField

namespace Fermat.FiftyNine.VandiverLemmaTwo

noncomputable section

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `59`: a unit
congruent to a rational `59`th power modulo `(1-zeta)^118` is itself a
`59`th power, unless the historical Bernoulli obstruction occurs. -/
theorem vandiverLemmaTwo_fiftyNine :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 59 := by
  apply
    Fermat.FiftyNine.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences59
  intro zeta hzeta
  exact
    Fermat.FiftyNine.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences59
      hzeta

end

end Fermat.FiftyNine.VandiverLemmaTwo
