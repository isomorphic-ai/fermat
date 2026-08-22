import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.FiveHundredEightySeven.VandiverPositiveRelationDerivative

/-!
# Exponent 587 as a generic Lemma II unit system

This file is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  The only specialized inputs are the 292
diagonal cyclotomic units, their finite-index calculation, and the completed
positive-relation derivative computation at `587`.
-/

open scoped NumberField

namespace Fermat.FiveHundredEightySeven.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FiveHundredEightySeven.VandiverDiagonalUnits
open Fermat.FiveHundredEightySeven.VandiverNormalizedRelationDerivative
open Fermat.FiveHundredEightySeven.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `587`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem587 : LemmaTwoUnitSystem K 587 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit587 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily587 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily587_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences587 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `587`. -/
theorem vandiverLemmaTwo_fiveHundredEightySeven_generic :
    VandiverLemmaTwo K 587 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem587 (K := K))

end

end Fermat.FiveHundredEightySeven.GenericLemmaTwo
