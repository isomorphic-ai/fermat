import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.OneHundredFiftySeven.VandiverPositiveRelationDerivative

/-!
# Exponent 157 as a generic Lemma II unit system

This file is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  The only specialized inputs are the
seventy-seven diagonal cyclotomic units (each built from seventy-eight
conjugate factors), their finite-index calculation, and the completed
positive-relation derivative computation at `157`.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits
open Fermat.OneHundredFiftySeven.VandiverNormalizedRelationDerivative
open Fermat.OneHundredFiftySeven.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `157`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem157 : LemmaTwoUnitSystem K 157 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit157 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily157 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily157_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences157 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `157`. -/
theorem vandiverLemmaTwo_oneHundredFiftySeven_generic :
    VandiverLemmaTwo K 157 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem157 (K := K))

end

end Fermat.OneHundredFiftySeven.GenericLemmaTwo
