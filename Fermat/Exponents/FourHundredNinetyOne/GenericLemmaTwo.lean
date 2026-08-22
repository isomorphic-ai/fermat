import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.FourHundredNinetyOne.VandiverPositiveRelationDerivative

/-!
# Exponent 491 as a generic Lemma II unit system

This file is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  The only specialized inputs are the
244 diagonal cyclotomic units, their finite-index calculation, and the
completed positive-relation derivative computation at `491`.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits
open Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative
open Fermat.FourHundredNinetyOne.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `491`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem491 : LemmaTwoUnitSystem K 491 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit491 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily491 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily491_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences491 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `491`. -/
theorem vandiverLemmaTwo_fourHundredNinetyOne_generic :
    VandiverLemmaTwo K 491 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem491 (K := K))

end

end Fermat.FourHundredNinetyOne.GenericLemmaTwo
