import Fermat.GenericIrregular.LemmaTwo
import Fermat.OneThousandThreeHundredEightyOne.VandiverPositiveRelationDerivative1381

/-!
# Exponent 1381 as a generic Lemma II unit system

This is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  Its specialized inputs are the 689
diagonal cyclotomic units (each built from 690 conjugate factors), their
finite-index calculation, and the completed positive-relation derivative
computation at `1381`.
-/

open scoped NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits
open Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative
open Fermat.OneThousandThreeHundredEightyOne.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `1381`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem1381 : LemmaTwoUnitSystem K 1381 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit1381 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily1381 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily1381_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences1381 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `1381`. -/
theorem vandiverLemmaTwo_oneThousandThreeHundredEightyOne_generic :
    VandiverLemmaTwo K 1381 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem1381 (K := K))

end

end Fermat.OneThousandThreeHundredEightyOne.GenericLemmaTwo
