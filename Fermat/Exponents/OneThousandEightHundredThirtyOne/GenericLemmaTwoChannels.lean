import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverDiagonalFiniteIndex1831
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative1831

/-!
# Determinant-free Lemma II adapter at exponent 1831

This is the Lemma-II unit system used by the new Bernoulli-channel ladder.
It keeps the historical diagonal units and the checked derivative theorem,
but obtains finite index from their intrinsic logarithmic Fourier transform
instead of the auxiliary-prime evaluation determinant.

The historical `GenericLemmaTwo` adapter remains available unchanged.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.GenericLemmaTwoChannels

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalFiniteIndex
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits
open Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative
open Fermat.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1831) K (by norm_num)

/-- The diagonal unit system at `1831`, with finite index supplied by the
intrinsic p-side logarithmic transform. -/
def lemmaTwoUnitSystem1831 : LemmaTwoUnitSystem K 1831 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit1831 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily1831 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily1831_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex_qfree hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences1831 hζ)

/-- Regression: the determinant-free unit system still proves Vandiver's
Lemma II at exponent `1831`. -/
theorem vandiverLemmaTwo_oneThousandEightHundredThirtyOne_channels :
    VandiverLemmaTwo K 1831 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem1831 (K := K))

end

end Fermat.OneThousandEightHundredThirtyOne.GenericLemmaTwoChannels
