import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.FourHundredNinetyOne.VandiverDiagonalFiniteIndex491
import Fermat.Exponents.FourHundredNinetyOne.VandiverPositiveRelationDerivative

/-!
# Determinant-free Lemma II adapter at exponent 491

This is the Lemma-II unit system used by the new Bernoulli-channel ladder.
It keeps the historical diagonal units and the checked derivative theorem,
but obtains finite index from their intrinsic logarithmic Fourier transform
instead of the auxiliary-prime evaluation determinant.

The historical `GenericLemmaTwo` adapter remains available unchanged.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.GenericLemmaTwoChannels

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FourHundredNinetyOne.VandiverDiagonalFiniteIndex
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits
open Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative
open Fermat.FourHundredNinetyOne.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- The diagonal unit system at `491`, with finite index supplied by the
intrinsic p-side logarithmic transform. -/
def lemmaTwoUnitSystem491 : LemmaTwoUnitSystem K 491 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit491 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily491 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily491_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex_qfree hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences491 hζ)

/-- Regression: the determinant-free unit system still proves Vandiver's
Lemma II at exponent `491`. -/
theorem vandiverLemmaTwo_fourHundredNinetyOne_channels :
    VandiverLemmaTwo K 491 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem491 (K := K))

end

end Fermat.FourHundredNinetyOne.GenericLemmaTwoChannels
