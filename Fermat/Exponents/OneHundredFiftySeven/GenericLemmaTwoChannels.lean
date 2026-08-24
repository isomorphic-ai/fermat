import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.OneHundredFiftySeven.VandiverDiagonalFiniteIndex157
import Fermat.Exponents.OneHundredFiftySeven.VandiverPositiveRelationDerivative

/-!
# Exponent 157 as a q-free generic Lemma II unit system

This is the parallel channel route. It uses the historical diagonal units
and derivative congruences, but supplies their finite-index field through
the Sinnott/logarithmic-transform proof in `VandiverDiagonalFiniteIndex157`.
The original `GenericLemmaTwo` adapter remains unchanged.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.GenericLemmaTwoChannels

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneHundredFiftySeven.VandiverDiagonalFiniteIndex
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits
open Fermat.OneHundredFiftySeven.VandiverNormalizedRelationDerivative
open Fermat.OneHundredFiftySeven.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- The q-free channel adapter for Vandiver's actual diagonal family. -/
def lemmaTwoUnitSystem157Channels : LemmaTwoUnitSystem K 157 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit157 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily157 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily157_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex_qfree hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences157 hζ)

/-- Regression: the channel route recovers Vandiver's Lemma II at 157
without consuming the auxiliary-prime residue determinant. -/
theorem vandiverLemmaTwo_oneHundredFiftySeven_channels :
    VandiverLemmaTwo K 157 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem157Channels (K := K))

end

end Fermat.OneHundredFiftySeven.GenericLemmaTwoChannels
