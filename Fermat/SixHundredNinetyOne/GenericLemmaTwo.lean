import Fermat.GenericIrregular.LemmaTwo
import Fermat.SixHundredNinetyOne.VandiverPositiveRelationDerivative

/-!
# Exponent 691 as a generic Lemma II unit system

This file packages the 344 diagonal cyclotomic units, their finite-index
calculation, and the completed positive-relation derivative calculation at
`691` behind the prime-generic `LemmaTwoUnitSystem` interface.
-/

open scoped NumberField

namespace Fermat.SixHundredNinetyOne.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixHundredNinetyOne.VandiverDiagonalUnits
open Fermat.SixHundredNinetyOne.VandiverNormalizedRelationDerivative
open Fermat.SixHundredNinetyOne.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K (by norm_num)

/-- The actual diagonal units and derivative computation at `691`, packaged
for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem691 : LemmaTwoUnitSystem K 691 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit691 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily691 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily691_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences691 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `691`. -/
theorem vandiverLemmaTwo_sixHundredNinetyOne_generic :
    VandiverLemmaTwo K 691 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem691 (K := K))

end

end Fermat.SixHundredNinetyOne.GenericLemmaTwo
