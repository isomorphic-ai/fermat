import Fermat.GenericIrregular.LemmaTwo
import Fermat.SixHundredSeven.VandiverPositiveRelationDerivative607

/-!
# Exponent 607 as a generic Lemma II unit system

This file packages the 302 diagonal cyclotomic units, their finite-index
calculation, and the completed positive-relation derivative calculation at
`607` behind the prime-generic `LemmaTwoUnitSystem` interface.
-/

open scoped NumberField

namespace Fermat.SixHundredSeven.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixHundredSeven.VandiverDiagonalUnits
open Fermat.SixHundredSeven.VandiverNormalizedRelationDerivative
open Fermat.SixHundredSeven.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 607) K (by norm_num)

/-- The actual diagonal units and derivative computation at `607`, packaged
for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem607 : LemmaTwoUnitSystem K 607 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit607 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily607 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily607_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences607 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `607`. -/
theorem vandiverLemmaTwo_sixHundredSeven_generic :
    VandiverLemmaTwo K 607 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem607 (K := K))

end

end Fermat.SixHundredSeven.GenericLemmaTwo
