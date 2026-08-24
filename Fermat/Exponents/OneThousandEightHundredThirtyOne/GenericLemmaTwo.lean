import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative1831

/-!
# Exponent 1831 as a generic Lemma II unit system

This thin adapter packages the existing 914 diagonal real units, their
finite-index theorem, and the completed positive-relation derivative
calculation behind the prime-generic `LemmaTwoUnitSystem` interface.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits
open Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative
open Fermat.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1831) K (by norm_num)

/-- The existing exponent-1831 diagonal units and derivative computation,
packaged as the generic finite Lemma-II system. -/
def lemmaTwoUnitSystem1831 : LemmaTwoUnitSystem K 1831 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit1831 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily1831 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily1831_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences1831 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `1831`. -/
theorem vandiverLemmaTwo_oneThousandEightHundredThirtyOne_generic :
    VandiverLemmaTwo K 1831 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem1831 (K := K))

end

end Fermat.OneThousandEightHundredThirtyOne.GenericLemmaTwo
