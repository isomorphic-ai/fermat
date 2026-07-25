import Fermat.GenericIrregular.LemmaTwo
import Fermat.FiftyNine.VandiverPositiveRelationDerivative

/-!
# Exponent 59 as a generic Lemma II unit system

This file is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  The only specialized inputs are the
twenty-eight diagonal cyclotomic units, their finite-index calculation, and
the completed positive-relation derivative computation at `59`.
-/

open scoped NumberField

namespace Fermat.FiftyNine.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FiftyNine.VandiverDiagonalUnits
open Fermat.FiftyNine.VandiverNormalizedRelationDerivative
open Fermat.FiftyNine.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `59`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem59 : LemmaTwoUnitSystem K 59 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit59 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily59 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily59_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences59 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `59`. -/
theorem vandiverLemmaTwo_fiftyNine_generic :
    VandiverLemmaTwo K 59 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem59 (K := K))

end

end Fermat.FiftyNine.GenericLemmaTwo
