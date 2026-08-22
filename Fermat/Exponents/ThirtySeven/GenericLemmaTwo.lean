import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.ThirtySeven.VandiverPositiveRelationDerivative

/-!
# Exponent 37 as a generic Lemma II unit system

This file is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  The only specialized inputs are the
seventeen diagonal cyclotomic units, their finite-index calculation, and
the completed positive-relation derivative computation at `37`.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.ThirtySeven.VandiverDiagonalUnits
open Fermat.ThirtySeven.VandiverNormalizedRelationDerivative
open Fermat.ThirtySeven.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `37`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem37 : LemmaTwoUnitSystem K 37 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit37 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily37 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily37_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences37 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `37`. -/
theorem vandiverLemmaTwo_thirtySeven_generic :
    VandiverLemmaTwo K 37 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem37 (K := K))

end

end Fermat.ThirtySeven.GenericLemmaTwo
