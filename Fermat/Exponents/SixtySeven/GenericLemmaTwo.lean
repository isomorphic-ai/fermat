import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Exponents.SixtySeven.VandiverPositiveRelationDerivative

/-!
# Exponent 67 as a generic Lemma II unit system

This file is the thin exponent-specific adapter for the prime-generic
`LemmaTwoUnitSystem` interface.  The only specialized inputs are the
thirty-two diagonal cyclotomic units, their finite-index calculation, and
the completed positive-relation derivative computation at `67`.
-/

open scoped NumberField

namespace Fermat.SixtySeven.GenericLemmaTwo

noncomputable section

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixtySeven.VandiverDiagonalUnits
open Fermat.SixtySeven.VandiverNormalizedRelationDerivative
open Fermat.SixtySeven.VandiverPositiveRelationDerivative

local instance : Fact (Nat.Prime 67) :=
  ⟨Fermat.SixtySeven.prime_67⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

/-- The actual diagonal units and finite derivative computation at `67`,
packaged for the prime-generic Lemma II assembly. -/
def lemmaTwoUnitSystem67 : LemmaTwoUnitSystem K 67 where
  ambientFamily := fun hζ ↦ diagonalVandiverUnit67 hζ
  realFamily := fun hζ ↦ diagonalVandiverUnitFamily67 hζ
  realFamily_coe := by
    intro ζ hζ i
    exact diagonalVandiverUnitFamily67_coe hζ i
  finiteIndex_realFamily := by
    intro ζ hζ
    exact real_closure_finiteIndex hζ
  relationCubeCongruences := by
    intro ζ hζ u hdeep
    exact primitiveRelationCubeCongruences_of_positive
      hζ u hdeep (positiveRelationDerivativeCongruences67 hζ)

/-- Regression: the generic finite-system theorem recovers Vandiver's
Lemma II at exponent `67`. -/
theorem vandiverLemmaTwo_sixtySeven_generic :
    VandiverLemmaTwo K 67 :=
  vandiverLemmaTwo_of_unitSystem (by norm_num)
    (lemmaTwoUnitSystem67 (K := K))

end

end Fermat.SixtySeven.GenericLemmaTwo
