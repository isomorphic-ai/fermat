import Fermat.Descent.Irregular.VandiverLemmaTwoBridge
import Fermat.Descent.Irregular.VandiverRealUnits
import Fermat.Exponents.OneThousandThreeHundredEightyOne.VandiverDeepReality1381
import Fermat.Exponents.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative1381

/-!
# Assembly of Vandiver's Lemma II at exponent 1381

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II. Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences1381`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandThreeHundredEightyOne.VandiverDeepReality
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits
open Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `1381`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences1381
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381),
      PositiveRelationDerivativeCongruences1381 hzeta) :
    VandiverLemmaTwo K 1381 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit1381 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 1381 u
        (diagonalVandiverUnit1381 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 1381 uReal
        (diagonalVandiverUnitFamily1381 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit1381_coe,
        diagonalVandiverUnitFamily1381_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily1381 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 1381 (by decide))
      uReal (diagonalVandiverUnitFamily1381 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit1381_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverLemmaTwoAssembly
