import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.OneThousandEightHundredThirtyOne.VandiverDeepReality1831
import Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative1831

/-!
# Assembly of Vandiver's Lemma II at exponent 1831

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II. Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences1831`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandEightHundredThirtyOne.VandiverDeepReality
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits
open Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1831) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `1831`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences1831
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831),
      PositiveRelationDerivativeCongruences1831 hzeta) :
    VandiverLemmaTwo K 1831 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit1831 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 1831 u
        (diagonalVandiverUnit1831 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 1831 uReal
        (diagonalVandiverUnitFamily1831 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit1831_coe,
        diagonalVandiverUnitFamily1831_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily1831 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 1831 (by decide))
      uReal (diagonalVandiverUnitFamily1831 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit1831_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverLemmaTwoAssembly
