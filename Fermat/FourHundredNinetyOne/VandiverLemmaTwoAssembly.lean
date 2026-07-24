import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.FourHundredNinetyOne.VandiverDeepReality
import Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative

/-!
# Assembly of Vandiver's Lemma II at exponent 491

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II.  Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences491`.
-/

open scoped BigOperators NumberField

namespace Fermat.FourHundredNinetyOne.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FourHundredNinetyOne.VandiverDeepReality
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits
open Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `491`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences491
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 491),
      PositiveRelationDerivativeCongruences491 hzeta) :
    VandiverLemmaTwo K 491 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit491 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 491 u
        (diagonalVandiverUnit491 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 491 uReal
        (diagonalVandiverUnitFamily491 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit491_coe,
        diagonalVandiverUnitFamily491_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily491 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 491 (by decide))
      uReal (diagonalVandiverUnitFamily491 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit491_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.FourHundredNinetyOne.VandiverLemmaTwoAssembly
