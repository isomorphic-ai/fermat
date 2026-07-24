import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.FiveHundredEightySeven.VandiverDeepReality
import Fermat.FiveHundredEightySeven.VandiverNormalizedRelationDerivative

/-!
# Assembly of Vandiver's Lemma II at exponent 587

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II.  Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences587`.
-/

open scoped BigOperators NumberField

namespace Fermat.FiveHundredEightySeven.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FiveHundredEightySeven.VandiverDeepReality
open Fermat.FiveHundredEightySeven.VandiverDiagonalUnits
open Fermat.FiveHundredEightySeven.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `587`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences587
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 587),
      PositiveRelationDerivativeCongruences587 hzeta) :
    VandiverLemmaTwo K 587 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit587 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 587 u
        (diagonalVandiverUnit587 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 587 uReal
        (diagonalVandiverUnitFamily587 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit587_coe,
        diagonalVandiverUnitFamily587_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily587 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 587 (by decide))
      uReal (diagonalVandiverUnitFamily587 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit587_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.FiveHundredEightySeven.VandiverLemmaTwoAssembly
