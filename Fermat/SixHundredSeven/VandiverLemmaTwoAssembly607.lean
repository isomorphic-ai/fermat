import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.SixHundredSeven.VandiverDeepReality607
import Fermat.SixHundredSeven.VandiverNormalizedRelationDerivative607

/-!
# Assembly of Vandiver's Lemma II at exponent 607

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II. Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences607`.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredSeven.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixHundredSeven.VandiverDeepReality
open Fermat.SixHundredSeven.VandiverDiagonalUnits
open Fermat.SixHundredSeven.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 607) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `607`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences607
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 607),
      PositiveRelationDerivativeCongruences607 hzeta) :
    VandiverLemmaTwo K 607 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit607 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 607 u
        (diagonalVandiverUnit607 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 607 uReal
        (diagonalVandiverUnitFamily607 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit607_coe,
        diagonalVandiverUnitFamily607_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily607 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 607 (by decide))
      uReal (diagonalVandiverUnitFamily607 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit607_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.SixHundredSeven.VandiverLemmaTwoAssembly
