import Fermat.Descent.Irregular.VandiverLemmaTwoBridge
import Fermat.Descent.Irregular.VandiverRealUnits
import Fermat.Exponents.SixHundredNinetyOne.VandiverDeepReality
import Fermat.Exponents.SixHundredNinetyOne.VandiverNormalizedRelationDerivative

/-!
# Assembly of Vandiver's Lemma II at exponent 691

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II.  Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences691`.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredNinetyOne.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixHundredNinetyOne.VandiverDeepReality
open Fermat.SixHundredNinetyOne.VandiverDiagonalUnits
open Fermat.SixHundredNinetyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `691`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences691
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 691),
      PositiveRelationDerivativeCongruences691 hzeta) :
    VandiverLemmaTwo K 691 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit691 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 691 u
        (diagonalVandiverUnit691 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 691 uReal
        (diagonalVandiverUnitFamily691 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit691_coe,
        diagonalVandiverUnitFamily691_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily691 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 691 (by decide))
      uReal (diagonalVandiverUnitFamily691 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit691_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.SixHundredNinetyOne.VandiverLemmaTwoAssembly
