import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.OneHundredFiftySeven.VandiverDeepReality
import Fermat.OneHundredFiftySeven.VandiverNormalizedRelationDerivative

/-!
# Assembly of Vandiver's Lemma II at exponent 157

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II.  Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences157`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneHundredFiftySeven.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneHundredFiftySeven.VandiverDeepReality
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits
open Fermat.OneHundredFiftySeven.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `157`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences157
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 157),
      PositiveRelationDerivativeCongruences157 hzeta) :
    VandiverLemmaTwo K 157 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit157 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 157 u
        (diagonalVandiverUnit157 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 157 uReal
        (diagonalVandiverUnitFamily157 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit157_coe,
        diagonalVandiverUnitFamily157_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, Subgroup.coe_prod] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily157 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 157 (by decide))
      uReal (diagonalVandiverUnitFamily157 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit157_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.OneHundredFiftySeven.VandiverLemmaTwoAssembly
