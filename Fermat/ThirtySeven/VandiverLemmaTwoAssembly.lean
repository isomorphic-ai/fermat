import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.ThirtySeven.VandiverDeepReality
import Fermat.ThirtySeven.VandiverNormalizedRelationDerivative

/-!
# Assembly of Vandiver's Lemma II at exponent 37

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II.  Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences37`.
-/

open scoped BigOperators NumberField

namespace Fermat.ThirtySeven.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.ThirtySeven.VandiverDeepReality
open Fermat.ThirtySeven.VandiverDiagonalUnits
open Fermat.ThirtySeven.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `37`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences37
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 37),
      PositiveRelationDerivativeCongruences37 hzeta) :
    VandiverLemmaTwo K 37 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit37 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 37 u
        (diagonalVandiverUnit37 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 37 uReal
        (diagonalVandiverUnitFamily37 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit37_coe,
        diagonalVandiverUnitFamily37_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily37 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 37 (by decide))
      uReal (diagonalVandiverUnitFamily37 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit37_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.ThirtySeven.VandiverLemmaTwoAssembly
