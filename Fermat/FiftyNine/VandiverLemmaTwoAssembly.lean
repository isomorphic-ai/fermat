import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.FiftyNine.VandiverDeepReality
import Fermat.FiftyNine.VandiverNormalizedRelationDerivative

/-!
# Assembly of Vandiver's Lemma II at exponent 59

This module assembles the real-unit, finite-index, relation-normalization,
and group-theoretic parts of Lemma II.  Its sole input is the positive
polynomial-relation derivative statement isolated in
`PositiveRelationDerivativeCongruences59`.
-/

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.VandiverLemmaTwoAssembly

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FiftyNine.VandiverDeepReality
open Fermat.FiftyNine.VandiverDiagonalUnits
open Fermat.FiftyNine.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

/-- The literal repository interface for Vandiver's Lemma II at `59`,
reduced only to the positive polynomial-relation derivative theorem. -/
theorem vandiverLemmaTwo_of_positiveRelationDerivativeCongruences59
    (hpositive : ∀ {zeta : K} (hzeta : IsPrimitiveRoot zeta 59),
      PositiveRelationDerivativeCongruences59 hzeta) :
    VandiverLemmaTwo K 59 := by
  intro zeta hzeta u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit59 hzeta u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences 59 u
        (diagonalVandiverUnit59 hzeta) :=
    primitiveRelationCubeCongruences_of_positive
      hzeta u hdeep (hpositive hzeta)
  have hcongReal :
      PrimitiveRelationCubeCongruences 59 uReal
        (diagonalVandiverUnitFamily59 hzeta) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit59_coe,
        diagonalVandiverUnitFamily59_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, Subgroup.coe_prod] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (diagonalVandiverUnitFamily59 hzeta))).FiniteIndex :=
    real_closure_finiteIndex hzeta
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (by norm_num)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) 59 (by decide))
      uReal (diagonalVandiverUnitFamily59 hzeta) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit59_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.FiftyNine.VandiverLemmaTwoAssembly
