import Fermat.Irregular.VandiverFiniteIndex
import Fermat.Irregular.VandiverLemmaTwoBridge
import Fermat.Irregular.VandiverRealUnits
import Fermat.ThirtySeven.ResidueHomomorphisms

/-!
# The real cyclotomic unit system for Vandiver's Lemma II at 37

This module gives the group-theoretically correct exponent-`37`
instantiation of the generic Lemma II core.  The family consists of the
seventeen normalized real circular units, regarded as elements of
Mathlib's real-unit subgroup.  The uploaded residue-symbol determinant
proves that their closure has finite index.  The `37`-power map is
injective on this subgroup by the odd-power theorem for real CM units.

The logarithmic-derivative congruence remains a separate theorem about
this family; no version of it is assumed here.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.VandiverLemmaTwoUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.VandiverLemmaTwoCore
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K]

/-- The canonical seventeen circular units, typed in the real-unit
subgroup where odd-power injectivity is valid. -/
def realCircularUnitFamily37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    SourceIndex 37 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨circularUnit37 hζ i, circularUnit37_mem_realUnits hζ i⟩

/-- The ambient closure of the same seventeen units has finite index in
the full unit group. -/
theorem ambient_closure_finiteIndex {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    (Subgroup.closure (Set.range fun i : SourceIndex 37 ↦
      ((realCircularUnitFamily37 hζ i :
        NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ))).FiniteIndex := by
  have hnot :=
    Fermat.ThirtySeven.ResidueHomomorphisms.not_dvd_circularUnit37_full_index hζ
  have hsup :
      (Subgroup.closure (Set.range (circularUnit37 hζ)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 37
  have hclosure :
      (Subgroup.closure (Set.range (circularUnit37 hζ))).FiniteIndex :=
    (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
      (Subgroup.closure (Set.range (circularUnit37 hζ)))).2 hsup
  simpa [realCircularUnitFamily37] using hclosure

/-- Vandiver's real circular-unit family has finite-index closure inside
the real-unit group itself. -/
theorem real_closure_finiteIndex {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    (Subgroup.closure (Set.range (realCircularUnitFamily37 hζ))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : SourceIndex 37 ↦
        ((realCircularUnitFamily37 hζ i :
          NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ))).FiniteIndex :=
    ambient_closure_finiteIndex hζ
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K) (realCircularUnitFamily37 hζ)

omit [IsCyclotomicExtension {37} ℚ K] in
/-- The power-map hypothesis of the generic Lemma II core, instantiated
on the correct group. -/
theorem pow_thirtySeven_injective :
    Function.Injective
      (fun u : NumberField.IsCMField.realUnits K ↦ u ^ (37 : ℕ)) :=
  Fermat.Irregular.VandiverRealUnits.odd_pow_injective 37 (by decide)

/-- All group-theoretic and finite-index inputs of Vandiver's Lemma II at
`37`, leaving only the historical primitive-relation congruence. -/
theorem real_isPower_or_bernoulliObstruction
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (u : NumberField.IsCMField.realUnits K)
    (hcong : PrimitiveRelationCubeCongruences 37 u
      (realCircularUnitFamily37 hζ)) :
    (∃ v : NumberField.IsCMField.realUnits K, u = v ^ (37 : ℕ)) ∨
      Fermat.Irregular.VandiverUnitLemma.BernoulliObstruction 37 := by
  letI :
      (Subgroup.closure (Set.range (realCircularUnitFamily37 hζ))).FiniteIndex :=
    real_closure_finiteIndex hζ
  exact Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
    (by norm_num) pow_thirtySeven_injective u
      (realCircularUnitFamily37 hζ) hcong

end

end Fermat.ThirtySeven.VandiverLemmaTwoUnits
