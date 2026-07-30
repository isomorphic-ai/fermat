/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Vandiver's conjugate normalized state pair

The two selected Fermat factors use the same denominator `ζ - 1`.
Conjugation sends that denominator to

`ζ⁻¹ - 1 = (-ζ⁻¹) * (ζ - 1)`,

so the normalized minus factor is the conjugate plus factor multiplied by
the unit `-ζ⁻¹`.  Their principal ideals are therefore literal conjugates.

Vandiver's statewise fold needs the same statement for the allocated ideal
roots.  It follows without an additional allocation hypothesis: the two
root powers are conjugate principal ideals, and nonzero natural powers are
injective in the ideal monoid of a Dedekind domain.
-/
import Fermat.FiftyNine.Conservation.Fold
import Fermat.FiftyNine.Conservation.StateFactorPair

open scoped NumberField

namespace Fermat.FiftyNine.Conservation.StateFactorConjugation

open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorPair

noncomputable section

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

variable {ζ : K}

private theorem complexConj_primitiveRoot
    (hζ : IsPrimitiveRoot ζ 59) :
    NumberField.IsCMField.complexConj K ζ = ζ⁻¹ := by
  let ζunit : (𝓞 K)ˣ := zetaUnit hζ
  have hζunitPow : ζunit ^ 59 = 1 := by
    apply Units.ext
    exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hmem : ζunit ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨59, by norm_num, hζunitPow⟩
  simpa [ζunit, zetaUnit] using
    NumberField.IsCMField.complexConj_torsion
      (K := K)
      (⟨ζunit, hmem⟩ : NumberField.Units.torsion K)

private theorem ringConj_toInteger
    (hζ : IsPrimitiveRoot ζ 59) :
    NumberField.IsCMField.ringOfIntegersComplexConj K hζ.toInteger =
      (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  change NumberField.IsCMField.complexConj K ζ =
    (((↑((zetaUnit hζ)⁻¹) : 𝓞 K)) : K)
  rw [complexConj_primitiveRoot hζ]
  rw [show
      (((↑((zetaUnit hζ)⁻¹) : 𝓞 K)) : K) =
        (((zetaUnit hζ : 𝓞 K) : K))⁻¹ by simp]
  rw [zetaUnit_val hζ]
  rfl

private theorem ringConj_fixedDenominator
    (hζ : IsPrimitiveRoot ζ 59) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (fixedDenominator hζ) =
      (↑(-((zetaUnit hζ)⁻¹)) : 𝓞 K) *
        fixedDenominator hζ := by
  have hinv_mul :
      (↑((zetaUnit hζ)⁻¹) : 𝓞 K) * hζ.toInteger = 1 := by
    rw [← zetaUnit_val hζ, ← Units.val_mul]
    simp
  simp only [fixedDenominator, map_sub, map_one,
    ringConj_toInteger hζ, Units.val_neg]
  change
    (↑((zetaUnit hζ)⁻¹) : 𝓞 K) - 1 =
      -(↑((zetaUnit hζ)⁻¹) : 𝓞 K) *
        (hζ.toInteger - 1)
  calc
    (↑((zetaUnit hζ)⁻¹) : 𝓞 K) - 1 =
        -1 + (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by ring
    _ = -
        ((↑((zetaUnit hζ)⁻¹) : 𝓞 K) * hζ.toInteger) +
          (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by rw [hinv_mul]
    _ = -(↑((zetaUnit hζ)⁻¹) : 𝓞 K) *
          (hζ.toInteger - 1) := by ring

private theorem ringConj_stateFactor_plus
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (Fermat.Conservation.KummerDrain.factorNode
          (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger) =
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K)
          (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by
  simp only [Fermat.Conservation.KummerDrain.factorNode,
    map_add, map_mul, map_intCast, ringConj_toInteger hζ]

/-- The normalized minus factor is the conjugate plus factor times the
unit which converts the conjugate denominator `ζ⁻¹ - 1` back to the
chosen common denominator `ζ - 1`.  This is Vandiver's normalized
conjugate-pair bookkeeping at the element level. -/
theorem normalizedMinusFactor_eq_unit_mul_conj
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedMinusFactor hζ S hz =
      (↑(-((zetaUnit hζ)⁻¹)) : 𝓞 K) *
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (normalizedPlusFactor hζ S hz) := by
  apply mul_right_cancel₀
    (show fixedDenominator hζ ≠ 0 by
      exact sub_ne_zero.mpr
        (hζ.toInteger_isPrimitiveRoot.ne_one (by norm_num)))
  rw [normalizedMinusFactor_spec]
  symm
  calc
    ((↑(-((zetaUnit hζ)⁻¹)) : 𝓞 K) *
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (normalizedPlusFactor hζ S hz)) *
        fixedDenominator hζ =
      NumberField.IsCMField.ringOfIntegersComplexConj K
        (normalizedPlusFactor hζ S hz) *
          NumberField.IsCMField.ringOfIntegersComplexConj K
            (fixedDenominator hζ) := by
              rw [ringConj_fixedDenominator hζ]
              ring
    _ = NumberField.IsCMField.ringOfIntegersComplexConj K
          (normalizedPlusFactor hζ S hz *
            fixedDenominator hζ) := by
              rw [map_mul]
    _ = NumberField.IsCMField.ringOfIntegersComplexConj K
          (Fermat.Conservation.KummerDrain.factorNode
            (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger) := by
              rw [normalizedPlusFactor_spec]
    _ = Fermat.Conservation.KummerDrain.factorNode
          (S.x : 𝓞 K) (S.y : 𝓞 K)
            (↑((zetaUnit hζ)⁻¹) : 𝓞 K) :=
      ringConj_stateFactor_plus hζ S

/-- Although the two normalized elements differ by a unit after
conjugation, their principal ideals are literal conjugates. -/
theorem span_normalizedMinusFactor_eq_map_conj
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    Ideal.span {normalizedMinusFactor hζ S hz} =
      Ideal.map
        (NumberField.IsCMField.ringOfIntegersComplexConj K)
        (Ideal.span {normalizedPlusFactor hζ S hz}) := by
  rw [Ideal.map_span, Set.image_singleton,
    normalizedMinusFactor_eq_unit_mul_conj hζ S hz]
  exact Ideal.span_singleton_mul_left_unit
    (Units.isUnit (-((zetaUnit hζ)⁻¹)))
    (NumberField.IsCMField.ringOfIntegersComplexConj K
      (normalizedPlusFactor hζ S hz))

set_option maxRecDepth 2000 in
/-- The allocated minus root is forced to be the conjugate of the plus
root: their `59`th powers are the conjugate principal ideals, and ideal
powers in a Dedekind domain are injective. -/
theorem StateLinkedIdealPair.minusIdeal_eq_map_conj_plusIdeal
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.minusIdeal =
      Ideal.map
        (NumberField.IsCMField.ringOfIntegersComplexConj K)
        pair.plusIdeal := by
  apply pow_left_injective (by norm_num : 59 ≠ 0)
  calc
    pair.minusIdeal ^ 59 =
        Ideal.span {normalizedMinusFactor hζ S hz} :=
      pair.minus_pow
    _ = Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (Ideal.span {normalizedPlusFactor hζ S hz}) :=
      span_normalizedMinusFactor_eq_map_conj hζ S hz
    _ = Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (pair.plusIdeal ^ 59) := by rw [pair.plus_pow]
    _ =
        (Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          pair.plusIdeal) ^ 59 :=
      Ideal.map_pow
        (NumberField.IsCMField.ringOfIntegersComplexConj K)
        pair.plusIdeal 59

/-- The selected two-node allocation ledger therefore satisfies the
conjugation-as-transpose input needed by Vandiver's statewise fold. -/
theorem StateLinkedIdealPair.ledger_conjugationTranspose
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.ledger.rootIdeal 1 =
      Ideal.map
        (NumberField.IsCMField.ringOfIntegersComplexConj K)
        (pair.ledger.rootIdeal 0) := by
  simpa using
    StateLinkedIdealPair.minusIdeal_eq_map_conj_plusIdeal pair

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000 in
/-- Vandiver's equation (7d) for the actual normalized state pair.  The
state supplies conjugation as ledger transpose above; the selected
relative-norm fold then kills its real norm class. -/
theorem StateLinkedIdealPair.vandiverSevenD
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.ledger.VandiverSevenD 0 1 :=
  Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_conjugationTranspose
    (ledger := pair.ledger) (i := 0) (j := 1)
    (ledger_conjugationTranspose pair)

/-- Once the same state pair supplies Vandiver's remaining Lemma-I
relation (7a), its derived fold relation (7d) nets both selected classes
and discharges the complete two-node factor-principalization permit. -/
theorem StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz)
    (sevenA : pair.ledger.VandiverSevenA 0 1) :
    Fermat.Conservation.KummerDrain.FactorPrincipalizationPermit
      pair.ledger :=
  Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_finTwo_of_vandiver_relations
    pair.ledger (by norm_num) sevenA (vandiverSevenD pair)

end

end Fermat.FiftyNine.Conservation.StateFactorConjugation
