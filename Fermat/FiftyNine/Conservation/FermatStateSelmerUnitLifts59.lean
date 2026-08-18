/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Unit lifts for the two allocated Fermat factors

Takagi principalization kills both ideal-class obstructions attached to the
literal normalized Fermat factors.  Exactness of the global
unit--Selmer--class sequence therefore supplies honest global-unit lifts of
both strict Selmer sources.  This is stronger than lifting only their
difference and keeps the two factor coordinates separately available for the
later descent.
-/
import Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
import Fermat.FiftyNine.Conservation.FermatStateEquationEight59
import Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatStateSelmerUnitLifts59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.FermatStateEquationEight59
open Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- The actual plus-factor strict Selmer source comes from a global unit
class once its Takagi ideal class has been killed. -/
theorem fermatPlusStrictSelmer59_mem_unitRange_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatPlusStrictSelmer59 pair ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  rw [(selmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)).exact_at_selmer]
  apply Subtype.ext
  change strictSelmerIdealClass59 (K := K)
      (fermatPlusStrictSelmer59 pair) = 0
  rw [fermatPlusStrictSelmer59_idealClass,
    (rootClasses_eq_zero_takagi pair).1]

/-- The actual minus-factor strict Selmer source likewise comes from a
global unit class. -/
theorem fermatMinusStrictSelmer59_mem_unitRange_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatMinusStrictSelmer59 pair ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  rw [(selmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)).exact_at_selmer]
  apply Subtype.ext
  change strictSelmerIdealClass59 (K := K)
      (fermatMinusStrictSelmer59 pair) = 0
  rw [fermatMinusStrictSelmer59_idealClass,
    (rootClasses_eq_zero_takagi pair).2]

/-- Relation (7a), now proved for the actual Fermat state, puts the genuine
plus/minus Selmer difference in the global-unit range. -/
theorem fermatFactorSelmerDifference59_mem_unitRange_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatFactorSelmerDifference59 pair ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) :=
  (fermatFactorSelmerDifference59_mem_unitRange_iff pair).2
    (vandiverSevenA_takagi pair)

/-- An explicit existential readback of the plus global-unit lift. -/
theorem exists_unitLift_fermatPlusStrictSelmer59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ u : UnitModP (NumberField.RingOfIntegers K) 59,
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u =
        fermatPlusStrictSelmer59 pair :=
  fermatPlusStrictSelmer59_mem_unitRange_takagi pair

/-- An explicit existential readback of the minus global-unit lift. -/
theorem exists_unitLift_fermatMinusStrictSelmer59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ u : UnitModP (NumberField.RingOfIntegers K) 59,
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u =
        fermatMinusStrictSelmer59 pair :=
  fermatMinusStrictSelmer59_mem_unitRange_takagi pair

/-! ## Equation-(8) readback of the selected unit classes -/

/-- The unit supplied by equation (8) is a concrete lift of the plus-factor
Selmer source.  The accompanying generator and ideal equality are retained
so later descent code can use the same witnesses. -/
theorem exists_explicitUnitLift_fermatPlusStrictSelmer59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : 𝓞 K) (epsilon : (𝓞 K)ˣ),
      pair.plusIdeal = Ideal.span {rho} ∧
      normalizedPlusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (Additive.ofMul (QuotientGroup.mk epsilon)) =
        fermatPlusStrictSelmer59 pair := by
  obtain ⟨rho, epsilon, hideal, heq⟩ :=
    exists_normalizedPlusFactor_equationEight59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  exact congrArg Additive.ofMul
    (emptySelmerClassOfIdealPower_eq_fromUnitLift_of_eq_unit_mul_pow
      (K := K)
      (normalizedPlusFactor hZeta S hz)
      (normalizedPlusFactor_ne_zero hZeta S hz)
      pair.plusIdeal pair.plus_pow epsilon rho heq).symm

/-- The equation-(8) coefficient on the minus factor is likewise its
concrete global-unit Selmer lift. -/
theorem exists_explicitUnitLift_fermatMinusStrictSelmer59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : 𝓞 K) (epsilon : (𝓞 K)ˣ),
      pair.minusIdeal = Ideal.span {rho} ∧
      normalizedMinusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (Additive.ofMul (QuotientGroup.mk epsilon)) =
        fermatMinusStrictSelmer59 pair := by
  obtain ⟨rho, epsilon, hideal, heq⟩ :=
    exists_normalizedMinusFactor_equationEight59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  exact congrArg Additive.ofMul
    (emptySelmerClassOfIdealPower_eq_fromUnitLift_of_eq_unit_mul_pow
      (K := K)
      (normalizedMinusFactor hZeta S hz)
      (normalizedMinusFactor_ne_zero hZeta S hz)
      pair.minusIdeal pair.minus_pow epsilon rho heq).symm

/-- Both concrete equation-(8) unit lifts, retained together. -/
theorem exists_explicitUnitLift_fermatFactorPair59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rhoPlus : 𝓞 K) (epsilonPlus : (𝓞 K)ˣ)
        (rhoMinus : 𝓞 K) (epsilonMinus : (𝓞 K)ˣ),
      pair.plusIdeal = Ideal.span {rhoPlus} ∧
      normalizedPlusFactor hZeta S hz = epsilonPlus * rhoPlus ^ 59 ∧
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (Additive.ofMul (QuotientGroup.mk epsilonPlus)) =
        fermatPlusStrictSelmer59 pair ∧
      pair.minusIdeal = Ideal.span {rhoMinus} ∧
      normalizedMinusFactor hZeta S hz = epsilonMinus * rhoMinus ^ 59 ∧
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (Additive.ofMul (QuotientGroup.mk epsilonMinus)) =
        fermatMinusStrictSelmer59 pair := by
  obtain ⟨rhoPlus, epsilonPlus, hplusIdeal, hplus, hplusLift⟩ :=
    exists_explicitUnitLift_fermatPlusStrictSelmer59 pair
  obtain ⟨rhoMinus, epsilonMinus, hminusIdeal, hminus, hminusLift⟩ :=
    exists_explicitUnitLift_fermatMinusStrictSelmer59 pair
  exact ⟨rhoPlus, epsilonPlus, rhoMinus, epsilonMinus,
    hplusIdeal, hplus, hplusLift, hminusIdeal, hminus, hminusLift⟩

end Fermat.FiftyNine.Conservation.FermatStateSelmerUnitLifts59
