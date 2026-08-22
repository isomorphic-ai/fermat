/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Literal equation (8) for the allocated Fermat state

The statewise Takagi--Furtwängler bridge kills both ideal classes allocated
to the normalized conjugate Fermat factors.  This file reads those two zero
classes back as principality of the actual integral root ideals and applies
the generic generator lemma to obtain Vandiver's literal equation (8): each
normalized factor is a unit times a `59`th power.

There is no new arithmetic premise here.  The witnesses are extracted from
the actual state ideals and their already-proved power identities.
-/
import Fermat.Exponents.FiftyNine.Conservation.FermatStateTakagiSevenA59

open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatStateEquationEight59

open Fermat.Conservation.Credit.Fold
open Fermat.Conservation.KummerDrain
open Fermat.Irregular.VandiverCriterion
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

private theorem plusIdeal_isPrincipal_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    Submodule.IsPrincipal (pair.plusIdeal : Ideal (𝓞 K)) := by
  have hzero := (rootClasses_eq_zero_takagi pair).1
  have hfractional :
      Submodule.IsPrincipal
        (((pair.plusIdeal : Ideal (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    apply (fractionalIdealClass_eq_zero_iff
      (pair.plusIdeal : FractionalIdeal (𝓞 K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr pair.plusIdeal_ne_zero)).mp
    simpa only [AllocatedFactorLedger.rootClass,
      StateLinkedIdealPair.ledger_rootIdeal_zero] using hzero
  exact (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K).mp hfractional

private theorem minusIdeal_isPrincipal_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    Submodule.IsPrincipal (pair.minusIdeal : Ideal (𝓞 K)) := by
  have hzero := (rootClasses_eq_zero_takagi pair).2
  have hfractional :
      Submodule.IsPrincipal
        (((pair.minusIdeal : Ideal (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    apply (fractionalIdealClass_eq_zero_iff
      (pair.minusIdeal : FractionalIdeal (𝓞 K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr pair.minusIdeal_ne_zero)).mp
    simpa only [AllocatedFactorLedger.rootClass,
      StateLinkedIdealPair.ledger_rootIdeal_one] using hzero
  exact (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K).mp hfractional

/-- Literal equation (8) for the normalized plus factor of the actual
allocated Fermat state. -/
theorem exists_normalizedPlusFactor_equationEight59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : 𝓞 K) (epsilon : (𝓞 K)ˣ),
      pair.plusIdeal = Ideal.span {rho} ∧
        normalizedPlusFactor hZeta S hz = epsilon * rho ^ 59 := by
  exact exists_unit_mul_pow_eq_of_isPrincipal_ideal
    pair.plusIdeal (normalizedPlusFactor hZeta S hz)
    (plusIdeal_isPrincipal_takagi pair) pair.plus_pow

/-- Literal equation (8) for the normalized minus factor of the actual
allocated Fermat state. -/
theorem exists_normalizedMinusFactor_equationEight59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : 𝓞 K) (epsilon : (𝓞 K)ˣ),
      pair.minusIdeal = Ideal.span {rho} ∧
        normalizedMinusFactor hZeta S hz = epsilon * rho ^ 59 := by
  exact exists_unit_mul_pow_eq_of_isPrincipal_ideal
    pair.minusIdeal (normalizedMinusFactor hZeta S hz)
    (minusIdeal_isPrincipal_takagi pair) pair.minus_pow

/-- The two literal equation-(8) witnesses, retained together for the
conjugate normalized factor pair selected by the Fermat state. -/
theorem exists_normalizedFactor_equationEightPair59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rhoPlus : 𝓞 K) (epsilonPlus : (𝓞 K)ˣ)
        (rhoMinus : 𝓞 K) (epsilonMinus : (𝓞 K)ˣ),
      pair.plusIdeal = Ideal.span {rhoPlus} ∧
      normalizedPlusFactor hZeta S hz = epsilonPlus * rhoPlus ^ 59 ∧
      pair.minusIdeal = Ideal.span {rhoMinus} ∧
      normalizedMinusFactor hZeta S hz = epsilonMinus * rhoMinus ^ 59 := by
  obtain ⟨rhoPlus, epsilonPlus, hplusIdeal, hplus⟩ :=
    exists_normalizedPlusFactor_equationEight59 pair
  obtain ⟨rhoMinus, epsilonMinus, hminusIdeal, hminus⟩ :=
    exists_normalizedMinusFactor_equationEight59 pair
  exact ⟨rhoPlus, epsilonPlus, rhoMinus, epsilonMinus,
    hplusIdeal, hplus, hminusIdeal, hminus⟩

end Fermat.FiftyNine.Conservation.FermatStateEquationEight59
