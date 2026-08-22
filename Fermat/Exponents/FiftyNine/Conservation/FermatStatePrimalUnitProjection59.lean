/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Equation-(8) units in the actual irregular character seat

The equation-(8) coefficient units are concrete preimages of the two
Fermat-factor Selmer sources.  Applying the canonical character projector
therefore identifies the actual odd irregular modes with projections of
those same explicit unit classes.  No choice made by abstract exactness is
left in this readback.
-/
import Fermat.Exponents.FiftyNine.Conservation.FermatStateSelmerUnitLifts59

open scoped MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatStatePrimalUnitProjection59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.FermatStateSelmerUnitLifts59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- The actual plus irregular mode is the projection of its concrete
equation-(8) coefficient unit. -/
theorem exists_explicitUnitProjection_fermatPlusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : 𝓞 K) (epsilon : (𝓞 K)ˣ),
      pair.plusIdeal = Ideal.span {rho} ∧
      normalizedPlusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (Additive.ofMul (QuotientGroup.mk epsilon))) =
        fermatPlusPrimalMode59 pair := by
  obtain ⟨rho, epsilon, hideal, heq, hlift⟩ :=
    exists_explicitUnitLift_fermatPlusStrictSelmer59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  rw [hlift]
  rfl

/-- The actual minus irregular mode is the projection of its concrete
equation-(8) coefficient unit. -/
theorem exists_explicitUnitProjection_fermatMinusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : 𝓞 K) (epsilon : (𝓞 K)ˣ),
      pair.minusIdeal = Ideal.span {rho} ∧
      normalizedMinusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (Additive.ofMul (QuotientGroup.mk epsilon))) =
        fermatMinusPrimalMode59 pair := by
  obtain ⟨rho, epsilon, hideal, heq, hlift⟩ :=
    exists_explicitUnitLift_fermatMinusStrictSelmer59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  rw [hlift]
  rfl

/-- Both explicit equation-(8) unit projections, retained together in the
same actual state. -/
theorem exists_explicitUnitProjection_fermatFactorPair59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rhoPlus : 𝓞 K) (epsilonPlus : (𝓞 K)ˣ)
        (rhoMinus : 𝓞 K) (epsilonMinus : (𝓞 K)ˣ),
      pair.plusIdeal = Ideal.span {rhoPlus} ∧
      normalizedPlusFactor hZeta S hz = epsilonPlus * rhoPlus ^ 59 ∧
      characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (Additive.ofMul (QuotientGroup.mk epsilonPlus))) =
        fermatPlusPrimalMode59 pair ∧
      pair.minusIdeal = Ideal.span {rhoMinus} ∧
      normalizedMinusFactor hZeta S hz = epsilonMinus * rhoMinus ^ 59 ∧
      characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (Additive.ofMul (QuotientGroup.mk epsilonMinus))) =
        fermatMinusPrimalMode59 pair := by
  obtain ⟨rhoPlus, epsilonPlus, hplusIdeal, hplus, hplusProjection⟩ :=
    exists_explicitUnitProjection_fermatPlusPrimalMode59 pair
  obtain ⟨rhoMinus, epsilonMinus, hminusIdeal, hminus,
      hminusProjection⟩ :=
    exists_explicitUnitProjection_fermatMinusPrimalMode59 pair
  exact ⟨rhoPlus, epsilonPlus, rhoMinus, epsilonMinus,
    hplusIdeal, hplus, hplusProjection,
    hminusIdeal, hminus, hminusProjection⟩

end Fermat.FiftyNine.Conservation.FermatStatePrimalUnitProjection59
