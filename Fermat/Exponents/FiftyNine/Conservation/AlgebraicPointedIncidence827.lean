/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Construct the pointed 827 incidence from its two visible coordinates

For the concrete `PointedTateIncidence827` shape, Fourier seating makes the
primal conormal arrow zero.  A nonzero reflected localization then makes the
one-dimensional connecting arrow injective, and its image is exactly the
annihilator of the kernel inclusion.  These are precisely the two stored
exactness fields.

Thus an already-typed reflected q-relaxed localization lift supplies the
remaining nonzero value.  No complement or splitting is selected.
-/
import Fermat.Experiments.Conservation.ReadoutLedger
import Fermat.Exponents.FiftyNine.Conservation.DetectorWitness827
import Fermat.Exponents.FiftyNine.Conservation.PointedTateIncidence

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827

open Fermat.Conservation
open Fermat.Conservation.ReadoutLedger
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.SteeringFiber
open DetectorWitness827
open GaugeSteering827
open PointedTateIncidence
open SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fact (0 < 59) := ⟨by decide⟩

variable {K : Type} [Field K] [NumberField K]
variable {Delta : Type} [CommGroup Delta] [Fintype Delta]
variable [Invertible (Fintype.card Delta : PadicInt 59)]
variable (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
variable (omega chi : InvolutiveBase.Character (PadicInt 59) Delta)
variable (selectedPlace : {v // v ∈ placesOver827 K})

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59) (QRelaxedReflectedDual827 rhoQ omega chi) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero rhoQ omega chi)

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
/-- A nonzero reflected localization makes its scalar transpose injective. -/
theorem reflectedCoordinatePairing827_flip_injective
    (hloc : reflectedPointedLocalization827 rhoQ omega chi selectedPlace ≠ 0) :
    Function.Injective
      (reflectedCoordinatePairing827 rhoQ omega chi selectedPlace).flip := by
  have hexists : ∃ y : QRelaxedReflectedDual827 rhoQ omega chi,
      reflectedPointedLocalization827 rhoQ omega chi selectedPlace y ≠ 0 := by
    by_contra h
    push Not at h
    apply hloc
    ext y
    exact h y
  obtain ⟨y, hy⟩ := hexists
  intro a b hab
  have hvalue := LinearMap.congr_fun hab y
  change
    reflectedPointedLocalization827 rhoQ omega chi selectedPlace y * a =
      reflectedPointedLocalization827 rhoQ omega chi selectedPlace y * b at hvalue
  exact mul_left_cancel₀ hy hvalue

/-- Fixed primal attention and one nonzero reflected localization value
construct both exactness fields of the concrete pointed incidence. -/
noncomputable def pointedTateIncidence827_of_fixed_of_localization_ne_zero
    (fixed : FixedAttention
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace))
    (hloc : reflectedPointedLocalization827 rhoQ omega chi selectedPlace ≠ 0) :
    PointedTateIncidence827 rhoQ omega chi selectedPlace where
  exact_at_pointed := by
    rw [LinearMap.exact_iff]
    have hprimal :
        (pointedConditions827 rhoQ omega chi selectedPlace).localization = 0 := by
      change pointedConormalRestriction827 rhoQ omega chi selectedPlace = 0
      exact (focusConormalRestriction_eq_zero_iff_fixed
        (relaxedClassProjection827 rhoQ omega chi)
        (tameSilence827 rhoQ omega chi selectedPlace)
        (pointedCoordinate827 rhoQ omega chi selectedPlace)).2 fixed
    rw [hprimal, LinearMap.range_zero,
      LinearMap.ker_eq_bot.mpr
        (reflectedCoordinatePairing827_flip_injective
          rhoQ omega chi selectedPlace hloc)]
  exact_at_reflected := by
    rw [LinearMap.exact_iff]
    ext f
    constructor
    · intro hf
      have hker :
          (reflectedPointedLocalization827 rhoQ omega chi selectedPlace).ker ≤
            f.ker := by
        intro y hy
        rw [LinearMap.mem_ker]
        have hzero := LinearMap.congr_fun (LinearMap.mem_ker.mp hf) ⟨y, hy⟩
        change f y = 0 at hzero
        exact hzero
      obtain ⟨a, ha, _⟩ := existsUnique_rankOneFactorization
        (reflectedPointedLocalization827 rhoQ omega chi selectedPlace)
        f hloc hker
      refine ⟨a, ?_⟩
      apply LinearMap.ext
      intro y
      change
        reflectedPointedLocalization827 rhoQ omega chi selectedPlace y * a = f y
      rw [ha y, mul_comm]
    · rintro ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      change
        reflectedPointedLocalization827 rhoQ omega chi selectedPlace y.1 * a = 0
      rw [LinearMap.mem_ker.mp y.property, zero_mul]

/-! ## The conductor-59 Fourier specialization -/

section CyclotomicIndex

variable [IsCyclotomicExtension {59} ℚ K]
variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
variable (rhoQ59 : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
variable (omega59 chi59 :
  InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

omit [IsCyclotomicExtension {59} ℚ K] in
/-- A typed q-relaxed lift exposes a nonzero value of the actual reflected
localization functional. -/
theorem reflectedPointedLocalization827_ne_zero_of_lift
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ59 omega59 chi59) :
    reflectedPointedLocalization827 rhoQ59 omega59 chi59 lift.selectedPlace ≠
      0 := by
  intro hzero
  have hvalue := LinearMap.congr_fun hzero lift.candidate
  change qLocalizationCoordinate827 rhoQ59 omega59 chi59 lift.selectedPlace
      lift.candidate = 0 at hvalue
  exact lift.selectedLocalization_ne_zero hvalue

/-- Fourier seating plus any nonzero reflected localization value constructs
the pointed incidence; no independent five-term exactness package remains. -/
noncomputable def pointedTateIncidence827_of_fourierSeating_of_localization_ne_zero
    (selected : Place827 K)
    (seating : QLocalizationEquivariance827 rhoQ59 omega59 chi59 selected)
    (hloc : reflectedPointedLocalization827 rhoQ59 omega59 chi59 selected ≠ 0) :
    PointedTateIncidence827 rhoQ59 omega59 chi59 selected :=
  pointedTateIncidence827_of_fixed_of_localization_ne_zero
    rhoQ59 omega59 chi59 selected
    (fixedAttention_of_fourierSeating
      rhoQ59 omega59 chi59 selected seating)
    hloc

/-- The concrete reflected lift supplies the nonzero value required by the
Fourier-seated incidence constructor. -/
noncomputable def pointedTateIncidence827_of_fourierSeating_of_lift
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ59 omega59 chi59)
    (seating : QLocalizationEquivariance827
      rhoQ59 omega59 chi59 lift.selectedPlace) :
    PointedTateIncidence827 rhoQ59 omega59 chi59 lift.selectedPlace :=
  pointedTateIncidence827_of_fourierSeating_of_localization_ne_zero
    rhoQ59 omega59 chi59 lift.selectedPlace seating
    (reflectedPointedLocalization827_ne_zero_of_lift
      rhoQ59 omega59 chi59 lift)

end CyclotomicIndex

end Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827
