/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The exact reflected localization-lift criterion at 827

The finite-`S` constructor for `ReflectedQRelaxedLocalizationLift827`
previously exposed two sufficient inputs: a nonzero projected q-coordinate
and identity of the projected class obstruction.  This file proves the
converse from the representative support already stored in every lift.

Consequently the representative fields carry no remaining existence
content: a lift exists exactly when a pointed q-coordinate is nonzero on the
kernel of the projected class obstruction.  For the canonical cyclotomic
action, the now-proved Fourier seating makes this an exact criterion at any
chosen place over 827.  It also shows that a hypothetical lift is a full
reflected-character wave, not a point mass: all its q-coordinates are
nonzero and its nonpointed-localization vector cannot vanish.

No lift, class-group computation, splitting, or new arithmetic premise is
introduced here.
-/
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.GaugeSteering827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

universe uK uDelta

variable {K : Type uK} [Field K] [NumberField K]
  {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
  (omega chi : InvolutiveBase.Character (PadicInt 59) Delta)

/-- The literal detector-support unit supplied by a lift's representative
support receipt. -/
private noncomputable def detectorSUnitOfLift
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) :
    (detectorSupport827 K).unit K :=
  ⟨lift.candidateRepresentative, by
    intro v hv
    have hp : v ∉ placesOver59 K := fun hp ↦ hv (Or.inl hp)
    have hq : v ∉ placesOver827 K := fun hq ↦ hv (Or.inr hq)
    have hzero := lift.representative_support v hp hq
    rw [← v.valuationOfNeZero_eq lift.candidateRepresentative,
      ← WithZero.coe_one, WithZero.coe_inj]
    exact hzero⟩

/-- The S-unit class obtained from a lift is exactly its projected
two-prime-supported Selmer candidate. -/
private theorem fromSUnitLift_detectorSUnitOfLift
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) :
    IsDedekindDomain.selmerGroup.fromSUnitLift
        (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
          (detectorSupport827 K)
        (QuotientGroup.mk (detectorSUnitOfLift rhoQ omega chi lift)) =
      projectedCandidateAtDetectorSupport827 rhoQ omega chi lift.source := by
  apply Subtype.ext
  change
    ((lift.candidateRepresentative : Kˣ) :
      Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) = _
  exact lift.candidate_represents

/-- The representative support stored in every localization lift forces the
projected finite-S obstruction to be the identity.  This is the missing
reverse direction of the existing finite-S constructor. -/
theorem projectedCandidateSClassObstruction827_eq_one_of_lift
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) :
    projectedCandidateSClassObstruction827 rhoQ omega chi lift.source = 1 := by
  have hrange :
      projectedCandidateAtDetectorSupport827 rhoQ omega chi lift.source ∈
        (IsDedekindDomain.selmerGroup.fromSUnitLift
          (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
            (detectorSupport827 K)).range :=
    ⟨QuotientGroup.mk (detectorSUnitOfLift rhoQ omega chi lift),
      fromSUnitLift_detectorSUnitOfLift rhoQ omega chi lift⟩
  rw [← IsDedekindDomain.selmerGroup.toSClass_ker
    (R := NumberField.RingOfIntegers K) (K := K) (n := 59)] at hrange
  exact hrange

/-- The selected q-coordinate restricted to sources whose projected
finite-S obstruction vanishes. -/
noncomputable def classSilentPointedCoordinate827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    (relaxedClassProjection827 rhoQ omega chi).toLinearMap.ker →ₗ[ZMod 59]
      ZMod 59 :=
  (pointedCoordinate827 rhoQ omega chi selectedPlace).domRestrict
    (relaxedClassProjection827 rhoQ omega chi).toLinearMap.ker

@[simp]
theorem classSilentPointedCoordinate827_apply
    (selectedPlace : {v // v ∈ placesOver827 K})
    (source : (relaxedClassProjection827 rhoQ omega chi).toLinearMap.ker) :
    classSilentPointedCoordinate827 rhoQ omega chi selectedPlace source =
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace
        (qRelaxedReflectedProjector827 rhoQ omega chi source.1) :=
  rfl

/-- Exact generic boundary: a reflected q-relaxed localization lift exists
precisely when some pointed q-coordinate is nonzero on the kernel of the
projected finite-S class obstruction. -/
theorem nonempty_reflectedQRelaxedLocalizationLift827_iff
    : Nonempty (ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) ↔
      ∃ selectedPlace : {v // v ∈ placesOver827 K},
        classSilentPointedCoordinate827 rhoQ omega chi selectedPlace ≠ 0 := by
  constructor
  · rintro ⟨lift⟩
    refine ⟨lift.selectedPlace, ?_⟩
    intro hzero
    have hclass :
        relaxedClassProjection827 rhoQ omega chi lift.source = 0 :=
      (relaxedClassProjection827_eq_zero_iff rhoQ omega chi _).2
        (projectedCandidateSClassObstruction827_eq_one_of_lift
          rhoQ omega chi lift)
    have happ := LinearMap.congr_fun hzero ⟨lift.source,
      LinearMap.mem_ker.mpr hclass⟩
    exact lift.selectedLocalization_ne_zero (by simpa using happ)
  · rintro ⟨selectedPlace, hnonzero⟩
    have hexists : ∃ source,
        classSilentPointedCoordinate827 rhoQ omega chi selectedPlace source ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hnonzero
      apply LinearMap.ext
      intro source
      exact hall source
    obtain ⟨source, hsource⟩ := hexists
    refine ⟨ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
      source.1 selectedPlace ?_ ?_⟩
    · simpa using hsource
    · exact (relaxedClassProjection827_eq_zero_iff rhoQ omega chi _).1
        (LinearMap.mem_ker.mp source.2)

section Cyclotomic

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- A cyclotomic lift is a full reflected-character wave: nonvanishing at
its selected place propagates to every place in the regular 827 orbit. -/
theorem qLocalizationCoordinate_ne_zero_at_every_place_of_lift
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (place : {v // v ∈ placesOver827 K}) :
    qLocalizationCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi place
        (qRelaxedReflectedProjector827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          lift.source) ≠ 0 := by
  let orbit := indexedPlaceOrbitEquiv827 K lift.selectedPlace
  obtain ⟨sigma, rfl⟩ := orbit.surjective place
  rw [(cyclotomicQLocalizationEquivariance827 K omega chi
    lift.selectedPlace).projected_coordinate_orbit]
  exact mul_ne_zero (Units.ne_zero _) lift.selectedLocalization_ne_zero

/-- For the canonical arithmetic action, lift inhabitation is exactly the
pointed class-silent kernel computation at any chosen 827-place.  Fourier
equivariance makes the criterion independent of the selected place. -/
theorem nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    Nonempty (ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) ↔
      classSilentPointedCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          selectedPlace ≠ 0 := by
  constructor
  · rintro ⟨lift⟩
    intro hzero
    have hclass : relaxedClassProjection827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          lift.source = 0 :=
      (relaxedClassProjection827_eq_zero_iff
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi _).2
          (projectedCandidateSClassObstruction827_eq_one_of_lift
            (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi lift)
    have happ := LinearMap.congr_fun hzero ⟨lift.source,
      LinearMap.mem_ker.mpr hclass⟩
    exact qLocalizationCoordinate_ne_zero_at_every_place_of_lift
      omega chi lift selectedPlace (by simpa using happ)
  · intro hnonzero
    exact (nonempty_reflectedQRelaxedLocalizationLift827_iff
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi).2
        ⟨selectedPlace, hnonzero⟩

/-- A canonical lift cannot be a point mass: its other q-localization
coordinates cannot all be silent. -/
theorem tameSilence827_ne_zero_of_lift
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    tameSilence827 (cyclotomicQRelaxedSelmerRepresentation827 K)
        omega chi lift.selectedPlace lift.source ≠ 0 := by
  intro hsilence
  have hclass : relaxedClassProjection827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
        lift.source = 0 :=
    (relaxedClassProjection827_eq_zero_iff
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi _).2
        (projectedCandidateSClassObstruction827_eq_one_of_lift
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi lift)
  have hpoint_mem := fixedAttention_of_fourierSeating
    (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
    lift.selectedPlace
    (cyclotomicQLocalizationEquivariance827 K omega chi lift.selectedPlace)
    ⟨LinearMap.mem_ker.mpr hclass, LinearMap.mem_ker.mpr hsilence⟩
  exact lift.selectedLocalization_ne_zero (LinearMap.mem_ker.mp hpoint_mem)

end Cyclotomic

end Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827
