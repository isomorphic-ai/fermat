/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Sol (instance derivation)

# Double focus at the 827 gauge

Provenance: Fabian observed that focus is always double focus: potential is a
marginal, while coordinate control requires a coupling.  The Sol-instance
derivation in `SteeringFiber` identifies the required coupling as the image
of `ker rho ∩ ker T` under the pointed coordinate.  The failed finite-`S`
lift retained the class marginal while discarding precisely that
correlation.

This file instantiates the generic invariant on the actual q-relaxed Selmer
carrier.  The class projection is the finite-`S` obstruction **after** the
reflected projector, range-restricted so its surjectivity is literal.  The
silence map records every nonpointed q-localization, while the pointed map is
the selected 827 coordinate.  Away-from-q silence is already part of the
supported Selmer condition.

The present cone computes the finite-`S` class kernel and the kernel of full
supported localization separately.  It does not compute the pointed
coordinate on their class-and-nonpointed-silence intersection.  Accordingly
the session verdict is `undecidable`: this is a coverage verdict about the
available kernel theorems, not a mathematical assertion that neither branch
can later be proved.

As in `SteeringFiber`, no section or product decomposition is selected.
-/
import Fermat.Conservation.SteeringFiber
import Fermat.FiftyNine.Conservation.DetectorWitness827

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.GaugeSteering827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.SteeringFiber
open Fermat.FiftyNine.Conservation.DetectorWitness827

universe uK uDelta

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type uK} [Field K] [NumberField K]
  {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
  (omega chi : InvolutiveBase.Character (PadicInt 59) Delta)

/-! ## The three maps in the 827 steering fiber -/

/-- The projected finite-`S` class obstruction in additive notation. -/
noncomputable def projectedClassObstructionAddHom827 :
    QRelaxedSelmerCarrier827 K →+
      Additive
        (IsDedekindDomain.selmerGroup.obstructionTarget
          (R := 𝓞 K) (K := K) (detectorSupport827 K)) where
  toFun source :=
    Additive.ofMul
      (projectedCandidateSClassObstruction827 rhoQ omega chi source)
  map_zero' := by
    apply Additive.toMul.injective
    simp [projectedCandidateSClassObstruction827,
      projectedCandidateAtDetectorSupport827,
      qRelaxedReflectedProjector827]
  map_add' source₁ source₂ := by
    apply Additive.toMul.injective
    simp [projectedCandidateSClassObstruction827,
      projectedCandidateAtDetectorSupport827,
      qRelaxedReflectedProjector827]

@[simp]
theorem projectedClassObstructionAddHom827_apply
    (source : QRelaxedSelmerCarrier827 K) :
    Additive.toMul
        (projectedClassObstructionAddHom827 rhoQ omega chi source) =
      projectedCandidateSClassObstruction827 rhoQ omega chi source :=
  rfl

/-- The literal range of the post-projector relaxed class projection. -/
abbrev ProjectedClassRange827 :=
  AddMonoidHom.range (projectedClassObstructionAddHom827 rhoQ omega chi)

/-- Every element in the projected class range is killed by 59 because its
source lies in the 59-Selmer carrier. -/
theorem projectedClassRange827_nsmul_eq_zero
    (c : ProjectedClassRange827 rhoQ omega chi) : 59 • c = 0 := by
  rcases c.property with ⟨source, hsource⟩
  apply Subtype.ext
  change 59 • c.1 = 0
  rw [← hsource, ← map_nsmul]
  rw [SelmerEigenspace.p_nsmul_eq_zero]
  exact map_zero _

noncomputable instance instProjectedClassRange827ModuleZMod :
    Module (ZMod 59) (ProjectedClassRange827 rhoQ omega chi) :=
  AddCommGroup.zmodModule (projectedClassRange827_nsmul_eq_zero rhoQ omega chi)

/-- The surjective relaxed class projection required by `SteeringFiber`.
Range restriction is bookkeeping, not a splitting. -/
noncomputable def relaxedClassProjection827 :
    SurjectiveLinearMap (ZMod 59)
      (QRelaxedSelmerCarrier827 K)
      (ProjectedClassRange827 rhoQ omega chi) where
  toLinearMap :=
    (projectedClassObstructionAddHom827 rhoQ omega chi).rangeRestrict
      |>.toZModLinearMap 59
  surjective :=
    by
      simpa only [AddMonoidHom.coe_toZModLinearMap] using
        (AddMonoidHom.rangeRestrict_surjective
          (projectedClassObstructionAddHom827 rhoQ omega chi))

/-- The remaining q-places after one pointed place has been selected. -/
abbrev NonpointedPlace827
    (selectedPlace : {v // v ∈ placesOver827 K}) :=
  {v : {v // v ∈ placesOver827 K} // v ≠ selectedPlace}

/-- The carrier of all nonpointed q-localization readings. -/
abbrev NonpointedReadings827
    (selectedPlace : {v // v ∈ placesOver827 K}) :=
  NonpointedPlace827 selectedPlace → ZMod 59

/-- The pointed localization after the genuine reflected projector. -/
noncomputable def pointedCoordinateAddHom827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    QRelaxedSelmerCarrier827 K →+ ZMod 59 :=
  (qLocalizationCoordinate827 rhoQ omega chi selectedPlace).comp
    (qRelaxedReflectedProjector827 rhoQ omega chi).toAddMonoidHom

/-- The pointed localization as a `ZMod 59`-linear functional. -/
noncomputable def pointedCoordinate827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    QRelaxedSelmerCarrier827 K →ₗ[ZMod 59] ZMod 59 :=
  (pointedCoordinateAddHom827 rhoQ omega chi selectedPlace).toZModLinearMap 59

/-- Every other q-coordinate after projection, packaged as one silence map.
An actual tame-symbol comparison is still the downstream
`SelectedTameComparison`; this map records the localization silence which
that comparison must realize. -/
noncomputable def tameSilenceAddHom827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    QRelaxedSelmerCarrier827 K →+ NonpointedReadings827 selectedPlace :=
  AddMonoidHom.pi fun v ↦
    pointedCoordinateAddHom827 rhoQ omega chi v.1

/-- The nonpointed tame-localization silence map. -/
noncomputable def tameSilence827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    QRelaxedSelmerCarrier827 K →ₗ[ZMod 59]
      NonpointedReadings827 selectedPlace :=
  (tameSilenceAddHom827 rhoQ omega chi selectedPlace).toZModLinearMap 59

@[simp]
theorem pointedCoordinate827_apply
    (selectedPlace : {v // v ∈ placesOver827 K})
    (source : QRelaxedSelmerCarrier827 K) :
    pointedCoordinate827 rhoQ omega chi selectedPlace source =
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace
        (qRelaxedReflectedProjector827 rhoQ omega chi source) :=
  rfl

@[simp]
theorem tameSilence827_apply
    (selectedPlace : {v // v ∈ placesOver827 K})
    (source : QRelaxedSelmerCarrier827 K)
    (v : NonpointedPlace827 selectedPlace) :
    tameSilence827 rhoQ omega chi selectedPlace source v =
      qLocalizationCoordinate827 rhoQ omega chi v.1
        (qRelaxedReflectedProjector827 rhoQ omega chi source) :=
  rfl

/-! ## The 48-scaled gauge has the same branch as the pointed coordinate -/

/-- The capacity-scaled gauge output attached to the pointed coordinate. -/
noncomputable def gaugeReading827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    QRelaxedSelmerCarrier827 K →ₗ[ZMod 59] ZMod 59 :=
  (firstLampScale827.comp
      (pointedCoordinateAddHom827 rhoQ omega chi selectedPlace)).toZModLinearMap 59

@[simp]
theorem gaugeReading827_apply
    (selectedPlace : {v // v ∈ placesOver827 K})
    (source : QRelaxedSelmerCarrier827 K) :
    gaugeReading827 rhoQ omega chi selectedPlace source =
      pointedCoordinate827 rhoQ omega chi selectedPlace source *
        firstLampReading827 :=
  rfl

theorem gaugeReading827_ne_zero_iff
    (selectedPlace : {v // v ∈ placesOver827 K})
    (source : QRelaxedSelmerCarrier827 K) :
    gaugeReading827 rhoQ omega chi selectedPlace source ≠ 0 ↔
      pointedCoordinate827 rhoQ omega chi selectedPlace source ≠ 0 := by
  rw [gaugeReading827_apply, mul_ne_zero_iff]
  simp [firstLampReading827_ne_zero]

/-! ## Expanded kernel computation -/

theorem relaxedClassProjection827_eq_zero_iff
    (source : QRelaxedSelmerCarrier827 K) :
    relaxedClassProjection827 rhoQ omega chi source = 0 ↔
      projectedCandidateSClassObstruction827 rhoQ omega chi source = 1 := by
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    change projectedClassObstructionAddHom827 rhoQ omega chi source = 0 at hval
    exact Additive.toMul.injective hval
  · intro h
    apply Subtype.ext
    change projectedClassObstructionAddHom827 rhoQ omega chi source = 0
    exact Additive.toMul.injective h

theorem tameSilence827_eq_zero_iff
    (selectedPlace : {v // v ∈ placesOver827 K})
    (source : QRelaxedSelmerCarrier827 K) :
    tameSilence827 rhoQ omega chi selectedPlace source = 0 ↔
      ∀ v : NonpointedPlace827 selectedPlace,
        qLocalizationCoordinate827 rhoQ omega chi v.1
          (qRelaxedReflectedProjector827 rhoQ omega chi source) = 0 := by
  constructor
  · intro h v
    exact congrFun h v
  · intro h
    funext v
    exact h v

/-! ## The retained pointed conormal class -/

/-- The quotient carrier of the pointed functional modulo the dual image of
the joint `(relaxed class, nonpointed localization)` constraint. -/
abbrev PointedConormalCokernel827
    (selectedPlace : {v // v ∈ placesOver827 K}) :=
  FocusConormalCokernel
    (relaxedClassProjection827 rhoQ omega chi)
    (tameSilence827 rhoQ omega chi selectedPlace)

/-- The actual pointed conormal coordinate.  Its old Boolean branch is only
the zero/nonzero shadow recorded below. -/
def pointedConormalClass827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    PointedConormalCokernel827 rhoQ omega chi selectedPlace :=
  focusConormalClass
    (relaxedClassProjection827 rhoQ omega chi)
    (tameSilence827 rhoQ omega chi selectedPlace)
    (pointedCoordinate827 rhoQ omega chi selectedPlace)

/-- The restriction presentation of the same pointed conormal coordinate. -/
def pointedConormalRestriction827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    Module.Dual (ZMod 59)
      (K_T
        (relaxedClassProjection827 rhoQ omega chi)
        (tameSilence827 rhoQ omega chi selectedPlace)) :=
  focusConormalRestriction
    (relaxedClassProjection827 rhoQ omega chi)
    (tameSilence827 rhoQ omega chi selectedPlace)
    (pointedCoordinate827 rhoQ omega chi selectedPlace)

/-- The pointed condition is fixed exactly when its retained class vanishes. -/
theorem pointedConormalClass827_eq_zero_iff_fixed
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    pointedConormalClass827 rhoQ omega chi selectedPlace = 0 ↔
      FixedAttention
        (relaxedClassProjection827 rhoQ omega chi)
        (tameSilence827 rhoQ omega chi selectedPlace)
        (pointedCoordinate827 rhoQ omega chi selectedPlace) :=
  focusConormalClass_eq_zero_iff_fixed _ _ _

/-- Nonvanishing of the pointed class is precisely the existence of a
transverse direction. -/
theorem pointedConormalClass827_ne_zero_iff_transverse
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    pointedConormalClass827 rhoQ omega chi selectedPlace ≠ 0 ↔
      Nonempty
        (TransverseDirection
          (relaxedClassProjection827 rhoQ omega chi)
          (tameSilence827 rhoQ omega chi selectedPlace)
          (pointedCoordinate827 rhoQ omega chi selectedPlace)) :=
  focusConormalClass_ne_zero_iff_transverse _ _ _

/-- The exact missing kernel computation, expanded without affine language.
It asks for a pure pointed q-direction with trivial projected finite-`S`
class and every nonpointed q-coordinate silent. -/
theorem transverseDirection_iff_exists_pointedKernel
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    Nonempty
        (TransverseDirection
          (relaxedClassProjection827 rhoQ omega chi)
          (tameSilence827 rhoQ omega chi selectedPlace)
          (pointedCoordinate827 rhoQ omega chi selectedPlace)) ↔
      ∃ k : QRelaxedSelmerCarrier827 K,
        projectedCandidateSClassObstruction827 rhoQ omega chi k = 1 ∧
        (∀ v : NonpointedPlace827 selectedPlace,
          qLocalizationCoordinate827 rhoQ omega chi v.1
            (qRelaxedReflectedProjector827 rhoQ omega chi k) = 0) ∧
        qLocalizationCoordinate827 rhoQ omega chi selectedPlace
          (qRelaxedReflectedProjector827 rhoQ omega chi k) ≠ 0 := by
  constructor
  · rintro ⟨k⟩
    refine ⟨k.direction, ?_, ?_, ?_⟩
    · exact (relaxedClassProjection827_eq_zero_iff rhoQ omega chi _).mp
        (LinearMap.mem_ker.mp k.direction_mem.1)
    · exact (tameSilence827_eq_zero_iff rhoQ omega chi selectedPlace _).mp
        (LinearMap.mem_ker.mp k.direction_mem.2)
    · exact k.reading_ne_zero
  · rintro ⟨k, hclass, hsilence, hpointed⟩
    exact ⟨
      { direction := k
        direction_mem := ⟨
          LinearMap.mem_ker.mpr
            ((relaxedClassProjection827_eq_zero_iff rhoQ omega chi _).mpr hclass),
          LinearMap.mem_ker.mpr
            ((tameSilence827_eq_zero_iff rhoQ omega chi selectedPlace _).mpr
              hsilence)⟩
        reading_ne_zero := hpointed }⟩

/-- The two mathematical branches are exhaustive, but this theorem does not
reduce to one named arithmetic branch without the missing kernel
calculation. -/
theorem pointedKernel_logical_dichotomy
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    FixedAttention
        (relaxedClassProjection827 rhoQ omega chi)
        (tameSilence827 rhoQ omega chi selectedPlace)
        (pointedCoordinate827 rhoQ omega chi selectedPlace) ∨
      Nonempty
        (TransverseDirection
          (relaxedClassProjection827 rhoQ omega chi)
          (tameSilence827 rhoQ omega chi selectedPlace)
          (pointedCoordinate827 rhoQ omega chi selectedPlace)) :=
  fixed_or_steerable _ _ _

/-! ## Conditional consequences of each branch -/

/-- The zero source is the canonical compatible lift of the zero projected
class with all nonpointed readings silent. -/
noncomputable def zeroCompatibleLift827
    (selectedPlace : {v // v ∈ placesOver827 K}) :
    CompatibleLift
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace) 0 where
  point := 0
  class_receipt := map_zero _
  silence_receipt := map_zero _

/-- In the steerable branch, focus the zero compatible lift to pointed
coordinate one.  Its embedded `FocusedLift` carries the three algebraic
receipts. -/
noncomputable def focusedUnitLift827
    (selectedPlace : {v // v ∈ placesOver827 K})
    (k : TransverseDirection
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace)) :
    FocusedLift
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace)
      (zeroCompatibleLift827 rhoQ omega chi selectedPlace) 1 :=
  focusedLift _ _ _ (zeroCompatibleLift827 rhoQ omega chi selectedPlace) k 1

/-- The primitive's focused lift discharges the old joint `hcoord`/`hobs`
wall and therefore constructs the honest q-relaxed localization lift. -/
noncomputable def localizationLiftOfTransverse827
    (selectedPlace : {v // v ∈ placesOver827 K})
    (k : TransverseDirection
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace)) :
    ReflectedQRelaxedLocalizationLift827 rhoQ omega chi := by
  let focused := focusedUnitLift827 rhoQ omega chi selectedPlace k
  apply ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
    focused.point selectedPlace
  · have hreading := focused.exact_steering_amount
    change qLocalizationCoordinate827 rhoQ omega chi selectedPlace
        (qRelaxedReflectedProjector827 rhoQ omega chi focused.point) = 1 at hreading
    rw [hreading]
    exact one_ne_zero
  · apply (relaxedClassProjection827_eq_zero_iff rhoQ omega chi _).mp
    calc
      relaxedClassProjection827 rhoQ omega chi focused.point =
          relaxedClassProjection827 rhoQ omega chi
            (zeroCompatibleLift827 rhoQ omega chi selectedPlace).point :=
        focused.class_preservation
      _ = 0 := map_zero _

/-- Complete conditional steerable receipt: the W1 focused lift, the honest
q-relaxed lift it induces, their common source, and the gauge output `48`. -/
structure SteerableGaugeReceipt827
    (selectedPlace : {v // v ∈ placesOver827 K})
    (k : TransverseDirection
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace)) where
  focused : FocusedLift
    (relaxedClassProjection827 rhoQ omega chi)
    (tameSilence827 rhoQ omega chi selectedPlace)
    (pointedCoordinate827 rhoQ omega chi selectedPlace)
    (zeroCompatibleLift827 rhoQ omega chi selectedPlace) 1
  localizationLift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi
  source_matches : localizationLift.source = focused.point
  gauge_output :
    gaugeReading827 rhoQ omega chi selectedPlace focused.point =
      firstLampReading827

/-- If the missing kernel direction is supplied, the gauge reading falls out
as the output of the generic invariant rather than hand steering. -/
noncomputable def steerableGaugeReceipt827
    (selectedPlace : {v // v ∈ placesOver827 K})
    (k : TransverseDirection
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace)) :
    SteerableGaugeReceipt827 rhoQ omega chi selectedPlace k := by
  let focused := focusedUnitLift827 rhoQ omega chi selectedPlace k
  let lift := localizationLiftOfTransverse827 rhoQ omega chi selectedPlace k
  refine
    { focused := focused
      localizationLift := lift
      source_matches := rfl
      gauge_output := ?_ }
  rw [gaugeReading827_apply, focused.exact_steering_amount, one_mul]

/-- In the fixed branch, the pointed detector is a pullback from the
projected relaxed class on the silent slice. -/
noncomputable def fixedPointedClassReadout827
    (selectedPlace : {v // v ∈ placesOver827 K})
    (fixed : FixedAttention
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace)) :
    Module.Dual (ZMod 59) (ProjectedClassRange827 rhoQ omega chi) :=
  rhoDual _ _ _ fixed

theorem fixedPointedReadout_pullback
    (selectedPlace : {v // v ∈ placesOver827 K})
    (fixed : FixedAttention
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace))
    (source : QRelaxedSelmerCarrier827 K)
    (hsilence : tameSilence827 rhoQ omega chi selectedPlace source = 0) :
    fixedPointedClassReadout827 rhoQ omega chi selectedPlace fixed
        (relaxedClassProjection827 rhoQ omega chi source) =
      pointedCoordinate827 rhoQ omega chi selectedPlace source :=
  rhoDual_pullback_of_silence _ _ _ fixed source hsilence

/-- The fixed branch changes the detector interpretation: among sources
with the same projected class and nonpointed silence, the scaled gauge is
preimage-independent rather than steerable. -/
theorem fixedGauge_preimage_independent
    (selectedPlace : {v // v ∈ placesOver827 K})
    (fixed : FixedAttention
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
      (pointedCoordinate827 rhoQ omega chi selectedPlace))
    {x y : QRelaxedSelmerCarrier827 K}
    (hclass : relaxedClassProjection827 rhoQ omega chi x =
      relaxedClassProjection827 rhoQ omega chi y)
    (hx : tameSilence827 rhoQ omega chi selectedPlace x = 0)
    (hy : tameSilence827 rhoQ omega chi selectedPlace y = 0) :
    gaugeReading827 rhoQ omega chi selectedPlace x =
      gaugeReading827 rhoQ omega chi selectedPlace y := by
  rw [gaugeReading827_apply, gaugeReading827_apply]
  rw [reading_preimage_independent _ _ _ fixed hclass hx hy]

/-! ## Present-machinery verdict -/

/-- Kernel computations inventoried for the W2 decision. -/
inductive KernelComputationKind
  | projectedFiniteSClassKernel
  | fullSupportedLocalizationKernel
  | pointedClassSilenceIntersection
  deriving DecidableEq, Repr

/-- Whether the current cone contains the corresponding computation. -/
def hasKernelComputation : KernelComputationKind → Bool
  | .projectedFiniteSClassKernel => true
  | .fullSupportedLocalizationKernel => true
  | .pointedClassSilenceIntersection => false

/-- The three requested W2 outcomes. -/
inductive Pointed827BranchStatus
  | fixed
  | steerable
  | undecidable
  deriving DecidableEq, Repr

/-- The current inventory needed to choose a named W2 branch. -/
def currentKernelInventory : List KernelComputationKind :=
  [.projectedFiniteSClassKernel, .fullSupportedLocalizationKernel,
    .pointedClassSilenceIntersection]

/-- Whether the current inventory contains every required kernel
calculation. -/
def kernelInventoryComplete (inventory : List KernelComputationKind) : Bool :=
  inventory.all hasKernelComputation

/-- Coverage-level branch decision from actual named branch receipts. -/
def branchStatus (hasFixedReceipt hasSteerableReceipt : Bool) :
    Pointed827BranchStatus :=
  if hasSteerableReceipt then .steerable
  else if hasFixedReceipt then .fixed
  else .undecidable

/-- Neither arithmetic branch receipt is supplied by the current cone. -/
def currentFixedReceiptAvailable : Bool := false

def currentSteerableReceiptAvailable : Bool := false

theorem current_kernelInventory_incomplete :
    kernelInventoryComplete currentKernelInventory = false := by
  rfl

/-- **W2 verdict: undecidable with present machinery.**  This records the
missing pointed kernel computation and does not claim mathematical
nonexistence of either branch. -/
theorem current_branchStatus_eq_undecidable :
    branchStatus currentFixedReceiptAvailable currentSteerableReceiptAvailable =
      .undecidable := by
  rfl

end Fermat.FiftyNine.Conservation.GaugeSteering827
