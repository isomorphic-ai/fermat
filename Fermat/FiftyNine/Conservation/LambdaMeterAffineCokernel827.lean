/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The affine cokernel obstruction for one lambda meter

The meter-parametric Poitou--Tate engine originally exposed the complete
reverse inclusion `ker boundary <= range localization`.  That statement is
stronger than the one lift used by the 7A route.  Once a normalized point of
the 827 fiber is retained, a fixed unit scale globalizes precisely when one
explicit lambda correction lies in the localization range of orbit-invisible
adjustments.

This file records that exact obstruction as a quotient class.  It is
independent of the retained normalized basepoint, and its vanishing is
equivalent to existence of an actual normalized global meter lift at the
specified scale.  No lift is selected, no cokernel is split, and no
Poitou--Tate exactness or vanishing theorem is asserted.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.FiftyNine.Conservation.LambdaMeterPointedPoitouTate827
import Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.LambdaMeterAffineCokernel827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CanonicalW1PointedIncidenceBridge827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LambdaMeterPointedPoitouTate827
open LambdaOrbitAffineCokernel827
open LambdaOrbitAffineKernelCriterion827
open LambdaOrbitLocalizationFiber827
open PointedTateIncidence
open SplitPrimeFourier827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-! ## The fixed-scale obstruction -/

/-- The correction between a prescribed scaled lambda meter and the lambda
localization of one retained normalized 827 point. -/
noncomputable def scaledLambdaMeterCorrection827
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    LambdaRootsContinuousH1 K :=
  scale • meter -
    lambdaReflectedLocalization827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀.1

/-- The scaled meter and the normalized 827 fiber are compared in the
literal cokernel of lambda localization on full-orbit-invisible global
adjustments. -/
noncomputable def scaledLambdaMeterObstructionClass827
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    W1LambdaCokernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  w1LambdaCokernelProjection827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59
    (scaledLambdaMeterCorrection827 (K := K) meter scale y₀)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The scaled-meter obstruction is the difference of the prescribed meter
coset and the already-realized normalized 827 coset. -/
theorem scaledLambdaMeterObstructionClass827_eq_meter_sub_normalized
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterObstructionClass827 (K := K) meter scale y₀ =
      w1LambdaCokernelProjection827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (scale • meter) -
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  simp [scaledLambdaMeterObstructionClass827,
    scaledLambdaMeterCorrection827, normalizedW3LambdaCoset827,
    w1LambdaCokernelProjection827]

/-- Changing the normalized 827 basepoint changes the representative only
by a restricted lambda image, hence leaves the meter obstruction unchanged. -/
theorem scaledLambdaMeterObstructionClass827_eq
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterObstructionClass827 (K := K) meter scale y₀ =
      scaledLambdaMeterObstructionClass827 (K := K) meter scale y₁ := by
  rw [scaledLambdaMeterObstructionClass827_eq_meter_sub_normalized,
    scaledLambdaMeterObstructionClass827_eq_meter_sub_normalized,
    normalizedW3LambdaCoset827_eq
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀ y₁]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Quotient vanishing is exactly membership of the explicit affine
correction in the restricted lambda range. -/
theorem scaledLambdaMeterObstructionClass827_eq_zero_iff_mem_range
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterObstructionClass827 (K := K) meter scale y₀ = 0 ↔
      scaledLambdaMeterCorrection827 (K := K) meter scale y₀ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59) := by
  change
    (Submodule.Quotient.mk
      (scaledLambdaMeterCorrection827 (K := K) meter scale y₀) :
        W1LambdaCokernel827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

/-- The correction-range criterion itself is independent of which
normalized 827 point was retained. -/
theorem scaledLambdaMeterCorrection827_mem_range_iff_basepoint
    (meter : LambdaRootsContinuousH1 K) (scale : ZMod 59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterCorrection827 (K := K) meter scale y₀ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59) ↔
      scaledLambdaMeterCorrection827 (K := K) meter scale y₁ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59) := by
  rw [← scaledLambdaMeterObstructionClass827_eq_zero_iff_mem_range,
    ← scaledLambdaMeterObstructionClass827_eq_zero_iff_mem_range,
    scaledLambdaMeterObstructionClass827_eq meter scale y₀ y₁]

/-! ## Exact lift criterion -/

/-- A lift at a fixed unit scale yields exactly the corresponding affine
correction in the orbit-kernel lambda range. -/
theorem scaledLambdaMeterCorrection827_mem_range_of_lift
    (meter : LambdaRootsContinuousH1 K)
    (lift : NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    scaledLambdaMeterCorrection827 (K := K) meter
        (lift.wildScale : ZMod 59) y₀ ∈
      LinearMap.range
        (lambdaOnFullOrbitKernel827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59) := by
  let z : FullOrbitValuationKernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 := ⟨
    lift.carrier - y₀.1, by
      change fullOrbitValuationLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59
          (lift.carrier - y₀.1) = 0
      apply (fullOrbitValuationLocalization827_eq_zero_iff_selected_eq_zero
        (K := K) (lift.carrier - y₀.1)).2
      rw [map_sub, lift.selected_eq]
      have hy₀ :
          reflectedPointedLocalization827
              (cyclotomicQRelaxedSelmerRepresentation827 K)
              canonicalTeichmullerCharacter59 irregularCharacter59
              (tameOrbitBasePlace827 (K := K)) y₀.1 = 1 := by
        simpa only [reflectedBoundaryFunctional827_apply] using y₀.2
      rw [hy₀, sub_self]
  ⟩
  refine ⟨z, ?_⟩
  change lambdaReflectedLocalization827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (lift.carrier - y₀.1) =
    scaledLambdaMeterCorrection827 (K := K) meter
      (lift.wildScale : ZMod 59) y₀
  rw [map_sub]
  have hlambda := congrArg Subtype.val lift.lambda_eq
  change lambdaReflectedLocalization827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 lift.carrier =
    (lift.wildScale : ZMod 59) • meter at hlambda
  rw [hlambda]
  rfl

/-- Conversely, one orbit-invisible correction constructs an actual global
lift at the specified unit scale.  The result is a value inside an
existential proof, not a globally selected representative. -/
theorem exists_normalizedOrbitScaledLambdaMeterLift827_of_correction_mem_range
    (meter : LambdaRootsContinuousH1 K) (scale : (ZMod 59)ˣ)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (correction_mem :
      scaledLambdaMeterCorrection827 (K := K) meter (scale : ZMod 59) y₀ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59)) :
    ∃ lift : NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter,
      lift.wildScale = scale := by
  obtain ⟨z, hz⟩ := correction_mem
  let carrier := y₀.1 + z.1
  have hzSelected :
      reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) z.1 = 0 := by
    apply (fullOrbitValuationLocalization827_eq_zero_iff_selected_eq_zero
      (K := K) z.1).1
    exact z.2
  have hy₀ :
      reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y₀.1 = 1 := by
    simpa only [reflectedBoundaryFunctional827_apply] using y₀.2
  refine ⟨⟨scale, carrier, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change lambdaReflectedLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 carrier =
      (scale : ZMod 59) • meter
    change lambdaReflectedLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (y₀.1 + z.1) = _
    rw [map_add]
    change lambdaReflectedLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 z.1 =
      scaledLambdaMeterCorrection827 (K := K) meter (scale : ZMod 59) y₀ at hz
    rw [hz]
    simp [scaledLambdaMeterCorrection827]
  · change reflectedPointedLocalization827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) (y₀.1 + z.1) = 1
    rw [map_add, hy₀, hzSelected, add_zero]

/-- **Sharp fixed-scale globalization criterion.**  A normalized global
meter lift with prescribed unit scale exists exactly when its one literal
cokernel obstruction vanishes. -/
theorem exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff
    (meter : LambdaRootsContinuousH1 K) (scale : (ZMod 59)ˣ)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    (∃ lift : NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter,
        lift.wildScale = scale) ↔
      scaledLambdaMeterObstructionClass827 (K := K) meter
        (scale : ZMod 59) y₀ = 0 := by
  rw [scaledLambdaMeterObstructionClass827_eq_zero_iff_mem_range]
  constructor
  · rintro ⟨lift, rfl⟩
    exact scaledLambdaMeterCorrection827_mem_range_of_lift meter lift y₀
  · exact exists_normalizedOrbitScaledLambdaMeterLift827_of_correction_mem_range
      meter scale y₀

/-- Allowing the one honest unit normalization freedom turns the former
full reverse-PT premise into existence of a scale whose explicit cokernel
class vanishes. -/
theorem nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale
    (meter : LambdaRootsContinuousH1 K)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (NormalizedOrbitScaledLambdaMeterLift827 (K := K) meter) ↔
      ∃ scale : (ZMod 59)ˣ,
        scaledLambdaMeterObstructionClass827 (K := K) meter
          (scale : ZMod 59) y₀ = 0 := by
  constructor
  · rintro ⟨lift⟩
    refine ⟨lift.wildScale, ?_⟩
    exact (exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff
      meter lift.wildScale y₀).1 ⟨lift, rfl⟩
  · rintro ⟨scale, hscale⟩
    obtain ⟨lift, _⟩ :=
      (exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff
        meter scale y₀).2 hscale
    exact ⟨lift⟩

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaMeterAffineCokernel827.scaledLambdaMeterObstructionClass827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scaledLambdaMeterObstructionClass827_eq

/--
info: 'Fermat.FiftyNine.Conservation.LambdaMeterAffineCokernel827.scaledLambdaMeterCorrection827_mem_range_of_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scaledLambdaMeterCorrection827_mem_range_of_lift

/--
info: 'Fermat.FiftyNine.Conservation.LambdaMeterAffineCokernel827.exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff

/--
info: 'Fermat.FiftyNine.Conservation.LambdaMeterAffineCokernel827.nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale

/- The fixed-scale criterion is assembled from the literal quotient
criterion and the two existential directions. -/
#guard_depends_on
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff,
  scaledLambdaMeterObstructionClass827_eq_zero_iff_mem_range

#guard_depends_on
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff,
  scaledLambdaMeterCorrection827_mem_range_of_lift

#guard_depends_on
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff,
  exists_normalizedOrbitScaledLambdaMeterLift827_of_correction_mem_range

/- Allowing the unit scale is only existential packaging of the fixed-scale
criterion. -/
#guard_depends_on
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale,
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff

/- The sharp criterion does not consume the former full reverse-PT
inclusion or its conditional lift constructor. -/
#guard_not_depends_on
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff,
  lambdaMeterPointedLocalization827_range_eq_ker_iff_kernel_lifts

#guard_not_depends_on
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff,
  nonempty_scaledLambdaMeterLift827_of_pt_and_unitComparison

end Fermat.FiftyNine.Conservation.LambdaMeterAffineCokernel827
