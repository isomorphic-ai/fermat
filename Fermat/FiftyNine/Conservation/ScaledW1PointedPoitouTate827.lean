/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The single retained normalization scale in the W1 plus 827 PT lift

Normalizing the selected 827 coordinate to one leaves one honest freedom:
the lambda-local reflected factor may be a nonzero scalar multiple of W1's
retained factor.  This file records that scale as a unit and proves the
corresponding two-charge Poitou--Tate consumer.

If the W1 receipt functional is a unit multiple `v` of the normalized local
Frobenius functional, the unique cancelling wild scale is `-v⁻¹`.  The
missing reverse Poitou--Tate inclusion then produces an existential global
reflected lift with normalized 827 profile and precisely that lambda scale.
No lift is selected globally, and no reciprocity, PT, or Kummer--Artin
producer is introduced.
-/
import Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Fermat.FiftyNine.Conservation.ScaledW1PointedPoitouTate827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalW1PointedIncidenceBridge827
open CanonicalW1PoitouTateReduction827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LambdaOrbitAffineKernelCriterion827
open LambdaOrbitLocalizationFiber827
open LocalKummerFrobeniusFactorization827
open NormalizedContinuousKummerPairing59
open NormalizedFullOrbitEigenprofile827
open PointedTateIncidence
open SplitPrimeFourier827
open TwistedLambdaCupReceipt59
open UlamReadout827
open VostokovLocalization59
open WildOrbitBoundaryComparison827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem oldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact SelmerEigenspace.p_nsmul_eq_zero x.1

noncomputable local instance instOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule oldPrimal59_nsmul_eq_zero

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-- A reflected global class with normalized selected 827 coordinate and a
retained nonzero scale on W1's lambda-local reflected factor. -/
structure NormalizedOrbitScaledWildLift827 where
  wildScale : (ZMod 59)ˣ
  carrier : QRelaxedReflectedDual827
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    canonicalTeichmullerCharacter59 irregularCharacter59
  lambda_eq :
    lambdaReflectedLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 carrier =
      (wildScale : ZMod 59) • (twistedLambdaCupReceipt59 K).reflected
  selected_eq :
    reflectedPointedLocalization827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) carrier = 1

/-- The selected-coordinate normalization propagates to the entire genuine
58-place reflected eigenprofile. -/
theorem NormalizedOrbitScaledWildLift827.fullOrbit
    (lift : NormalizedOrbitScaledWildLift827 (K := K))
    (tau : GaloisIndex59) :
    relaxedOrbitValuation827 K tau lift.carrier.1 =
      normalizedFullOrbitEigenprofileCoordinates827
        canonicalTeichmullerCharacter59 irregularCharacter59 tau := by
  rw [relaxedOrbitValuation827_eq_profile_mul_selected,
    lift.selected_eq, mul_one]

/-- Forgetting the wild scale gives an actual point of W3's normalized
reflected fiber. -/
noncomputable def NormalizedOrbitScaledWildLift827.toNormalizedReflectedFiber827
    (lift : NormalizedOrbitScaledWildLift827 (K := K)) :
    NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) :=
  ⟨lift.carrier, by
    rw [reflectedBoundaryFunctional827_apply]
    exact lift.selected_eq⟩

/-- Evaluating the two-charge boundary at a scaled W1 factor and normalized
827 coordinate gives the correspondingly scaled W1 receipt plus the local
Frobenius functional. -/
theorem lambdaPointedPoitouTateBoundary827_scaledReceipt_one
    (scale : ZMod 59) :
    lambdaPointedPoitouTateBoundary827 (K := K)
        (scale • (twistedLambdaCupReceipt59 K).reflected, 1) =
      scale • w1ReceiptPrimalBoundaryFunctional827 (K := K) +
        irregularPrimalFrobeniusFunctional827 (K := K) := by
  apply LinearMap.ext
  intro x
  simp only [lambdaPointedPoitouTateBoundary827_apply, one_mul,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_smul]
  rfl

/-- The unit scale which cancels a comparison
`W1 receipt = v * Frobenius` while the selected 827 coordinate stays one. -/
def cancelingWildScale827 (v : (ZMod 59)ˣ) : (ZMod 59)ˣ :=
  -v⁻¹

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem cancelingWildScale827_mul (v : (ZMod 59)ˣ) :
    ((cancelingWildScale827 v : (ZMod 59)ˣ) : ZMod 59) * (v : ZMod 59) = -1 := by
  unfold cancelingWildScale827
  rw [Units.val_neg, Units.val_inv_eq_inv_val, neg_mul,
    inv_mul_cancel₀ (Units.ne_zero v)]

/-- A supplied cancellation at a nonzero wild scale and the reverse PT
inclusion produce an existential normalized-orbit, scaled-wild lift. -/
theorem nonempty_normalizedOrbitScaledWildLift827_of_boundary_cancels
    (kernel_lifts :
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaPointedLocalization827 (K := K)))
    (scale : (ZMod 59)ˣ)
    (cancels :
      lambdaPointedPoitouTateBoundary827 (K := K)
        ((scale : ZMod 59) • (twistedLambdaCupReceipt59 K).reflected, 1) = 0) :
    Nonempty (NormalizedOrbitScaledWildLift827 (K := K)) := by
  obtain ⟨y, hlambda, hselected⟩ :=
    exists_reflected_lift_of_pt_kernel_lifts_of_boundary_cancels
      (K := K) kernel_lifts
      ((scale : ZMod 59) • (twistedLambdaCupReceipt59 K).reflected) 1 cancels
  exact ⟨⟨scale, y, hlambda, hselected⟩⟩

/-- **Scaled PT consumer.**  Unit proportionality of the W1 and 827
functionals is enough: exact equality with coefficient `-1` is unnecessary.
The inverse unit is retained as the lambda-local wild scale. -/
theorem nonempty_normalizedOrbitScaledWildLift827_of_pt_and_unitComparison
    (kernel_lifts :
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaPointedLocalization827 (K := K)))
    (comparisonUnit : (ZMod 59)ˣ)
    (comparison :
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        (comparisonUnit : ZMod 59) •
          irregularPrimalFrobeniusFunctional827 (K := K)) :
    Nonempty (NormalizedOrbitScaledWildLift827 (K := K)) := by
  let scale := cancelingWildScale827 comparisonUnit
  apply nonempty_normalizedOrbitScaledWildLift827_of_boundary_cancels
    (K := K) kernel_lifts scale
  rw [lambdaPointedPoitouTateBoundary827_scaledReceipt_one, comparison,
    smul_smul, cancelingWildScale827_mul]
  simp

/-- The wild boundary of a scaled lift is exactly the retained scale times
W1's receipt functional. -/
theorem NormalizedOrbitScaledWildLift827.wildBoundary_eq_scaledReceipt
    (lift : NormalizedOrbitScaledWildLift827 (K := K)) :
    seatedWildBoundaryFunctional59 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift.carrier =
      (lift.wildScale : ZMod 59) •
        w1ReceiptPrimalBoundaryFunctional827 (K := K) := by
  apply LinearMap.ext
  intro x
  rw [seatedWildBoundaryFunctional59_apply,
    normalizedLambdaGlobalPairing59_eq_localized_factor_cup,
    ← lambdaReflectedLocalization827_apply, lift.lambda_eq,
    LinearMap.smul_apply, w1ReceiptPrimalBoundaryFunctional827_apply]
  rw [(lambdaContinuousCup59 K
      (lambdaPrimalFactorOfGlobalKummer59 (K := K)
        (toKummerClass x))).map_smul,
    (normalizedInflationReadout59 K).map_smul]

/-- Its normalized orbit boundary is the genuine local Frobenius functional. -/
theorem NormalizedOrbitScaledWildLift827.orbitBoundary_eq_frobenius
    (lift : NormalizedOrbitScaledWildLift827 (K := K)) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift.carrier =
      irregularPrimalFrobeniusFunctional827 (K := K) := by
  apply LinearMap.ext
  intro x
  rw [seatedOrbitBoundaryFunctional827_eq_selected_mul_localFrobenius,
    lift.selected_eq, one_mul,
    irregularPrimalFrobeniusFunctional827_apply]

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.ScaledW1PointedPoitouTate827.lambdaPointedPoitouTateBoundary827_scaledReceipt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaPointedPoitouTateBoundary827_scaledReceipt_one

/--
info: 'Fermat.FiftyNine.Conservation.ScaledW1PointedPoitouTate827.nonempty_normalizedOrbitScaledWildLift827_of_pt_and_unitComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_normalizedOrbitScaledWildLift827_of_pt_and_unitComparison

/--
info: 'Fermat.FiftyNine.Conservation.ScaledW1PointedPoitouTate827.NormalizedOrbitScaledWildLift827.wildBoundary_eq_scaledReceipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizedOrbitScaledWildLift827.wildBoundary_eq_scaledReceipt

end Fermat.FiftyNine.Conservation.ScaledW1PointedPoitouTate827
