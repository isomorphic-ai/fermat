/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The W1 plus 827 Poitou--Tate boundary on its required local carrier

The first compiler-visible W1 plus `827` Poitou--Tate boundary used the
whole ambient `LambdaRootsContinuousH1 K` as its wild local term.  That
ambient object is larger than the local reflected quotient requested by
`7A-ARTIN-READ.md`.

This file makes the honest refinement already justified by the repository:
the wild term is restricted to `lambdaReflectedRequiredCarrier827`, the
smallest submodule containing every genuine reflected global localization
and W1's retained reflected receipt.  Thus the restriction makes no
character-seat claim, and it loses none of the local states actually used
by the proof.

On this exact carrier we define simultaneous lambda plus selected-`827`
localization and its two-charge boundary.  Global reciprocity proves the
easy inclusion `range <= kernel`; the reverse inclusion is isolated as the
literal remaining Poitou--Tate lifting seam.  The final consumer is
existential and retains the one allowed wild normalization scale.  No
action, covariance theorem, selected lift, provider, or arithmetic premise
is introduced.
-/
import Fermat.Exponents.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827
import Fermat.Exponents.FiftyNine.Conservation.ScaledW1PointedPoitouTate827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Fermat.FiftyNine.Conservation.RequiredCarrierW1PointedPoitouTate827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
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
open LambdaReflectedLocalSeatAudit827
open LocalKummerFrobeniusFactorization827
open NormalizedFullOrbitEigenprofile827
open PointedTateIncidence
open ScaledW1PointedPoitouTate827
open SplitPrimeFourier827
open TwistedLambdaCupReceipt59
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

/-! ## The honest restricted local term -/

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Every actual reflected q-relaxed localization belongs to the minimal
required local carrier. -/
theorem lambdaReflectedLocalization_mem_requiredCarrier827
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    lambdaReflectedLocalizationLinear827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y ∈
      lambdaReflectedRequiredCarrier827 (K := K) := by
  unfold lambdaReflectedRequiredCarrier827
  apply (le_sup_left :
    LinearMap.range
        (lambdaReflectedLocalizationLinear827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59) ≤ _)
  exact ⟨y, rfl⟩

/-- Genuine lambda localization with its codomain restricted to the
smallest currently justified reflected carrier. -/
noncomputable def lambdaReflectedRequiredLocalization827 :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59 →ₗ[ZMod 59]
      lambdaReflectedRequiredCarrier827 (K := K) where
  toFun y :=
    ⟨lambdaReflectedLocalizationLinear827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y,
      lambdaReflectedLocalization_mem_requiredCarrier827 (K := K) y⟩
  map_add' x y := by
    apply Subtype.ext
    exact (lambdaReflectedLocalizationLinear827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59).map_add x y
  map_smul' a y := by
    apply Subtype.ext
    exact (lambdaReflectedLocalizationLinear827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59).map_smul a y

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem lambdaReflectedRequiredLocalization827_apply_coe
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    (lambdaReflectedRequiredLocalization827 (K := K) y :
      LambdaRootsContinuousH1 K) =
        lambdaReflectedLocalization827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- W1's retained reflected receipt belongs to the same minimal carrier. -/
theorem twistedLambdaReceipt_mem_requiredCarrier827 :
    (twistedLambdaCupReceipt59 K).reflected ∈
      lambdaReflectedRequiredCarrier827 (K := K) := by
  unfold lambdaReflectedRequiredCarrier827
  apply (le_sup_right :
    Submodule.span (ZMod 59)
        {(twistedLambdaCupReceipt59 K).reflected} ≤ _)
  exact Submodule.subset_span (Set.mem_singleton _)

/-- W1's retained reflected receipt as an element of the honest local
carrier, rather than merely of ambient local `H¹`. -/
noncomputable def w1ReflectedRequiredReceipt827 :
    lambdaReflectedRequiredCarrier827 (K := K) :=
  ⟨(twistedLambdaCupReceipt59 K).reflected,
    twistedLambdaReceipt_mem_requiredCarrier827 (K := K)⟩

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem w1ReflectedRequiredReceipt827_coe :
    (w1ReflectedRequiredReceipt827 (K := K) :
      LambdaRootsContinuousH1 K) =
        (twistedLambdaCupReceipt59 K).reflected :=
  rfl

/-! ## Restricted simultaneous localization and boundary -/

/-- Simultaneous genuine localization into the required wild carrier and
the selected `827` coordinate. -/
noncomputable def lambdaRequiredPointedLocalization827 :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59 →ₗ[ZMod 59]
      (lambdaReflectedRequiredCarrier827 (K := K) × ZMod 59) :=
  (lambdaReflectedRequiredLocalization827 (K := K)).prod
    (reflectedPointedLocalization827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem lambdaRequiredPointedLocalization827_apply
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    lambdaRequiredPointedLocalization827 (K := K) y =
      (lambdaReflectedRequiredLocalization827 (K := K) y,
        reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y) :=
  rfl

/-- The two-charge PT boundary with the lambda input honestly restricted to
the minimal required carrier. -/
noncomputable def lambdaRequiredPointedPoitouTateBoundary827 :
    (lambdaReflectedRequiredCarrier827 (K := K) × ZMod 59) →ₗ[ZMod 59]
      Module.Dual (ZMod 59)
        (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59) where
  toFun state :=
    (irregularPrimalLambdaTestMap827 (K := K)).flip
        (state.1 : LambdaRootsContinuousH1 K) +
      state.2 • irregularPrimalFrobeniusFunctional827 (K := K)
  map_add' left right := by
    ext x
    simp
    ring
  map_smul' a state := by
    ext x
    simp
    ring

@[simp]
theorem lambdaRequiredPointedPoitouTateBoundary827_apply
    (state : lambdaReflectedRequiredCarrier827 (K := K) × ZMod 59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    lambdaRequiredPointedPoitouTateBoundary827 (K := K) state x =
      irregularPrimalLambdaTestMap827 (K := K) x
          (state.1 : LambdaRootsContinuousH1 K) +
        state.2 * irregularPrimalFrobeniusFunctional827 (K := K) x :=
  rfl

/-- Restriction changes only the type: the required-carrier boundary is the
ambient boundary evaluated after forgetting the subtype proof. -/
theorem lambdaRequiredPointedPoitouTateBoundary827_eq_ambient
    (state : lambdaReflectedRequiredCarrier827 (K := K) × ZMod 59) :
    lambdaRequiredPointedPoitouTateBoundary827 (K := K) state =
      lambdaPointedPoitouTateBoundary827 (K := K)
        ((state.1 : LambdaRootsContinuousH1 K), state.2) :=
  rfl

/-! ## The exact PT seam -/

/-- Global reciprocity proves the easy half of Poitou--Tate exactness on
the honest required carrier. -/
theorem lambdaRequiredPointedLocalization827_range_le_boundary_ker
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    LinearMap.range (lambdaRequiredPointedLocalization827 (K := K)) ≤
      LinearMap.ker
        (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) := by
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  have hambient :=
    lambdaPointedLocalization827_range_le_poitouTateBoundary_ker
      (K := K) reciprocity
      (show lambdaPointedLocalization827 (K := K) y ∈
        LinearMap.range (lambdaPointedLocalization827 (K := K)) from
          ⟨y, rfl⟩)
  rw [LinearMap.mem_ker] at hambient
  exact hambient

/-- Once reciprocity supplies `range <= kernel`, full exactness is
equivalent to the single missing reverse lifting inclusion.  This is the
literal required-carrier Poitou--Tate seam. -/
theorem lambdaRequiredPointedLocalization827_range_eq_ker_iff_kernel_lifts
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    LinearMap.range (lambdaRequiredPointedLocalization827 (K := K)) =
        LinearMap.ker
          (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) ↔
      LinearMap.ker
          (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaRequiredPointedLocalization827 (K := K)) := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm
      (lambdaRequiredPointedLocalization827_range_le_boundary_ker
        reciprocity)
      h

/-- Reverse PT exactness lifts any cancelling state in the honest local
carrier.  The result is existential; no global lift is selected. -/
theorem exists_reflected_lift_of_required_pt_kernel_lifts
    (kernel_lifts :
      LinearMap.ker
          (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaRequiredPointedLocalization827 (K := K)))
    (r : lambdaReflectedRequiredCarrier827 (K := K)) (a : ZMod 59)
    (cancels :
      lambdaRequiredPointedPoitouTateBoundary827 (K := K) (r, a) = 0) :
    ∃ y : QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59,
      lambdaReflectedRequiredLocalization827 (K := K) y = r ∧
        reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y = a := by
  have hker : (r, a) ∈
      LinearMap.ker
        (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) :=
    LinearMap.mem_ker.mpr cancels
  obtain ⟨y, hy⟩ := kernel_lifts hker
  refine ⟨y, congrArg Prod.fst hy, congrArg Prod.snd hy⟩

/-! ## The scaled W1 consumer on the honest carrier -/

/-- A normalized reflected global lift whose lambda equality is typed in
the honest required carrier itself. -/
structure RequiredCarrierNormalizedOrbitScaledWildLift827 where
  wildScale : (ZMod 59)ˣ
  carrier : QRelaxedReflectedDual827
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    canonicalTeichmullerCharacter59 irregularCharacter59
  lambda_eq :
    lambdaReflectedRequiredLocalization827 (K := K) carrier =
      (wildScale : ZMod 59) • w1ReflectedRequiredReceipt827 (K := K)
  selected_eq :
    reflectedPointedLocalization827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) carrier = 1

/-- Forgetting the carrier proof recovers the ambient scaled-lift object. -/
noncomputable def RequiredCarrierNormalizedOrbitScaledWildLift827.toAmbient
    (lift : RequiredCarrierNormalizedOrbitScaledWildLift827 (K := K)) :
    NormalizedOrbitScaledWildLift827 (K := K) where
  wildScale := lift.wildScale
  carrier := lift.carrier
  lambda_eq := by
    have h := congrArg Subtype.val lift.lambda_eq
    simpa [lambdaReflectedLocalization827_apply] using h
  selected_eq := lift.selected_eq

/-- The two-charge boundary of a scaled W1 receipt and normalized tame
coordinate, now entirely inside the honest required carrier. -/
theorem lambdaRequiredPointedPoitouTateBoundary827_scaledReceipt_one
    (scale : ZMod 59) :
    lambdaRequiredPointedPoitouTateBoundary827 (K := K)
        (scale • w1ReflectedRequiredReceipt827 (K := K), 1) =
      scale • w1ReceiptPrimalBoundaryFunctional827 (K := K) +
        irregularPrimalFrobeniusFunctional827 (K := K) := by
  rw [lambdaRequiredPointedPoitouTateBoundary827_eq_ambient]
  simpa using lambdaPointedPoitouTateBoundary827_scaledReceipt_one
    (K := K) scale

/-- A cancelling scaled W1 state and reverse PT exactness produce an
existential normalized lift on the honest carrier. -/
theorem nonempty_requiredCarrierScaledWildLift827_of_boundary_cancels
    (kernel_lifts :
      LinearMap.ker
          (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaRequiredPointedLocalization827 (K := K)))
    (scale : (ZMod 59)ˣ)
    (cancels :
      lambdaRequiredPointedPoitouTateBoundary827 (K := K)
        ((scale : ZMod 59) • w1ReflectedRequiredReceipt827 (K := K), 1) = 0) :
    Nonempty (RequiredCarrierNormalizedOrbitScaledWildLift827 (K := K)) := by
  obtain ⟨y, hlambda, hselected⟩ :=
    exists_reflected_lift_of_required_pt_kernel_lifts
      (K := K) kernel_lifts
      ((scale : ZMod 59) • w1ReflectedRequiredReceipt827 (K := K)) 1 cancels
  exact ⟨⟨scale, y, hlambda, hselected⟩⟩

/-- **Required-carrier scaled PT consumer.**  If W1's receipt functional is
a unit multiple of the local Frobenius functional, the inverse unit is the
single wild scale that cancels the normalized tame charge. -/
theorem nonempty_requiredCarrierScaledWildLift827_of_pt_and_unitComparison
    (kernel_lifts :
      LinearMap.ker
          (lambdaRequiredPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaRequiredPointedLocalization827 (K := K)))
    (comparisonUnit : (ZMod 59)ˣ)
    (comparison :
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        (comparisonUnit : ZMod 59) •
          irregularPrimalFrobeniusFunctional827 (K := K)) :
    Nonempty (RequiredCarrierNormalizedOrbitScaledWildLift827 (K := K)) := by
  let scale := cancelingWildScale827 comparisonUnit
  apply nonempty_requiredCarrierScaledWildLift827_of_boundary_cancels
    (K := K) kernel_lifts scale
  rw [lambdaRequiredPointedPoitouTateBoundary827_scaledReceipt_one,
    comparison, smul_smul, cancelingWildScale827_mul]
  simp

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.RequiredCarrierW1PointedPoitouTate827.lambdaRequiredPointedLocalization827_range_le_boundary_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaRequiredPointedLocalization827_range_le_boundary_ker

/--
info: 'Fermat.FiftyNine.Conservation.RequiredCarrierW1PointedPoitouTate827.lambdaRequiredPointedLocalization827_range_eq_ker_iff_kernel_lifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaRequiredPointedLocalization827_range_eq_ker_iff_kernel_lifts

/--
info: 'Fermat.FiftyNine.Conservation.RequiredCarrierW1PointedPoitouTate827.nonempty_requiredCarrierScaledWildLift827_of_pt_and_unitComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_requiredCarrierScaledWildLift827_of_pt_and_unitComparison

end Fermat.FiftyNine.Conservation.RequiredCarrierW1PointedPoitouTate827
