/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The seated Dwork lambda meter

The projected Dwork classes now supply honest inputs to the two differently
oriented continuous Kummer maps.  This file retains their actual local cup,
curries the power-44 right factor into a scalar Presence² functional, and
plugs that concrete meter into the existing meter-parametric pointed
Poitou--Tate engine.

Only structural readbacks and conditional reuse are proved.  In particular,
this file does not assert that either projected class is nonzero, that their
cup is nonzero, that the cyclotomic action extends to all continuous `H¹`,
that the reverse Poitou--Tate inclusion holds, or that the resulting meter is
already identified with the Artin/7A readout.
-/
import Fermat.Exponents.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
import Fermat.Exponents.FiftyNine.Conservation.LambdaMeterPointedPoitouTate827

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827
open Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827
open Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
open Fermat.FiftyNine.Conservation.LambdaMeterPointedPoitouTate827
open Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827
open Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
open Fermat.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59
open Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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

noncomputable local instance instLambdaLocalKummerClass59ModuleZMod :
    Module (ZMod 59) (LambdaLocalKummerClass59 K) :=
  AddCommGroup.zmodModule
    (n := 59) (G := LambdaLocalKummerClass59 K)
    (lambdaLocalKummerClass59_nsmul_eq_zero K)

/-! ## The two actual continuous Kummer factors -/

/-- The seated depth-15 Kummer class sent through the genuine oriented left
continuous Kummer map. -/
noncomputable def dworkSeatedLambdaPrimalFifteen59 :
    LambdaOrientedContinuousH1 K :=
  leftKummerMap 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (projectedDworkPrincipalKummerClassFifteen59 K :
      LambdaLocalKummerClass59 K)

/-- The seated depth-44 Kummer class sent through the genuine un-oriented
right continuous Kummer map.  This is the concrete local PT meter. -/
noncomputable def dworkSeatedLambdaMeterFortyFour59 :
    LambdaRootsContinuousH1 K :=
  rightKummerMap 59 (LambdaLocalField59 K)
    (projectedDworkPrincipalKummerClassFortyFour59 K :
      LambdaLocalKummerClass59 K)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem dworkSeatedLambdaPrimalFifteen59_apply :
    dworkSeatedLambdaPrimalFifteen59 (K := K) =
      leftKummerMap 59 (LambdaLocalField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (projectedDworkPrincipalKummerClassFifteen59 K :
          LambdaLocalKummerClass59 K) :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem dworkSeatedLambdaMeterFortyFour59_apply :
    dworkSeatedLambdaMeterFortyFour59 (K := K) =
      rightKummerMap 59 (LambdaLocalField59 K)
        (projectedDworkPrincipalKummerClassFortyFour59 K :
          LambdaLocalKummerClass59 K) :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The left factor's source retains its exact power-15 Kummer eigenlaw.
No action on its continuous `H¹` target is inferred. -/
theorem dworkSeatedLambdaPrimalFifteen59_source_eigen
    (sigma : GaloisIndex59) :
    lambdaLocalKummerClassRepresentation59 K sigma
        (projectedDworkPrincipalKummerClassFifteen59 K :
          LambdaLocalKummerClass59 K) =
      ((PrimalFourierNonvanishing827.powerCharacter59 15 sigma :
          (ZMod 59)ˣ) : ZMod 59) •
        (projectedDworkPrincipalKummerClassFifteen59 K :
          LambdaLocalKummerClass59 K) :=
  projectedDworkPrincipalKummerClassFifteen59_eigen K sigma

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The meter's source retains its exact power-44 Kummer eigenlaw.
No action on the complete continuous `H¹` carrier is manufactured. -/
theorem dworkSeatedLambdaMeterFortyFour59_source_eigen
    (sigma : GaloisIndex59) :
    lambdaLocalKummerClassRepresentation59 K sigma
        (projectedDworkPrincipalKummerClassFortyFour59 K :
          LambdaLocalKummerClass59 K) =
      ((PrimalFourierNonvanishing827.powerCharacter59 44 sigma :
          (ZMod 59)ˣ) : ZMod 59) •
        (projectedDworkPrincipalKummerClassFortyFour59 K :
          LambdaLocalKummerClass59 K) :=
  projectedDworkPrincipalKummerClassFortyFour59_eigen K sigma

/-! ## The retained H2 interaction and Presence² functional -/

/-- The actual continuous lambda-local cup of the two projected Dwork
Kummer factors. -/
noncomputable def dworkSeatedLambdaCupClass59 :
    LambdaRootsContinuousH2 K :=
  lambdaContinuousCup59 K
    (dworkSeatedLambdaPrimalFifteen59 (K := K))
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem dworkSeatedLambdaCupClass59_apply :
    dworkSeatedLambdaCupClass59 (K := K) =
      lambdaContinuousCup59 K
        (dworkSeatedLambdaPrimalFifteen59 (K := K))
        (dworkSeatedLambdaMeterFortyFour59 (K := K)) :=
  rfl

/-- Curry the actual cup against the seated depth-44 meter and then apply
the already constructed normalized `H²` readout.  This is the local scalar
Presence² functional; no nonzero value is claimed. -/
noncomputable def dworkSeatedLambdaPresenceFunctional59 :
    Module.Dual (ZMod 59) (LambdaOrientedContinuousH1 K) :=
  (normalizedInflationReadout59 K).comp
    ((lambdaContinuousCup59 K).flip
      (dworkSeatedLambdaMeterFortyFour59 (K := K)))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem dworkSeatedLambdaPresenceFunctional59_apply
    (x : LambdaOrientedContinuousH1 K) :
    dworkSeatedLambdaPresenceFunctional59 (K := K) x =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K x
          (dworkSeatedLambdaMeterFortyFour59 (K := K))) :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The retained Dwork cup reads exactly as the Presence² functional
evaluated on its retained left factor. -/
theorem normalizedReadout_dworkSeatedLambdaCupClass59 :
    normalizedInflationReadout59 K
        (dworkSeatedLambdaCupClass59 (K := K)) =
      dworkSeatedLambdaPresenceFunctional59 (K := K)
        (dworkSeatedLambdaPrimalFifteen59 (K := K)) :=
  rfl

/-- Restrict the local Presence² functional to the genuine irregular primal
Selmer test space through its actual lambda localization. -/
noncomputable def dworkSeatedLambdaPrimalBoundaryFunctional827 :
    Module.Dual (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  (dworkSeatedLambdaPresenceFunctional59 (K := K)).comp
    (irregularPrimalLambdaLocalization827 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem dworkSeatedLambdaPrimalBoundaryFunctional827_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) x =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (irregularPrimalLambdaLocalization827 (K := K) x)
          (dworkSeatedLambdaMeterFortyFour59 (K := K))) :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The explicit Presence² restriction is exactly the generic PT engine's
wild functional specialized to the depth-44 Dwork meter. -/
theorem dworkSeatedLambdaPrimalBoundaryFunctional827_eq_lambdaMeter :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) =
      lambdaMeterPrimalBoundaryFunctional827 (K := K)
        (dworkSeatedLambdaMeterFortyFour59 (K := K)) := by
  apply LinearMap.ext
  intro x
  rfl

/-! ## Honest transversality from an explicit localization fiber -/

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- If the retained Dwork cup has nonzero normalized reading and an actual
irregular primal test class lies over the depth-15 Dwork factor, then the
concrete seated boundary functional is nonzero.  The global localization
fiber is deliberately retained as an existential premise: this theorem
neither chooses a canonical lift nor claims that one exists. -/
theorem dworkSeatedLambdaPrimalBoundaryFunctional827_ne_zero_of_cup_and_exists_lift
    (cup_nonzero :
      normalizedInflationReadout59 K
          (dworkSeatedLambdaCupClass59 (K := K)) ≠ 0)
    (localization_fiber :
      ∃ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59,
        irregularPrimalLambdaLocalization827 (K := K) x =
          dworkSeatedLambdaPrimalFifteen59 (K := K)) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) ≠ 0 := by
  rintro functional_zero
  obtain ⟨x, hx⟩ := localization_fiber
  apply cup_nonzero
  calc
    normalizedInflationReadout59 K
        (dworkSeatedLambdaCupClass59 (K := K)) =
        dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) x := by
          rw [dworkSeatedLambdaPrimalBoundaryFunctional827_apply, hx]
          rfl
    _ = 0 := by rw [functional_zero]; rfl

/-! ## Specialization of the meter-parametric PT engine -/

/-- The smallest actual right-`H¹` carrier containing all genuine reflected
localizations and the seated Dwork meter. -/
abbrev DworkSeatedLambdaRequiredCarrier827 :=
  lambdaMeterRequiredCarrier827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The seated Dwork meter as an element of its generated required carrier. -/
noncomputable def dworkSeatedLambdaMeterRequiredElement827 :
    DworkSeatedLambdaRequiredCarrier827 (K := K) :=
  meterRequiredElement827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem dworkSeatedLambdaMeterRequiredElement827_coe :
    (dworkSeatedLambdaMeterRequiredElement827 (K := K) :
      LambdaRootsContinuousH1 K) =
        dworkSeatedLambdaMeterFortyFour59 (K := K) :=
  rfl

/-- The pointed localization specialized to the concrete seated meter. -/
noncomputable abbrev dworkSeatedLambdaPointedLocalization827 :=
  lambdaMeterPointedLocalization827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

/-- The two-charge PT boundary specialized to the concrete seated meter. -/
noncomputable abbrev dworkSeatedLambdaPoitouTateBoundary827 :=
  lambdaMeterPointedPoitouTateBoundary827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

/-- The generic normalized existential lift type at the concrete Dwork
meter. -/
abbrev DworkSeatedNormalizedOrbitScaledLambdaLift827 :=
  NormalizedOrbitScaledLambdaMeterLift827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

/-! ## Concrete readbacks from any conditional lift -/

/-- The selected-coordinate normalization of a concrete Dwork-meter lift
propagates to its entire genuine 58-place reflected eigenprofile. -/
theorem DworkSeatedNormalizedOrbitScaledLambdaLift827.fullOrbit
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (tau : GaloisIndex59) :
    relaxedOrbitValuation827 K tau lift.carrier.1 =
      normalizedFullOrbitEigenprofileCoordinates827
        canonicalTeichmullerCharacter59 irregularCharacter59 tau := by
  rw [relaxedOrbitValuation827_eq_profile_mul_selected,
    lift.selected_eq, mul_one]

/-- The actual wild boundary of a concrete Dwork-meter lift is its retained
unit scale times the concrete seated Presence² functional. -/
theorem DworkSeatedNormalizedOrbitScaledLambdaLift827.wildBoundary_eq_scaledMeter
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) :
    seatedWildBoundaryFunctional59 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift.carrier =
      (lift.wildScale : ZMod 59) •
        dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) := by
  have hlocal :
      lambdaReflectedLocalization827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift.carrier =
        (lift.wildScale : ZMod 59) •
          dworkSeatedLambdaMeterFortyFour59 (K := K) := by
    rw [← lambdaMeterRequiredLocalization827_apply_coe
      (K := K) (dworkSeatedLambdaMeterFortyFour59 (K := K)) lift.carrier]
    rw [lift.lambda_eq]
    rfl
  apply LinearMap.ext
  intro x
  rw [seatedWildBoundaryFunctional59_apply,
    normalizedLambdaGlobalPairing59_eq_localized_factor_cup,
    ← lambdaReflectedLocalization827_apply, hlocal, LinearMap.smul_apply,
    dworkSeatedLambdaPrimalBoundaryFunctional827_apply,
    irregularPrimalLambdaLocalization827_apply]
  rw [(lambdaContinuousCup59 K
      (lambdaPrimalFactorOfGlobalKummer59 (K := K)
        (toKummerClass x))).map_smul,
    (normalizedInflationReadout59 K).map_smul]

/-- The normalized orbit boundary of the same lift is the genuine local
Frobenius functional. -/
theorem DworkSeatedNormalizedOrbitScaledLambdaLift827.orbitBoundary_eq_frobenius
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift.carrier =
      irregularPrimalFrobeniusFunctional827 (K := K) := by
  apply LinearMap.ext
  intro x
  rw [seatedOrbitBoundaryFunctional827_eq_selected_mul_localFrobenius,
    lift.selected_eq, one_mul,
    irregularPrimalFrobeniusFunctional827_apply]

/-- Global reciprocity supplies the proved `range ≤ kernel` direction for
the concrete Dwork meter. -/
theorem dworkSeatedLambdaPointedLocalization827_range_le_boundary_ker
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    LinearMap.range
        (dworkSeatedLambdaPointedLocalization827 (K := K)) ≤
      LinearMap.ker
        (dworkSeatedLambdaPoitouTateBoundary827 (K := K)) :=
  lambdaMeterPointedLocalization827_range_le_boundary_ker
    (K := K) (dworkSeatedLambdaMeterFortyFour59 (K := K)) reciprocity

/-- Exact conditional reuse of the generic PT lift consumer.  Reverse PT
inclusion and cancellation remain explicit inputs. -/
theorem nonempty_dworkSeatedLambdaLift827_of_boundary_cancels
    (kernel_lifts :
      LinearMap.ker
          (dworkSeatedLambdaPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range
          (dworkSeatedLambdaPointedLocalization827 (K := K)))
    (scale : (ZMod 59)ˣ)
    (cancels :
      dworkSeatedLambdaPoitouTateBoundary827 (K := K)
        ((scale : ZMod 59) •
            dworkSeatedLambdaMeterRequiredElement827 (K := K), 1) = 0) :
    Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) :=
  nonempty_scaledLambdaMeterLift827_of_boundary_cancels
    (K := K) (dworkSeatedLambdaMeterFortyFour59 (K := K))
    kernel_lifts scale cancels

/-- Unit comparison plus reverse PT inclusion conditionally produces the
same concrete existential lift.  No comparison theorem is manufactured. -/
theorem nonempty_dworkSeatedLambdaLift827_of_pt_and_unitComparison
    (kernel_lifts :
      LinearMap.ker
          (dworkSeatedLambdaPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range
          (dworkSeatedLambdaPointedLocalization827 (K := K)))
    (comparisonUnit : (ZMod 59)ˣ)
    (comparison :
      dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) =
        (comparisonUnit : ZMod 59) •
          irregularPrimalFrobeniusFunctional827 (K := K)) :
    Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) := by
  apply nonempty_scaledLambdaMeterLift827_of_pt_and_unitComparison
    (K := K) (dworkSeatedLambdaMeterFortyFour59 (K := K))
    kernel_lifts comparisonUnit
  rw [← dworkSeatedLambdaPrimalBoundaryFunctional827_eq_lambdaMeter]
  exact comparison

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.normalizedReadout_dworkSeatedLambdaCupClass59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizedReadout_dworkSeatedLambdaCupClass59

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.dworkSeatedLambdaPrimalBoundaryFunctional827_eq_lambdaMeter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkSeatedLambdaPrimalBoundaryFunctional827_eq_lambdaMeter

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.dworkSeatedLambdaPrimalBoundaryFunctional827_ne_zero_of_cup_and_exists_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkSeatedLambdaPrimalBoundaryFunctional827_ne_zero_of_cup_and_exists_lift

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.DworkSeatedNormalizedOrbitScaledLambdaLift827.fullOrbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms DworkSeatedNormalizedOrbitScaledLambdaLift827.fullOrbit

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.DworkSeatedNormalizedOrbitScaledLambdaLift827.wildBoundary_eq_scaledMeter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms DworkSeatedNormalizedOrbitScaledLambdaLift827.wildBoundary_eq_scaledMeter

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.DworkSeatedNormalizedOrbitScaledLambdaLift827.orbitBoundary_eq_frobenius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms DworkSeatedNormalizedOrbitScaledLambdaLift827.orbitBoundary_eq_frobenius

/--
info: 'Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59.nonempty_dworkSeatedLambdaLift827_of_pt_and_unitComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_dworkSeatedLambdaLift827_of_pt_and_unitComparison

end Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59
