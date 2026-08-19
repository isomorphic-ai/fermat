/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The seated Dwork meter balances the relation-7A Artin read

For any already supplied normalized Dwork-meter lift, genuine global
reciprocity identifies its scaled wild Presence² functional with the
negative of the canonical relation-7A class readout.  The proof is a direct
composition of four committed interfaces:

* the lift's actual wild-boundary readback;
* the wild-plus-orbit reciprocity balance;
* propagation of the selected coordinate to the full 58-place profile;
* the exact relation-7A Kummer--Artin factorization of that profile.

This file does not construct a Poitou--Tate lift, prove a faithfulness or
nonvanishing statement, or conclude relation `(7a)`.  Both the lift and the
global reciprocity law remain explicit inputs.
-/
import Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59
import Fermat.FiftyNine.Conservation.SevenAKummerArtinFactorization59

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
open Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59
open Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827
open Fermat.FiftyNine.Conservation.LambdaMeterPointedPoitouTate827
open Fermat.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59
open Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem irregularOldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact p_nsmul_eq_zero x.1

noncomputable local instance instIrregularOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule irregularOldPrimal59_nsmul_eq_zero

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-! ## The exact scaled balance -/

/-- A concrete Dwork-meter lift and genuine global reciprocity identify the
scaled wild Presence² map with the negative canonical class-gauge readout.
No nonzero premise or conclusion is used. -/
theorem scaledDworkLambdaBoundary_eq_neg_classGaugeReadout
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    (lift.wildScale : ZMod 59) •
        dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) =
      -((canonicalModeFortyFourClassReadout827 K).comp
        (irregularPrimalClassGauge59 K)) := by
  rw [← lift.wildBoundary_eq_scaledMeter,
    seatedWildBoundaryFunctional59_eq_neg_orbit
      canonicalTeichmullerCharacter59 irregularCharacter59
      reciprocity lift.carrier,
    SevenAKummerArtinFactorization59 K lift.carrier lift.fullOrbit]

/-! ## Removing the retained unit scale -/

/-- Since the retained wild scale is a unit, the unscaled Dwork functional
is the negative inverse-unit multiple of the canonical class-gauge readout. -/
theorem dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) =
      -(((lift.wildScale⁻¹ : (ZMod 59)ˣ) : ZMod 59) •
        ((canonicalModeFortyFourClassReadout827 K).comp
          (irregularPrimalClassGauge59 K))) := by
  calc
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) =
        ((lift.wildScale⁻¹ : (ZMod 59)ˣ) : ZMod 59) •
          ((lift.wildScale : ZMod 59) •
            dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K)) := by
              rw [smul_smul, Units.inv_mul, one_smul]
    _ = ((lift.wildScale⁻¹ : (ZMod 59)ˣ) : ZMod 59) •
        (-((canonicalModeFortyFourClassReadout827 K).comp
          (irregularPrimalClassGauge59 K))) := by
            rw [scaledDworkLambdaBoundary_eq_neg_classGaugeReadout
              lift reciprocity]
    _ = -(((lift.wildScale⁻¹ : (ZMod 59)ˣ) : ZMod 59) •
        ((canonicalModeFortyFourClassReadout827 K).comp
          (irregularPrimalClassGauge59 K))) := by
            rw [smul_neg]

/-! ## Exact algebraic consequences -/

/-- Unit rescaling and the reciprocity sign preserve map nonvanishing. -/
theorem dworkLambdaBoundary_ne_zero_iff_classGaugeReadout_ne_zero
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) ≠ 0 ↔
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularPrimalClassGauge59 K) ≠ 0 := by
  rw [dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout lift reciprocity]
  constructor
  · intro scaled_nonzero class_zero
    apply scaled_nonzero
    rw [class_zero, smul_zero, neg_zero]
  · intro class_nonzero scaled_zero
    apply class_nonzero
    have smul_zero :
        ((lift.wildScale⁻¹ : (ZMod 59)ˣ) : ZMod 59) •
            ((canonicalModeFortyFourClassReadout827 K).comp
              (irregularPrimalClassGauge59 K)) = 0 :=
      neg_eq_zero.mp scaled_zero
    exact (smul_eq_zero.mp smul_zero).resolve_left (Units.ne_zero _)

/-- The Dwork local boundary and canonical class-gauge readout detect
exactly the same primal test subspace. -/
theorem dworkLambdaBoundary_ker_eq_classGaugeReadout_ker
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    (dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K)).ker =
      ((canonicalModeFortyFourClassReadout827 K).comp
        (irregularPrimalClassGauge59 K)).ker := by
  rw [dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout lift reciprocity]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.neg_apply, LinearMap.smul_apply,
    neg_eq_zero]
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_left (Units.ne_zero _)
  · intro h
    rw [h, smul_zero]

/-- Pointwise form of the same exact kernel identification. -/
theorem dworkLambdaBoundary_apply_eq_zero_iff_classGaugeReadout_apply_eq_zero
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) x = 0 ↔
      canonicalModeFortyFourClassReadout827 K
          (irregularPrimalClassGauge59 K x) = 0 := by
  change x ∈
      (dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K)).ker ↔
    x ∈ ((canonicalModeFortyFourClassReadout827 K).comp
      (irregularPrimalClassGauge59 K)).ker
  rw [dworkLambdaBoundary_ker_eq_classGaugeReadout_ker lift reciprocity]

/-! ## Kernel-trust and route-separation audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59.scaledDworkLambdaBoundary_eq_neg_classGaugeReadout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scaledDworkLambdaBoundary_eq_neg_classGaugeReadout

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59.dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59.dworkLambdaBoundary_ne_zero_iff_classGaugeReadout_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkLambdaBoundary_ne_zero_iff_classGaugeReadout_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59.dworkLambdaBoundary_ker_eq_classGaugeReadout_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkLambdaBoundary_ker_eq_classGaugeReadout_ker

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59.dworkLambdaBoundary_apply_eq_zero_iff_classGaugeReadout_apply_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkLambdaBoundary_apply_eq_zero_iff_classGaugeReadout_apply_eq_zero

/- The balance must use the concrete lift's actual wild-boundary readback. -/
#guard_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  DworkSeatedLambdaMeter59.DworkSeatedNormalizedOrbitScaledLambdaLift827.wildBoundary_eq_scaledMeter

/- The only sign comes from the genuine wild-plus-orbit reciprocity law. -/
#guard_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit

/- The supplied lift contributes its proved complete 58-place profile. -/
#guard_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  DworkSeatedLambdaMeter59.DworkSeatedNormalizedOrbitScaledLambdaLift827.fullOrbit

/- The orbit side is identified by the committed relation-7A Artin
factorization, not by a duplicate class readout. -/
#guard_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  Fermat.FiftyNine.Conservation.SevenAKummerArtinFactorization59

/- Removing the unit scale is an algebraic consequence of the exact
balance. -/
#guard_depends_on
  dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout,
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout

/- The kernel and nonzero consequences consume the inverse-unit equality. -/
#guard_depends_on
  dworkLambdaBoundary_ne_zero_iff_classGaugeReadout_ne_zero,
  dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout

#guard_depends_on
  dworkLambdaBoundary_ker_eq_classGaugeReadout_ker,
  dworkLambdaBoundary_eq_neg_inv_smul_classGaugeReadout

#guard_depends_on
  dworkLambdaBoundary_apply_eq_zero_iff_classGaugeReadout_apply_eq_zero,
  dworkLambdaBoundary_ker_eq_classGaugeReadout_ker

/- A supplied lift is consumed, never manufactured by the balance. -/
#guard_not_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  DworkSeatedLambdaMeter59.nonempty_dworkSeatedLambdaLift827_of_pt_and_unitComparison

/- This cone does not close relation `(7a)` through either available
endpoint. -/
#guard_not_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

#guard_not_depends_on
  scaledDworkLambdaBoundary_eq_neg_classGaugeReadout,
  UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA

end Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59
