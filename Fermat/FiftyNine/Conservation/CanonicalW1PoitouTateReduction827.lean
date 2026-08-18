/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The actual primal-test reduction of the canonical W1 boundary

The point-free W2 boundary is defined on every functional annihilating the
lambda image of a full-`827`-orbit-invisible reflected adjustment.  This
file places the genuine irregular primal Selmer space inside that abstract
test space, using the already constructed lambda localization, local cup,
full-orbit tame pairing, and the explicit global-reciprocity API.

It then isolates the two exact assertions still needed to kill W2:

* every abstract annihilator test is represented by a genuine primal test;
* the retained W1 lambda receipt cancels the normalized full-orbit boundary
  on every genuine primal test.

No Poitou--Tate exactness, global reciprocity, Artin comparison, selected
lift, provider, or certificate is asserted here.  Reciprocity remains an
explicit theorem argument, and the two missing assertions remain explicit
hypotheses of the final reduction theorem.
-/
import Fermat.FiftyNine.Conservation.CanonicalW1LambdaBoundary827
import Fermat.FiftyNine.Conservation.FullOrbitGlobalReciprocityCriterion827
import Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalW1LambdaBoundary827
open CanonicalW1LambdaObstruction827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open FermatFactorArtinFourierBoundary827
open LambdaOrbitAffineKernelCriterion827
open LambdaOrbitLocalizationFiber827
open LocalCompletion59
open LocalKummerFrobeniusFactorization827
open NormalizedContinuousKummerPairing59
open NormalizedFullOrbitGlobalRealization827
open PointedTateIncidence
open SplitPrimeFourier827
open StrictTameOrbitClassFactorization827
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

/-- Genuine localization of the actual irregular primal Selmer test space
into the oriented left lambda-local `H¹` seat. -/
noncomputable def irregularPrimalLambdaLocalization827 :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 →ₗ[ZMod 59]
      LambdaOrientedContinuousH1 K :=
  ((leftKummerMap 59 (LambdaLocalField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)).comp
    ((LocalKummerTransport.map 59 (lambdaLocalization59 K)).comp
      (toKummerClass
        (rho := cyclotomicStrictSelmerRepresentation59 K)
        (chi := irregularCharacter59)))).toZModLinearMap 59

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem irregularPrimalLambdaLocalization827_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    irregularPrimalLambdaLocalization827 (K := K) x =
      lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x) :=
  rfl

/-- Curry the genuine lambda-local cup against each actual irregular primal
test.  Its codomain is the complete dual of the reflected local `H¹` seat;
no perfectness or surjectivity is claimed. -/
noncomputable def irregularPrimalLambdaTestMap827 :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 →ₗ[ZMod 59]
      Module.Dual (ZMod 59) (LambdaRootsContinuousH1 K) :=
  ((LinearMap.llcomp (ZMod 59)
      (LambdaRootsContinuousH1 K)
      (LambdaRootsContinuousH2 K)
      (ZMod 59)
      (normalizedInflationReadout59 K)).comp
    (lambdaContinuousCup59 K)).comp
      (irregularPrimalLambdaLocalization827 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem irregularPrimalLambdaTestMap827_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (r : LambdaRootsContinuousH1 K) :
    irregularPrimalLambdaTestMap827 (K := K) x r =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x)) r) :=
  rfl

/-- The retained W1 reflected factor, evaluated against every genuine
irregular primal Selmer test.  This is the wild charge which must cancel the
normalized full-orbit charge in the Poitou--Tate boundary. -/
noncomputable def w1ReceiptPrimalBoundaryFunctional827 :
    Module.Dual (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  ((normalizedInflationReadout59 K).comp
    ((lambdaContinuousCup59 K).flip
      (twistedLambdaCupReceipt59 K).reflected)).comp
        (irregularPrimalLambdaLocalization827 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem w1ReceiptPrimalBoundaryFunctional827_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    w1ReceiptPrimalBoundaryFunctional827 (K := K) x =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x))
          (twistedLambdaCupReceipt59 K).reflected) :=
  rfl

/-- Reciprocity makes every genuine primal lambda test annihilate the lambda
image of every reflected adjustment invisible on the complete `827` orbit.
This is the concrete half of the Poitou--Tate boundary representation: it
constructs the map into the annihilator but deliberately does not claim
that the map is onto. -/
theorem irregularPrimalLambdaTestMap827_mem_dualAnnihilator
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    irregularPrimalLambdaTestMap827 (K := K) x ∈
      (LinearMap.range
        (lambdaOnFullOrbitKernel827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59)).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro r hr
  obtain ⟨z, rfl⟩ := hr
  have hOrbitZero :
      seatedOrbitBoundaryFunctional827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 z.1 x = 0 := by
    rw [seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827,
      strictTameOrbitFunctional827_apply]
    apply Finset.sum_eq_zero
    intro tau _
    rw [rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation]
    have hz :
        fullOrbitValuationLocalization827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 z.1 = 0 := by
      exact z.2
    have hzTau :=
      (fullOrbitValuationLocalization827_eq_zero_iff
        canonicalTeichmullerCharacter59 irregularCharacter59 z.1).mp hz tau
    rw [hzTau, mul_zero]
  have hWild := LinearMap.congr_fun
    (seatedWildBoundaryFunctional59_eq_neg_orbit (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 reciprocity z.1) x
  rw [lambdaOnFullOrbitKernel827_apply,
    irregularPrimalLambdaTestMap827_apply]
  change normalizedInflationReadout59 K
      (lambdaContinuousCup59 K
        (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x))
        (lambdaReflectedFactorOfGlobalKummer59 (K := K)
          (toKummerClassAt z.1))) = 0
  rw [← normalizedLambdaGlobalPairing59_eq_localized_factor_cup,
    ← seatedWildBoundaryFunctional59_apply]
  rw [hWild, LinearMap.neg_apply, hOrbitZero, neg_zero]

/-- The honest map from the actual irregular primal/PT test space into the
abstract W2 annihilator-test space. -/
noncomputable def irregularPrimalToW1BoundaryTests827
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 →ₗ[ZMod 59]
      CanonicalW1LambdaBoundaryTestSpace827 (K := K) where
  toFun x := ⟨irregularPrimalLambdaTestMap827 (K := K) x,
    irregularPrimalLambdaTestMap827_mem_dualAnnihilator reciprocity x⟩
  map_add' x y := by ext r; simp
  map_smul' a x := by ext r; simp

@[simp]
theorem irregularPrimalToW1BoundaryTests827_apply_coe
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity x).1 =
      irregularPrimalLambdaTestMap827 (K := K) x :=
  rfl

/-- On the genuine primal test space, the canonical W2 boundary is exactly
the sum of the retained W1 wild charge and the normalized `827` orbit
charge.  This is the actual two-charge Poitou--Tate equation; it follows
from the existing reciprocity API and introduces no new arithmetic input. -/
theorem canonicalW1LambdaBoundary827_comp_primalTests_eq_receipt_add_orbit
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    (canonicalW1LambdaBoundary827 (K := K)).comp
        (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity) =
      w1ReceiptPrimalBoundaryFunctional827 (K := K) +
        seatedOrbitBoundaryFunctional827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y.1 := by
  ext x
  rw [LinearMap.comp_apply,
    canonicalW1LambdaBoundary827_apply y,
    irregularPrimalToW1BoundaryTests827_apply_coe]
  change
    irregularPrimalLambdaTestMap827 (K := K) x
        ((twistedLambdaCupReceipt59 K).reflected -
          lambdaReflectedLocalization827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y.1) = _
  rw [map_sub, irregularPrimalLambdaTestMap827_apply,
    irregularPrimalLambdaTestMap827_apply]
  change
    w1ReceiptPrimalBoundaryFunctional827 (K := K) x -
        normalizedLambdaGlobalPairing59 K
          (toKummerClass x) (toKummerClassAt y.1) =
      w1ReceiptPrimalBoundaryFunctional827 (K := K) x +
        seatedOrbitBoundaryFunctional827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y.1 x
  rw [← seatedWildBoundaryFunctional59_apply]
  have hWild := LinearMap.congr_fun
    (seatedWildBoundaryFunctional59_eq_neg_orbit (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 reciprocity y.1) x
  rw [hWild, LinearMap.neg_apply]
  ring

/-- The same boundary identity after replacing the normalized orbit charge
by its already proved local Kummer--Frobenius map.  This is the exact point
where the new `7A-ARTIN-READ` strategy meets the compiler-visible W2
obstruction. -/
theorem canonicalW1LambdaBoundary827_comp_primalTests_eq_receipt_add_frobenius
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    (canonicalW1LambdaBoundary827 (K := K)).comp
        (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity) =
      w1ReceiptPrimalBoundaryFunctional827 (K := K) +
        (localKummerFrobeniusModeFortyFourLinearMap827 K).comp
          (irregularPrimalInclusion59 K) := by
  have hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau := by
    intro tau
    exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
      canonicalTeichmullerCharacter59 irregularCharacter59 y tau
  rw [canonicalW1LambdaBoundary827_comp_primalTests_eq_receipt_add_orbit
    reciprocity y,
    seatedOrbitBoundaryFunctional827_eq_localKummerFrobeniusMode_comp
      K y.1 hprofile]

/-- Exact compiler-visible W2 reduction.  Global reciprocity places actual
primal tests in the lawful boundary space.  Surjectivity is the missing
Poitou--Tate/local-duality representation theorem; pointwise vanishing is
the missing W1-versus-normalized-`827` cancellation theorem.  Supplying
exactly those two facts kills the canonical boundary. -/
theorem canonicalW1LambdaBoundary827_eq_zero_of_primal_representation
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (represented : Function.Surjective
      (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity))
    (cancels : ∀ x : OldPrimal59
        (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59,
      canonicalW1LambdaBoundary827 (K := K)
        (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity x) = 0) :
    canonicalW1LambdaBoundary827 (K := K) = 0 := by
  apply LinearMap.ext
  intro phi
  obtain ⟨x, rfl⟩ := represented phi
  exact cancels x

/-- Sharp W2 closure interface exposed by the present APIs.  Besides the
explicit reciprocity law, exactly two mathematical facts remain:

1. Poitou--Tate/local duality says every lawful abstract annihilator test is
   represented by an actual irregular primal test;
2. Kummer--Artin compatibility says the retained W1 receipt functional is
   the negative of the normalized local Frobenius boundary.

Once those are supplied, the canonical W2 boundary vanishes. -/
theorem canonicalW1LambdaBoundary827_eq_zero_of_pt_and_kummerArtin
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (pt_represents : Function.Surjective
      (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity))
    (kummerArtin_cancels :
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        -((localKummerFrobeniusModeFortyFourLinearMap827 K).comp
          (irregularPrimalInclusion59 K))) :
    canonicalW1LambdaBoundary827 (K := K) = 0 := by
  apply LinearMap.ext
  intro phi
  obtain ⟨x, rfl⟩ := pt_represents phi
  have h := LinearMap.congr_fun
    (canonicalW1LambdaBoundary827_comp_primalTests_eq_receipt_add_frobenius
      (K := K) reciprocity y) x
  rw [kummerArtin_cancels, neg_add_cancel] at h
  simpa using h

/-- Direct obstruction consumer.  The same two genuine hypotheses close the
named point-free W2 cokernel class, via dual-annihilator separation. -/
theorem canonicalW1LambdaObstruction827_eq_zero_of_pt_and_kummerArtin
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (pt_represents : Function.Surjective
      (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity))
    (kummerArtin_cancels :
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        -((localKummerFrobeniusModeFortyFourLinearMap827 K).comp
          (irregularPrimalInclusion59 K))) :
    canonicalW1LambdaObstruction827 (K := K) = 0 := by
  apply
    (canonicalW1LambdaObstruction827_eq_zero_iff_boundary_eq_zero
      (K := K)).2
  exact canonicalW1LambdaBoundary827_eq_zero_of_pt_and_kummerArtin
    reciprocity y pt_represents kummerArtin_cancels

/-- Direct W2 fiber consumer.  Once actual primal tests represent the full
annihilator and the W1 receipt cancels the normalized Frobenius boundary,
an end-to-end W1+W3 compatible reflected class exists.  The conclusion is
`Nonempty`; no selected lift is exposed. -/
theorem w1w3CompatibleFiber827_nonempty_of_pt_and_kummerArtin
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (pt_represents : Function.Surjective
      (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity))
    (kummerArtin_cancels :
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        -((localKummerFrobeniusModeFortyFourLinearMap827 K).comp
          (irregularPrimalInclusion59 K))) :
    Nonempty (W1W3CompatibleFiber827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59) := by
  apply
    (w1w3CompatibleFiber827_nonempty_iff_canonicalBoundary_eq_zero
      (K := K)).2
  exact canonicalW1LambdaBoundary827_eq_zero_of_pt_and_kummerArtin
    reciprocity y pt_represents kummerArtin_cancels

/-! ## Dependency audit

The three endpoints below depend only on the repository's ordinary quotient
and choice infrastructure.  In particular they install no new axiom for
reciprocity, Poitou--Tate representation, Kummer--Artin cancellation, or a
selected reflected lift: all three mathematical seams remain visible as
arguments in the theorem types above. -/

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827.canonicalW1LambdaBoundary827_eq_zero_of_pt_and_kummerArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canonicalW1LambdaBoundary827_eq_zero_of_pt_and_kummerArtin

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827.canonicalW1LambdaObstruction827_eq_zero_of_pt_and_kummerArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canonicalW1LambdaObstruction827_eq_zero_of_pt_and_kummerArtin

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827.w1w3CompatibleFiber827_nonempty_of_pt_and_kummerArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms w1w3CompatibleFiber827_nonempty_of_pt_and_kummerArtin

end Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827
