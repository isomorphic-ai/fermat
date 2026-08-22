/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Local Kummer--Frobenius factorization of the 827 readout

The strict residue wave is already a linear map, while its pointwise values
have now been identified with the exponents by which literal residue
Frobenius scales the corresponding universal Kummer roots.  This file names
that linear map in its Frobenius interpretation and promotes the pointwise
comparison to an equality of `ZMod 59`-linear maps.

The resulting theorem is deliberately local.  It does not construct a
ray-class Artin map, invoke global Artin reciprocity or Poitou--Tate, or prove
faithfulness of the descended class readout.
-/
import Fermat.Exponents.FiftyNine.Conservation.KummerFrobeniusRead827
import Fermat.Exponents.FiftyNine.Conservation.WildOrbitBoundaryComparison827

open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827
open Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.KummerFrobeniusRead827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.VostokovLocalization59
open Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

private theorem irregularOldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
  irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact Fermat.Conservation.SelmerEigenspace.p_nsmul_eq_zero x.1

noncomputable local instance instIrregularOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule (irregularOldPrimal59_nsmul_eq_zero K)

/-! ## The literal residue Frobenius endomorphism -/

/-- The actual `ZMod 827`-algebra Frobenius endomorphism of the universal
degree-59 residue Kummer algebra. -/
noncomputable def residueFrobeniusAlgHom827
    (u : (ZMod Credit.attestationPrime)ˣ) :
    ResidueKummerAlgebra827 u →ₐ[ZMod Credit.attestationPrime]
      ResidueKummerAlgebra827 u :=
  FiniteField.frobeniusAlgHom (ZMod Credit.attestationPrime)
    (ResidueKummerAlgebra827 u)

/-- The bundled residue Frobenius endomorphism has the previously proved
fourteenth-power scaling action on the universal Kummer root. -/
@[simp]
theorem residueFrobeniusAlgHom827_root
    (u : (ZMod Credit.attestationPrime)ˣ) :
    residueFrobeniusAlgHom827 u (residueKummerRoot827 u) =
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          ((u : ZMod Credit.attestationPrime) ^ 14) *
        residueKummerRoot827 u := by
  change residueKummerRoot827 u ^
      Fintype.card (ZMod Credit.attestationPrime) = _
  rw [ZMod.card]
  exact frobenius_residueKummerRoot827 u

/-! ## The Frobenius interpretation as a linear map -/

/-- The actual residue-Frobenius exponent wave, bundled linearly by using
the already proved equality with the strict residue-wave linear map. -/
noncomputable def strictOrbitFrobeniusExponentWaveLinearMap827 :
    StrictCarrier59 K →ₗ[ZMod 59] (GaloisIndex59 → ZMod 59) :=
  strictOrbitResidueWaveLinearMap827 K

@[simp]
theorem strictOrbitFrobeniusExponentWaveLinearMap827_apply
    (x : StrictCarrier59 K) :
    strictOrbitFrobeniusExponentWaveLinearMap827 K x =
      strictOrbitFrobeniusExponentWave827 K x := by
  rw [strictOrbitFrobeniusExponentWaveLinearMap827,
    strictOrbitResidueWaveLinearMap827_apply]
  exact (strictOrbitFrobeniusExponentWave827_eq_residueWave K x).symm

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The signed mode-44 scalar reading, now named by its literal local
Kummer--Frobenius semantics.  Its implementation reuses the existing linear
Fourier reading of the strict residue wave. -/
noncomputable def localKummerFrobeniusModeFortyFourLinearMap827 :
    StrictCarrier59 K →ₗ[ZMod 59] ZMod 59 :=
  strictOrbitNegativeModeFortyFourLinearMap827 K

/-- Pointwise semantic form: the local Frobenius-mode map is the negative
mode-44 Fourier coefficient of the actual residue-Frobenius exponent wave. -/
@[simp]
theorem localKummerFrobeniusModeFortyFourLinearMap827_apply
    (x : StrictCarrier59 K) :
    localKummerFrobeniusModeFortyFourLinearMap827 K x =
      -fourierCoefficient
        (strictOrbitFrobeniusExponentWave827 K x)
        (powerCharacter59 44) := by
  rw [localKummerFrobeniusModeFortyFourLinearMap827,
    strictOrbitNegativeModeFortyFourLinearMap827_apply]
  rw [strictOrbitFrobeniusExponentWave827_eq_residueWave]

/-! ## Equality of linear maps -/

/-- The canonical class readout after the genuine strict-Selmer class gauge
is exactly the local residue-Frobenius mode-44 reading.

This is the local Kummer--Frobenius factorization supplied by the present
infrastructure.  It is not the still-missing global ray-class Artin
factorization or a faithfulness theorem. -/
theorem SevenALocalKummerFrobeniusFactorization827 :
    (canonicalModeFortyFourClassReadout827 K).comp
        (fermatFactorClassGaugeMap59 (K := K)) =
      localKummerFrobeniusModeFortyFourLinearMap827 K := by
  ext x
  rw [LinearMap.comp_apply,
    localKummerFrobeniusModeFortyFourLinearMap827_apply]
  exact canonicalModeFortyFourClassReadout827_eq_frobeniusFourier K x

/-! ## Restriction to the genuine Poitou--Tate test space -/

/-- The linear inclusion of the actual irregular primal eigenspace into the
complete strict Selmer carrier. -/
noncomputable def irregularPrimalInclusion59 :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 →ₗ[ZMod 59] StrictCarrier59 K :=
  (toSeatedCarrier
    (rho := cyclotomicStrictSelmerRepresentation59 K)
    (chi := irregularCharacter59)).toAddMonoidHom.toZModLinearMap 59

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem irregularPrimalInclusion59_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    irregularPrimalInclusion59 K x = x.1 :=
  rfl

/-- Any reflected class with the normalized 58-coordinate profile induces,
on the actual irregular Poitou--Tate test space, exactly the restriction of
the local Kummer--Frobenius mode map.  This is equality of linear maps, not
an assertion that the reflected class was globally produced by PT. -/
theorem seatedOrbitBoundaryFunctional827_eq_localKummerFrobeniusMode_comp
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y =
      (localKummerFrobeniusModeFortyFourLinearMap827 K).comp
        (irregularPrimalInclusion59 K) := by
  ext x
  rw [LinearMap.comp_apply, irregularPrimalInclusion59_apply,
    seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827,
    strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y.1 hprofile x.1,
    localKummerFrobeniusModeFortyFourLinearMap827_apply,
    strictOrbitFrobeniusExponentWave827_eq_residueWave]

/-- Pointwise W5 comparison on every genuine irregular primal test: the
normalized 827 boundary is the canonical class readout of the genuine class
gauge. -/
theorem seatedOrbitBoundaryFunctional827_eq_canonicalClassReadout
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y x =
      canonicalModeFortyFourClassReadout827 K
        (fermatFactorClassGaugeMap59 (K := K) x.1) := by
  calc
    _ = localKummerFrobeniusModeFortyFourLinearMap827 K x.1 := by
      have h := LinearMap.congr_fun
        (seatedOrbitBoundaryFunctional827_eq_localKummerFrobeniusMode_comp
          K y hprofile) x
      simpa only [LinearMap.comp_apply, irregularPrimalInclusion59_apply]
        using h
    _ = _ := by
      have h := LinearMap.congr_fun
        (SevenALocalKummerFrobeniusFactorization827 K) x.1
      simpa only [LinearMap.comp_apply] using h.symm

/-- The same W5 comparison in literal residue-Frobenius coordinates. -/
theorem seatedOrbitBoundaryFunctional827_eq_frobeniusFourier
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y x =
      -fourierCoefficient
        (strictOrbitFrobeniusExponentWave827 K x.1)
        (powerCharacter59 44) := by
  calc
    _ = localKummerFrobeniusModeFortyFourLinearMap827 K x.1 := by
      have h := LinearMap.congr_fun
        (seatedOrbitBoundaryFunctional827_eq_localKummerFrobeniusMode_comp
          K y hprofile) x
      simpa only [LinearMap.comp_apply, irregularPrimalInclusion59_apply]
        using h
    _ = _ := localKummerFrobeniusModeFortyFourLinearMap827_apply K x.1

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.residueFrobeniusAlgHom827_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms residueFrobeniusAlgHom827_root

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.strictOrbitFrobeniusExponentWaveLinearMap827_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictOrbitFrobeniusExponentWaveLinearMap827_apply

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.localKummerFrobeniusModeFortyFourLinearMap827_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms localKummerFrobeniusModeFortyFourLinearMap827_apply

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.SevenALocalKummerFrobeniusFactorization827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SevenALocalKummerFrobeniusFactorization827

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.seatedOrbitBoundaryFunctional827_eq_localKummerFrobeniusMode_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms seatedOrbitBoundaryFunctional827_eq_localKummerFrobeniusMode_comp

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.seatedOrbitBoundaryFunctional827_eq_canonicalClassReadout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms seatedOrbitBoundaryFunctional827_eq_canonicalClassReadout

/--
info: 'Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827.seatedOrbitBoundaryFunctional827_eq_frobeniusFourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms seatedOrbitBoundaryFunctional827_eq_frobeniusFourier

end Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827
