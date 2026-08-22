/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Unconditional normalized-orbit unit silence at 827

The committed normalized reflected fiber supplies an actual global
`827`-relaxed Selmer carrier whose supported valuations are exactly the W3
inverse-reflected profile.  The arbitrary-unit tame-orbit theorem therefore
kills the genuine strict tame functional on every global-unit class.  The
quotient adapter upgrades this to every `UnitModP` class, and the exact
strict Selmer class sequence constructs the unique class readout.

The carrier remains existential throughout.  This module makes no W1
lambda comparison, Poitou--Tate assertion, Artin comparison, readout
injectivity claim, relation `(7a)`, or Fermat claim.
-/
import Fermat.Exponents.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827
import Fermat.Exponents.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827
import Fermat.Exponents.FiftyNine.Conservation.UnitSilenceClassReadout827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
open Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Exact W3-profile realization makes the actual strict tame functional
silent on every quotient-level global-unit class. -/
theorem strictTameOrbitFunctional827_unitInclusion_eq_zero_of_normalizedProfile
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (unitClass : UnitModP (NumberField.RingOfIntegers K) 59) :
    strictTameOrbitFunctional827 K y
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          unitClass) = 0 := by
  obtain ⟨u, rfl⟩ := ringUnitClass59_surjective K unitClass
  exact
    strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero
      K u y
      (relaxedOrbitValuation827_isPureCharacter_of_eq_normalizedProfile
        K y hprofile)

/-- There exists an actual relaxed carrier retaining all of the following
receipts simultaneously:

* reflected eigenspace membership;
* the exact normalized W3 orbit profile;
* silence of the genuine strict tame functional on every ring unit;
* silence on every `UnitModP` class;
* the unique actual class readout factoring that functional.

No distinguished carrier is chosen or named. -/
theorem exists_normalizedFullOrbitProfile_unitSilence_classReadout827 :
    ∃ y : RelaxedCarrier827 K,
      y ∈ characterEigenspaceAt
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          (InvolutiveBase.reflectedCharacter
            canonicalTeichmullerCharacter59 irregularCharacter59) ∧
      (∀ tau : GaloisIndex59,
        relaxedOrbitValuation827 K tau y =
          normalizedFullOrbitEigenprofileCoordinates827
            canonicalTeichmullerCharacter59 irregularCharacter59 tau) ∧
      (∀ u : (NumberField.RingOfIntegers K)ˣ,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (ringUnitClass59 K u)) = 0) ∧
      (∀ unitClass : UnitModP (NumberField.RingOfIntegers K) 59,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            unitClass) = 0) ∧
      ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
        readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
          strictTameOrbitFunctional827 K y := by
  obtain ⟨y, heigen, hprofile⟩ :=
    exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile
      (K := K)
  have hpure : IsPureCharacter (powerCharacter59 14)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y) :=
    relaxedOrbitValuation827_isPureCharacter_of_eq_normalizedProfile
      K y hprofile
  have hringUnit : ∀ u : (NumberField.RingOfIntegers K)ˣ,
      strictTameOrbitFunctional827 K y
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) = 0 := by
    intro u
    exact
      strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero
        K u y hpure
  have hunitClass : ∀ unitClass :
      UnitModP (NumberField.RingOfIntegers K) 59,
      strictTameOrbitFunctional827 K y
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          unitClass) = 0 := by
    intro unitClass
    exact
      strictTameOrbitFunctional827_unitInclusion_eq_zero_of_normalizedProfile
        y hprofile unitClass
  have hreadout :
      ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
        readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
          strictTameOrbitFunctional827 K y :=
    existsUnique_classReadout_of_ringUnit_silence K y hringUnit
  exact ⟨y, heigen, hprofile, hringUnit, hunitClass, hreadout⟩

end Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827
