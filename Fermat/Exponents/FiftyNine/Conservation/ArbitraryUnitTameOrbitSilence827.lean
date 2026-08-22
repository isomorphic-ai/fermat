/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Arbitrary-global-unit silence in the genuine 827 tame orbit

The genuine carrier/context bridge writes every canonical tame row of a
global ring unit as

`(tau * rawUnitWave(tau⁻¹)) * relaxedValuation(tau)`.

Thus the global-root coordinate shifts a reflected valuation wave in mode
`14` into mode `15`, the inverse of mode `43`.  The already-proved
arbitrary-unit Fourier theorem kills mode `43` of the inverse-oriented raw
unit wave, so the complete genuine tame-orbit sum vanishes.

The primary theorem is conditional only on the actual relaxed carrier's
localization coordinates forming the required pure mode.  A second theorem
specializes this to literal equality with the committed normalized W3
profile.  No carrier, profile, lift, provider, or class certificate is
manufactured here.
-/
import Fermat.Exponents.FiftyNine.Conservation.ArbitraryUnitFourierSilence827
import Fermat.Exponents.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
import Fermat.Exponents.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
import Fermat.Exponents.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827
import Fermat.Exponents.FiftyNine.Conservation.UnitSilenceClassReadout827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827
open Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
open Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-- In the canonical irregular seat, the inverse reflected residue
character is exactly raw power-character mode `14`. -/
theorem inverseReflectedResidueCharacter827_canonical_irregular_eq_powerFourteen :
    inverseReflectedResidueCharacter827 canonicalTeichmullerCharacter59
      irregularCharacter59 = powerCharacter59 14 := by
  change (orientedPrimalMode827 canonicalTeichmullerCharacter59
    irregularCharacter59)⁻¹ = powerCharacter59 14
  rw [orientedPrimalMode827_canonical_irregular,
    powerCharacter59_fortyFour_inv]

/-- Literal equality with the normalized W3 profile supplies the required
pure reflected mode on the actual relaxed carrier. -/
theorem relaxedOrbitValuation827_isPureCharacter_of_eq_normalizedProfile
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    IsPureCharacter (powerCharacter59 14)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y) := by
  have hfunction :
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y) =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 := by
    funext tau
    exact hprofile tau
  rw [hfunction,
    ← inverseReflectedResidueCharacter827_canonical_irregular_eq_powerFourteen]
  exact normalizedFullOrbitEigenprofileCoordinates827_isPureCharacter
    canonicalTeichmullerCharacter59 irregularCharacter59

/-- The localization wave after inserting the global-root coordinate carried
by the canonical tame context. -/
def weightedRelaxedOrbitValuation827 (y : RelaxedCarrier827 K) :
    GaloisIndex59 → ZMod 59 :=
  fun tau ↦ (tau : ZMod 59) * relaxedOrbitValuation827 K tau y

/-- Multiplication by the global-root coordinate shifts a pure mode-`14`
relaxed localization wave into pure mode `15`. -/
theorem weightedRelaxedOrbitValuation827_isPureCharacter
    (y : RelaxedCarrier827 K)
    (hreflected : IsPureCharacter (powerCharacter59 14)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y)) :
    IsPureCharacter (powerCharacter59 15)
      (weightedRelaxedOrbitValuation827 K y) := by
  rcases hreflected with ⟨component, hcomponent⟩
  refine ⟨component, ?_⟩
  funext tau
  change (tau : ZMod 59) * relaxedOrbitValuation827 K tau y =
    (component • characterFunction (powerCharacter59 15)) tau
  rw [congrFun hcomponent tau]
  simp only [Pi.smul_apply, smul_eq_mul, characterFunction,
    powerCharacter59_apply]
  rw [show (14 : ZMod 58).val = 14 by decide,
    show (15 : ZMod 58).val = 15 by decide]
  simp only [Units.val_pow_eq_pow_val]
  ring

/-- Every actual global ring unit has zero total genuine tame-orbit reading
against an actual relaxed carrier whose valuation coordinates occupy the
canonical reflected pure mode. -/
theorem sum_rawTameOrbitReading827_unitInclusion_eq_zero_of_pureMode
    (u : (NumberField.RingOfIntegers K)ˣ)
    (y : RelaxedCarrier827 K)
    (hreflected : IsPureCharacter (powerCharacter59 14)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y)) :
    (∑ tau : GaloisIndex59,
      rawTameOrbitReading827 K tau
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) y) = 0 := by
  let raw := inverseReindex (rawGlobalUnitOrbitWave827 u)
  let weighted := weightedRelaxedOrbitValuation827 K y
  have hsum :
      (∑ tau : GaloisIndex59,
        rawTameOrbitReading827 K tau
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (ringUnitClass59 K u)) y) =
        ∑ tau : GaloisIndex59, raw tau * weighted tau := by
    apply Finset.sum_congr rfl
    intro tau _
    rw [rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation]
    change ((tau : ZMod 59) * rawGlobalUnitOrbitWave827 u tau⁻¹) *
        relaxedOrbitValuation827 K tau y =
      rawGlobalUnitOrbitWave827 u tau⁻¹ *
        ((tau : ZMod 59) * relaxedOrbitValuation827 K tau y)
    ring
  have hweighted :
      IsPureCharacter (powerCharacter59 43)⁻¹ weighted := by
    rw [powerCharacter59_fortyThree_inv]
    exact weightedRelaxedOrbitValuation827_isPureCharacter K y hreflected
  have hprojection :=
    sum_mul_pureInverse_eq_sum_characterComponent_mul
      galoisIndex59_card (powerCharacter59 43) raw weighted hweighted
  rw [hsum, hprojection]
  have hzero :=
    inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero u
  change fourierCoefficient raw (powerCharacter59 43) = 0 at hzero
  simp [hzero]

/-- The same genuine orbit silence under the explicit normalized-W3-profile
readback premise. -/
theorem sum_rawTameOrbitReading827_unitInclusion_eq_zero_of_normalizedProfile
    (u : (NumberField.RingOfIntegers K)ˣ)
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    (∑ tau : GaloisIndex59,
      rawTameOrbitReading827 K tau
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) y) = 0 := by
  exact sum_rawTameOrbitReading827_unitInclusion_eq_zero_of_pureMode K u y
    (relaxedOrbitValuation827_isPureCharacter_of_eq_normalizedProfile
      K y hprofile)

/-- The complete actual strict tame-orbit functional therefore kills every
ring-unit class in the canonical reflected pure seat. -/
theorem strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero
    (u : (NumberField.RingOfIntegers K)ˣ)
    (y : RelaxedCarrier827 K)
    (hreflected : IsPureCharacter (powerCharacter59 14)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y)) :
    strictTameOrbitFunctional827 K y
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) = 0 := by
  rw [strictTameOrbitFunctional827_apply]
  exact sum_rawTameOrbitReading827_unitInclusion_eq_zero_of_pureMode
    K u y hreflected

/-- Consequently the existing exact strict Selmer sequence constructs the
unique class readout for every actual relaxed carrier in the canonical
reflected pure seat. -/
theorem existsUnique_classReadout_of_relaxedOrbitValuation_isPureCharacter
    (y : RelaxedCarrier827 K)
    (hreflected : IsPureCharacter (powerCharacter59 14)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y)) :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y := by
  apply existsUnique_classReadout_of_ringUnit_silence K y
  intro u
  exact strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero
    K u y hreflected

end Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827
