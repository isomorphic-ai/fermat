/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Canonical class factorization of the mode-44 reading

The normalized full `827` orbit reads the negative mode-`44` Fourier
coefficient of the strict residue wave.  Character covariance makes that
coefficient a literal linear map on the genuine strict Selmer carrier.

This file proves directly that the signed map kills the complete
`UnitModP` range.  The proof opens an existing normalized-profile witness
only locally; no reflected point is selected, named, or retained in the
result.  Exactness of the genuine strict Selmer class sequence then produces
a unique class readout whose pullback is the signed mode-`44` map.

The remaining arithmetic seam is exposed exactly: injectivity of this unique
readout is equivalent to the mode-`44` reading reflecting the zero ideal
class.  No Artin reciprocity theorem, class-rank premise, Takagi theorem,
provider, certificate, or new axiom is used.
-/
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827
open Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-! ## The point-free signed Fourier map -/

/-- The canonical scalar map read by the normalized full orbit.  The minus
sign is forced by the inverse-reflected orbit orientation. -/
noncomputable def strictOrbitNegativeModeFortyFourLinearMap827 :
    StrictCarrier59 K →ₗ[ZMod 59] ZMod 59 :=
  -strictOrbitModeFortyFourLinearMap827 K

@[simp]
theorem strictOrbitNegativeModeFortyFourLinearMap827_apply
    (x : StrictCarrier59 K) :
    strictOrbitNegativeModeFortyFourLinearMap827 K x =
      -fourierCoefficient (strictOrbitResidueWave827 K x)
        (powerCharacter59 44) := by
  rfl

/-- The point-free signed mode-44 map kills every genuine quotient-level
global-unit class.  A normalized reflected carrier is used only as a local
proof witness and disappears from the statement. -/
theorem strictOrbitNegativeModeFortyFourLinearMap827_unitInclusion_eq_zero
    (unitClass : UnitModP (NumberField.RingOfIntegers K) 59) :
    strictOrbitNegativeModeFortyFourLinearMap827 K
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          unitClass) = 0 := by
  obtain ⟨y, _heigen, hprofile, _hringUnit, hunitClass,
      _readout⟩ :=
    exists_normalizedFullOrbitProfile_unitSilence_classReadout827
      (K := K)
  have hformula :=
    strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hprofile
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          unitClass)
  rw [hunitClass unitClass] at hformula
  exact hformula.symm

/-! ## Unique descent to the genuine class carrier -/

/-- The signed mode-44 map has one and only one class-level factorization.
No normalized reflected point and no chosen readout occur in the theorem. -/
theorem existsUnique_classReadout_factorization_negativeModeFortyFour827 :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K := by
  exact
    (existsUnique_classReadout_factorization_iff_unit_silence
      (K := K)
      (reading := strictOrbitNegativeModeFortyFourLinearMap827 K)).1
        (strictOrbitNegativeModeFortyFourLinearMap827_unitInclusion_eq_zero K)

/-- The actual canonical class readout.  This chooses the uniquely determined
factorization of the signed mode-44 map, not a point of any reflected
localization fiber. -/
noncomputable def canonicalModeFortyFourClassReadout827 :
    ClassTorsion59 K →ₗ[ZMod 59] ZMod 59 :=
  Classical.choose
    (existsUnique_classReadout_factorization_negativeModeFortyFour827 K)

/-- The canonical readout pulls back to the signed mode-44 map on every
strict Selmer input. -/
theorem canonicalModeFortyFourClassReadout827_factorization :
    (canonicalModeFortyFourClassReadout827 K).comp
        (fermatFactorClassGaugeMap59 (K := K)) =
      strictOrbitNegativeModeFortyFourLinearMap827 K :=
  (Classical.choose_spec
    (existsUnique_classReadout_factorization_negativeModeFortyFour827 K)).1

/-- Any class readout with the required pullback is definitionally the
canonical mode-44 readout. -/
theorem classReadout_eq_canonicalModeFortyFourClassReadout827
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K) :
    readout = canonicalModeFortyFourClassReadout827 K :=
  (Classical.choose_spec
    (existsUnique_classReadout_factorization_negativeModeFortyFour827 K)).2
      readout factorization

@[simp]
theorem canonicalModeFortyFourClassReadout827_classGaugeMap59
    (x : StrictCarrier59 K) :
    canonicalModeFortyFourClassReadout827 K
        (fermatFactorClassGaugeMap59 (K := K) x) =
      strictOrbitNegativeModeFortyFourLinearMap827 K x :=
  LinearMap.congr_fun
    (canonicalModeFortyFourClassReadout827_factorization K) x

/-- Any factorizing readout evaluates the class gauge by the literal signed
mode-44 map on every strict Selmer input. -/
theorem classReadout_classGaugeMap59_eq_negativeModeFortyFour
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K)
    (x : StrictCarrier59 K) :
    readout (fermatFactorClassGaugeMap59 (K := K) x) =
      strictOrbitNegativeModeFortyFourLinearMap827 K x :=
  LinearMap.congr_fun factorization x

/-- The kernel of the signed mode-44 map is exactly the pullback of the
class-readout kernel. -/
theorem negativeModeFortyFour_ker_eq_comap_classReadout_ker
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K) :
    LinearMap.ker (strictOrbitNegativeModeFortyFourLinearMap827 K) =
      (LinearMap.ker readout).comap
        (fermatFactorClassGaugeMap59 (K := K)) := by
  calc
    LinearMap.ker (strictOrbitNegativeModeFortyFourLinearMap827 K) =
        LinearMap.ker
          (readout.comp (fermatFactorClassGaugeMap59 (K := K))) :=
      congrArg LinearMap.ker factorization.symm
    _ = (LinearMap.ker readout).comap
          (fermatFactorClassGaugeMap59 (K := K)) :=
      LinearMap.ker_comp _ _

/-- Injectivity of the descended readout is exactly equality between the
mode-44 kernel and the genuine global-unit kernel of the class gauge. -/
theorem classReadout_injective_iff_negativeModeFortyFour_ker_eq_classGauge_ker
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K) :
    Function.Injective readout ↔
      LinearMap.ker (strictOrbitNegativeModeFortyFourLinearMap827 K) =
        LinearMap.ker (fermatFactorClassGaugeMap59 (K := K)) := by
  constructor
  · intro hinjective
    rw [negativeModeFortyFour_ker_eq_comap_classReadout_ker
      K readout factorization, LinearMap.ker_eq_bot.mpr hinjective,
      Submodule.comap_bot]
  · intro hker
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.comap_injective_of_surjective
      (fermatFactorClassGaugeMap59_surjective (K := K))
    rw [← negativeModeFortyFour_ker_eq_comap_classReadout_ker
        K readout factorization,
      hker, Submodule.comap_bot]

/-- Equivalently, injectivity says precisely that a zero signed mode-44
reading forces the genuine ideal-class gauge to vanish. -/
theorem classReadout_injective_iff_negativeModeFortyFour_reflects_classGauge_zero
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K) :
    Function.Injective readout ↔
      ∀ x : StrictCarrier59 K,
        strictOrbitNegativeModeFortyFourLinearMap827 K x = 0 →
          fermatFactorClassGaugeMap59 (K := K) x = 0 := by
  rw [classReadout_injective_iff_negativeModeFortyFour_ker_eq_classGauge_ker
    K readout factorization]
  constructor
  · intro hker x hx
    apply LinearMap.mem_ker.mp
    rw [← hker]
    exact LinearMap.mem_ker.mpr hx
  · intro hreflect
    apply le_antisymm
    · intro x hx
      exact LinearMap.mem_ker.mpr
        (hreflect x (LinearMap.mem_ker.mp hx))
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hvalue := LinearMap.congr_fun factorization x
      change readout (fermatFactorClassGaugeMap59 (K := K) x) =
        strictOrbitNegativeModeFortyFourLinearMap827 K x at hvalue
      rw [hx, map_zero] at hvalue
      exact hvalue.symm

/-- Removing the harmless sign gives the concrete Fourier spelling of the
same remaining injectivity seam. -/
theorem classReadout_injective_iff_modeFortyFour_reflects_classGauge_zero
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K) :
    Function.Injective readout ↔
      ∀ x : StrictCarrier59 K,
        fourierCoefficient (strictOrbitResidueWave827 K x)
            (powerCharacter59 44) = 0 →
          fermatFactorClassGaugeMap59 (K := K) x = 0 := by
  simpa only [strictOrbitNegativeModeFortyFourLinearMap827_apply,
    neg_eq_zero] using
    (classReadout_injective_iff_negativeModeFortyFour_reflects_classGauge_zero
      K readout factorization)

/-! ## The selected Fermat class -/

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The map-level factorization specializes to the selected relation-7A
class with no reflected carrier parameter. -/
theorem classReadout_selectedClassGauge59_eq_negativeModeFortyFour
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K)
    (pair : StateLinkedIdealPair hZeta S hz) :
    readout (selectedClassGauge59 pair) =
      strictOrbitNegativeModeFortyFourLinearMap827 K
        (fermatFactorSelmerDifference59 pair) := by
  rw [← fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59 K pair]
  exact classReadout_classGaugeMap59_eq_negativeModeFortyFour
    K readout factorization (fermatFactorSelmerDifference59 pair)

/-- If the unique descended readout is injective, zero mode 44 is exactly
Vandiver's relation `(7a)` for the selected Fermat class. -/
theorem fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_classReadout_injective
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictOrbitNegativeModeFortyFourLinearMap827 K)
    (hinjective : Function.Injective readout)
    (pair : StateLinkedIdealPair hZeta S hz) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (fermatFactorSelmerDifference59 pair))
        (powerCharacter59 44) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  constructor
  · intro hzero
    apply (selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).1
    apply hinjective
    rw [classReadout_selectedClassGauge59_eq_negativeModeFortyFour
      K readout factorization pair, map_zero,
      strictOrbitNegativeModeFortyFourLinearMap827_apply, hzero, neg_zero]
  · exact fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA K pair

end Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
