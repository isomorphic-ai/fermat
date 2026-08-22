/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Pointwise-faithful 827 class readout at relation 7A

The Fermat-specific W7 step does not need an injective scalar readout on the
complete 59-torsion class group.  It only needs the factorizing readout to
reflect zero at the single class selected by the Fermat-factor difference.

This file proves that sharper implication directly from the map-level
factorization.  It then packages it with the unique readout constructed from
global-unit silence, both at quotient level and at actual ring-unit
representative level.  Pointwise faithfulness remains the sole visible
arithmetic input; no Artin readout or class-group dimension statement is
supplied.
-/
import Fermat.Exponents.FiftyNine.Conservation.UnitSilenceClassReadout827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open CanonicalFullOrbitLocalPairing827
open CyclotomicSelmerClassNaturality59
open FermatFactorClassGaugeSeating59
open FermatFactorSelmerGauge59
open SevenAArtinPartialClosure59
open SplitPrimeFourier827
open StateFactorPair
open StrictTameOrbitClassFactorization827
open UnitSilenceClassReadout827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- A factorizing class readout detects zero at the actual Fermat input as
soon as it reflects zero at that one selected class.  No behavior on any
other class-group element is needed. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero_of_pointwiseFaithful
    (y : RelaxedCarrier827 K)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (pair : StateLinkedIdealPair hZeta S hz)
    (pointwise_faithful :
      readout (selectedClassGauge59 pair) = 0 →
        selectedClassGauge59 pair = 0) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      selectedClassGauge59 pair = 0 := by
  have factorization_at_fermat :=
    LinearMap.congr_fun factorization (fermatFactorSelmerDifference59 pair)
  change readout
      (fermatFactorClassGaugeMap59 (K := K)
        (fermatFactorSelmerDifference59 pair)) =
    strictTameOrbitFunctional827 K y
      (fermatFactorSelmerDifference59 pair) at factorization_at_fermat
  rw [fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59 K pair]
    at factorization_at_fermat
  constructor
  · intro orbit_zero
    apply pointwise_faithful
    exact factorization_at_fermat.trans orbit_zero
  · intro class_zero
    calc
      strictTameOrbitFunctional827 K y
          (fermatFactorSelmerDifference59 pair) =
          readout (selectedClassGauge59 pair) :=
        factorization_at_fermat.symm
      _ = 0 := by rw [class_zero, map_zero]

/-- Fermat-specific W7 with the exact minimal faithfulness premise: the
produced class readout only has to reflect zero at `selectedClassGauge59`. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
    (y : RelaxedCarrier827 K)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (pair : StateLinkedIdealPair hZeta S hz)
    (pointwise_faithful :
      readout (selectedClassGauge59 pair) = 0 →
        selectedClassGauge59 pair = 0) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  rw [strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero_of_pointwiseFaithful
      K y readout factorization pair pointwise_faithful,
    selectedClassGauge59_eq_zero_iff_vandiverSevenA]

/-- Quotient-level global-unit silence constructs the unique readout and
packages W7 with only pointwise faithfulness of that readout left visible. -/
theorem existsUnique_classReadout_with_pointwiseW7_of_unit_silence
    (y : RelaxedCarrier827 K)
    (unit_silence :
      ∀ u : UnitModP (NumberField.RingOfIntegers K) 59,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0)
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
          strictTameOrbitFunctional827 K y ∧
        ((readout (selectedClassGauge59 pair) = 0 →
            selectedClassGauge59 pair = 0) →
          (strictTameOrbitFunctional827 K y
              (fermatFactorSelmerDifference59 pair) = 0 ↔
            pair.ledger.VandiverSevenA 0 1)) := by
  obtain ⟨readout, factorization, unique⟩ :=
    existsUnique_classReadout_of_unit_silence K y unit_silence
  refine ⟨readout, ⟨factorization, ?_⟩, ?_⟩
  · intro pointwise_faithful
    exact
      strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
        K y readout factorization pair pointwise_faithful
  · intro other hother
    exact unique other hother.1

/-- The same unique-readout package from silence checked on every actual
ring-unit representative.  Quotient surjectivity is handled by the existing
unit-silence adapter; pointwise faithfulness remains the only later W7
premise. -/
theorem existsUnique_classReadout_with_pointwiseW7_of_ringUnit_silence
    (y : RelaxedCarrier827 K)
    (ringUnit_silence :
      ∀ u : (NumberField.RingOfIntegers K)ˣ,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (ArbitraryUnitRawTameCarrierBridge827.ringUnitClass59 K u)) = 0)
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
          strictTameOrbitFunctional827 K y ∧
        ((readout (selectedClassGauge59 pair) = 0 →
            selectedClassGauge59 pair = 0) →
          (strictTameOrbitFunctional827 K y
              (fermatFactorSelmerDifference59 pair) = 0 ↔
            pair.ledger.VandiverSevenA 0 1)) := by
  obtain ⟨readout, factorization, unique⟩ :=
    existsUnique_classReadout_of_ringUnit_silence K y ringUnit_silence
  refine ⟨readout, ⟨factorization, ?_⟩, ?_⟩
  · intro pointwise_faithful
    exact
      strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
        K y readout factorization pair pointwise_faithful
  · intro other hother
    exact unique other hother.1

/-- Readout-free consumer form.  Unit silence constructs the unique
factorizing readout internally; an arithmetic proof only has to establish
pointwise faithfulness for that (necessarily unique) factorization. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_unit_silence
    (y : RelaxedCarrier827 K)
    (unit_silence :
      ∀ u : UnitModP (NumberField.RingOfIntegers K) 59,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0)
    (pair : StateLinkedIdealPair hZeta S hz)
    (pointwise_faithful :
      ∀ readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
        readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
            strictTameOrbitFunctional827 K y →
          readout (selectedClassGauge59 pair) = 0 →
            selectedClassGauge59 pair = 0) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  obtain ⟨readout, factorization, -⟩ :=
    existsUnique_classReadout_of_unit_silence K y unit_silence
  exact
    strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
      K y readout factorization pair
        (pointwise_faithful readout factorization)

/-- Readout-free representative-level consumer.  The quotient readout is
again constructed internally, leaving only pointwise faithfulness at the
selected class as arithmetic input. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence
    (y : RelaxedCarrier827 K)
    (ringUnit_silence :
      ∀ u : (NumberField.RingOfIntegers K)ˣ,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (ArbitraryUnitRawTameCarrierBridge827.ringUnitClass59 K u)) = 0)
    (pair : StateLinkedIdealPair hZeta S hz)
    (pointwise_faithful :
      ∀ readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
        readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
            strictTameOrbitFunctional827 K y →
          readout (selectedClassGauge59 pair) = 0 →
            selectedClassGauge59 pair = 0) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  obtain ⟨readout, factorization, -⟩ :=
    existsUnique_classReadout_of_ringUnit_silence K y ringUnit_silence
  exact
    strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
      K y readout factorization pair
        (pointwise_faithful readout factorization)

end Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827
