/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Constructing the 827 class readout from global-unit silence

For a fixed genuine 827-relaxed class, silence of the concrete strict tame
orbit functional on every actual global-unit class constructs a unique
scalar readout of the genuine 59-torsion ideal-class gauge.  The readout is
an output, not an input.

The same construction packages the honest remaining W7 boundary.  If the
constructed readout is injective, its value at the Fermat-factor difference
detects Vandiver's relation (7a).  Injectivity is deliberately retained as
an implication hypothesis: unit silence and quotient factorization alone do
not prove it.
-/
import Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
import Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalFullOrbitLocalPairing827
open CyclotomicSelmerClassNaturality59
open FermatFactorClassGaugeSeating59
open FermatFactorSelmerGauge59
open SevenAArtinPartialClosure59
open SplitPrimeFourier827
open StateFactorPair
open StrictTameOrbitClassFactorization827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Every quotient-level global-unit class has an actual ring-unit
representative.  This is the adapter from arithmetic silence proved on ring
units to the `UnitModP` kernel statement required by the class quotient. -/
theorem ringUnitClass59_surjective :
    Function.Surjective (ringUnitClass59 K) := by
  intro unitClass
  refine ⟨(Additive.toMul unitClass).out, ?_⟩
  apply Additive.ext
  exact QuotientGroup.out_eq' (Additive.toMul unitClass)

/-- Global-unit silence constructs, rather than assumes, the unique actual
class readout through which the concrete 827 tame-orbit functional factors. -/
theorem existsUnique_classReadout_of_unit_silence
    (y : RelaxedCarrier827 K)
    (unit_silence :
      ∀ u : UnitModP (NumberField.RingOfIntegers K) 59,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0) :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y := by
  exact
    (unit_silence_strictTameOrbitFunctional827_iff_existsUnique_classReadout
      K y).mp unit_silence

/-- The representative-level form used by the explicit arbitrary-unit tame
calculation.  Surjectivity of the quotient map upgrades silence for every
actual ring unit to silence for every `UnitModP` class before constructing
the unique class readout. -/
theorem existsUnique_classReadout_of_ringUnit_silence
    (y : RelaxedCarrier827 K)
    (ringUnit_silence :
      ∀ u : (NumberField.RingOfIntegers K)ˣ,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
            (ringUnitClass59 K u)) = 0) :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y := by
  apply existsUnique_classReadout_of_unit_silence K y
  intro unitClass
  obtain ⟨u, rfl⟩ := ringUnitClass59_surjective K unitClass
  exact ringUnit_silence u

/-- The unique readout produced by unit silence gives the pointwise W7
kernel comparison as soon as that same readout is injective.  This statement
does not take a readout as data and leaves the genuine injectivity seam
visible. -/
theorem existsUnique_classReadout_with_kernel_detection_of_unit_silence
    (y : RelaxedCarrier827 K)
    (unit_silence :
      ∀ u : UnitModP (NumberField.RingOfIntegers K) 59,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0) :
    ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
          strictTameOrbitFunctional827 K y ∧
        (Function.Injective readout →
          ∀ x : StrictCarrier59 K,
            strictTameOrbitFunctional827 K y x = 0 ↔
              fermatFactorClassGaugeMap59 (K := K) x = 0) := by
  obtain ⟨readout, factorization, unique⟩ :=
    existsUnique_classReadout_of_unit_silence K y unit_silence
  refine ⟨readout, ⟨factorization, ?_⟩, ?_⟩
  · intro readout_injective x
    exact strictTameOrbitFunctional827_eq_zero_iff_classGauge_eq_zero
      K y readout factorization readout_injective x
  · intro other hother
    exact unique other hother.1

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- At the actual Fermat-factor input, unit silence constructs the unique
class readout, and injectivity of that produced readout is exactly the still
visible hypothesis needed to derive Vandiver's relation-(7a) equivalence. -/
theorem existsUnique_classReadout_with_vandiverSevenA_of_unit_silence
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
        (Function.Injective readout →
          (strictTameOrbitFunctional827 K y
              (fermatFactorSelmerDifference59 pair) = 0 ↔
            pair.ledger.VandiverSevenA 0 1)) := by
  obtain ⟨readout, factorization, unique⟩ :=
    existsUnique_classReadout_of_unit_silence K y unit_silence
  refine ⟨readout, ⟨factorization, ?_⟩, ?_⟩
  · intro readout_injective
    exact strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA
      K y readout factorization readout_injective pair
  · intro other hother
    exact unique other hother.1

end Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827
